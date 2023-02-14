load "new_models.m";

//////////////
// Philippe // // get in touch with me if (when) you find problems with the code!
//////////////

// This code searches for rational points on AL quotients of X_0(N) 
// and pulls them back to quadratic points on X_0(N).

// See EXAMPLES at end of file.

// When we discuss quadratic points here we mean true quadratic points (i.e. not sums of rational points)
// We ouptut a quadratic point on a curve X / Q as a tuple.
// If the quadratic point is defined over K, then the tuple is:
// < [P in X(K), conjugate of P in X(K)]  , K >
// The field K will always be represented as K = K[x] / (x^2 - d) for an integer d.

// We start with an auxiliary function that checks if two quadratic points are equal:

equal_quad_points := function(tup1, tup2);
    K1 := tup1[2];
    K2 := tup2[2];
    if Discriminant(Integers(K1)) ne Discriminant(Integers(K2)) then // check if number fields are the same
        return false;
    end if;
    pt1 := Eltseq(tup1[1][1]);
    pt2 := Eltseq(tup2[1][1]);
    for i in [1..#pt1] do
        if MinimalPolynomial(pt1[i]) ne MinimalPolynomial(pt2[i]) then 
            return false;
        end if;
    end for;
    return true;
end function;
    

// We now look at the main function, "pullback_points"

// Input:
// 1. A curve X = X_0(N) (obtained from the function eqs_quos in the new_models.m file)
// 2. pairs (a sequence of AL quotients and the quotient maps, obtained from eqs_quos)
// 3. The level (N)
// 4. A height bound for the rational point search on the quotient (I use 10000 for most examples)

// Output: A list of quadratic points

// Each quadratic point arises as the pullback of a rational point on an AL quotient
// If the AL quotient curve is genus 0, then we do not search for points.

pullback_points := function(X, pairs, N, bound);
    point_list := [* *];
    for i in [i : i in [1..#pairs]] do
        pair := pairs[i];
        Y := pair[1];
        rho := pair[2];
        if Genus(Y) eq 0 then 
            continue;
        elif IsHyperelliptic(Y) or Genus(Y) eq 1 then 
            rat_pts := Points(Y : Bound := bound);
        else rat_pts := PointSearch(Y, bound);
        end if;
        BS := BaseScheme(rho); 
        for R in rat_pts do 
            S := Pullback(rho,R); // The pullback scheme (including base scheme)
            D := Difference(S, BS); // The pullback scheme (not including base scheme)
            pb, K1 := PointsOverSplittingField(D);
            K := NumberField(AbsolutePolynomial(K1));
            if Degree(K) eq 2 then // we look for a nicer defining polynomial for K
                d := Discriminant(Integers(K));
                if (d mod 4) eq 0 then 
                    d := Integers() ! (d/4);
                end if;
                T<z> := PolynomialRing(Rationals());
                K := NumberField(z^2 - d);  // K has now been redefined in a nicer form.
            end if;
            pbK := Points(Intersection(X,D),K);
            pbX := < [X(K) ! p : p in pbK | IsRationalPoint(p) eq false], K>; // do not include rational points. 
            if #pbX[1] ne 0 then 
                point_list := point_list cat [* pbX *];
            end if;
        end for;
    end for;
    // We now remove any repeated points
    remov_indices := [];
    for i in [1..#point_list] do
        for j in [1..#point_list] do
            if j gt i then 
                if equal_quad_points(point_list[i],point_list[j]) then 
                    remov_indices := remov_indices cat [j];
                end if;
            end if;
        end for;
    end for; 
    no_rep_point_list := [*point_list[i] : i in [1..#point_list] | i notin remov_indices*];     
    return no_rep_point_list;
end function;

/*

////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////

// EXAMPLES //

// Example 1

// We consider the curve X_0(34). 
// This curve has 3 AL quotients.
// Each is an elliptic curve of rank 0.
// From the table in Ozman--Siksek, there are 6 (pairs of) pullback quadratic points.
// (These are in fact all the quadratic points).

N := 34;
al_seq := [ [m] : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1]; // AL indices are 2, 17, and 34
X, _, pairs := eqs_quos(N, al_seq);
bound := 10000;

time pullbacks := pullback_points(X,pairs,N, bound); // 0.3 seconds
assert #pullbacks eq 6;
// Note that we have removed any repetitions from this list of points.
// If we had not done this we would have two pairs of repeated quadratic points

// We now check that the field of definition and j invariant of these points match the data in the Ozman--Siksek table.

j := jmap(X,N);
for quad_pt in pullbacks do
    quad_pt[2]; // The field of definition
    j(quad_pt[1][1]);
end for;

// Output: (this matches the known data)

// Number Field with defining polynomial z^2 + 15 over the Rational Field
// (1/34359738368*(-53184785340479*$.1 - 7319387769191) : 1)
// Number Field with defining polynomial z^2 + 15 over the Rational Field
// (1/8*(-2041*$.1 + 11779) : 1)
// Number Field with defining polynomial z^2 + 1 over the Rational Field
// (287496 : 1)
// Number Field with defining polynomial z^2 + 2 over the Rational Field
// (8000 : 1)
// Number Field with defining polynomial z^2 + 1 over the Rational Field
// (1728 : 1)
// Number Field with defining polynomial z^2 + 1 over the Rational Field
// (1728 : 1)


// Note that the coordinates of the points are different to those in the Ozman--Siksek table.
// This is because our model for the curve is different.

////////////////////////////////////////////
////////////////////////////////////////////

// Example 2
        
// The curve X_0(74) has both hyperelliptic and non-hyperelliptic quotients.

N := 74;
al_seq := [ [m] : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
X, _, pairs := eqs_quos(N, al_seq);
bound := 10000;

time pullbacks := pullback_points(X,pairs,N, bound); // 15 seconds 
assert #pullbacks eq 11;

// Let's see how to access the coordinates of a point:
P := pullbacks[1][1][1];
seqP := Eltseq(P);
// [0, -5/74*$.1, 1/37*$.1, -1/74*$.1, 0, 0, 0, 1]
// Here the $.1 can be read off from the field of definition
K := pullbacks[1][2];
// Number Field with defining polynomial z^2 - 37 over the Rational Field
// So $.1 is sqrt(37).
// We could also ask:
MinimalPolynomial(K.1); // z^2 - 37
// Alternatively, we can ask for the minimal polynomial of a coordinate:
c := seqP[2];
MinimalPolynomial(c); // z^2 - 25/148
MinimalPolynomial(c*(-74/5)); // z^2-37, as expected, since c = (-5/74)*$.1

////////////////////////////////////////////
////////////////////////////////////////////

// Example 3

// We consider an example of larger genus

N := 163;
al_seq := [[163]];
X,_,pairs := eqs_quos(N,al_seq);
bound := 1000;

time pullbacks := pullback_points(X,pairs,N, bound); //15 seconds

////////////////////////////////////////////
////////////////////////////////////////////

// Example 4

N := 60;
al_seq := [ [m] : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
X, _, pairs := eqs_quos(N, al_seq);
bound := 10000;

time pullbacks := pullback_points(X,pairs,N, bound); // 23 seconds

// In this case, all the pullbacks are rational points on X_0(60)
// This is not so suprising since X_0(60) has 12 rational points (the 12 cusps).
// In fact, by Najman--Vukorepa, there are no quadratic points at all.
assert pullbacks eq [* *]; 


////////////////////////////////////////////
////////////////////////////////////////////

// Example 5

N := 85;
al_seq := [ [m] : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
X, _, pairs := eqs_quos(N, al_seq);
bound := 10000;

time pullbacks := pullback_points(X,pairs,N, bound); // 14 seconds

////////////////////////////////////////////
////////////////////////////////////////////

*/
