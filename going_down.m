// This file contains all computations used in the going-down method

load  "models_and_maps.m";

// We will make use of the following function

/////////////////
/// coords_jK ///
/////////////////

// Function for computing points with a given j-invariant
// Please see the examples at the end of the file for further detailed examples of usage

// Input: X, j, jinv, K

// X is a model for X_0(N) (obtained from eqs_quos) (non-hyperelliptic genus > 2)
// j is the j map on this model to P^1 (obtained from jmap)
// jinv is the j-invariant of the point of interest. This must be a rational j-invariant.
// K is the quadratic field over which the point is defined

// Output: Points with j-invariant jinv defined over K on X

// The points are output as an ordered set.
// The list includes quadratic points AND their conjugate points

coords_jK := function(X,j,jinv,K);
    PP := Codomain(j);
    pt := PP ! [jinv];
    base_scheme := BaseScheme(j);
    pullback_scheme := Pullback(j,pt);
    difference := Difference(pullback_scheme, base_scheme);
    differenceK := BaseChange(difference,K);
    points := Points(differenceK);
    return points;
end function;

////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////


// 58 //

// We first deal with the case N=58. The first thing we do is check that the exceptional quadratic points on X_0(29) do not pull back to quadratic points on X_0(58). 
// We do this by checking that none of them have a 2-isogeny, which is equivalent to having a 2-torsion point.
// We take the exceptional j-invariants from the Bruin-Najman paper and check whether a curve with that j-invariant has any 2-torsion. 
// This is a quadratic-twist invariant property, so the choice of the twist does not matter. 

// we use the same model as in the Bruin-Najman paper for the curve X_0(29)

C:=SmallModularCurve(29); 

// There are four exceptional j-invariants that we must test.

d:=-1;
K<w>:=QuadraticField(d);

C1:=ChangeRing(C,K);
P:=C1![w-1,2*w+4];
j:=jInvariant(P,29);
j; // 59*w - 12
E:=EllipticCurveFromjInvariant(j);
TwoTorsionSubgroup(E); // Abelian Group of order 1

/////

P:=C1![w-1,-1];
j:=jInvariant(P,29);
j; // 278824619*w - 321016092
E:=EllipticCurveFromjInvariant(j);
TwoTorsionSubgroup(E); // Abelian Group of order 1

/////

d:=-7;
K<w>:=QuadraticField(d);

C1:=ChangeRing(C,K);
P:=C1![(w+1)/4,(-11*w-7)/16];
j:=jInvariant(P,29); 
j;//  1/4*(697*w - 4915)
E:=EllipticCurveFromjInvariant(j);
TwoTorsionSubgroup(E); // Abelian Group of order 1

/////

P:=C1![(w+1)/4,(5*w+9)/8];
j:=jInvariant(P,29); 
j; // 1/1073741824*(2243516025815593*w - 3839648355219715)
E:=EllipticCurveFromjInvariant(j);
TwoTorsionSubgroup(E); // Abelian Group of order 1

// all checked, none of the exceptional quadratic points on X_0(29) lift to quadratic points on X_0(58)

///////////////////////////////////////////////
///////////////////////////////////////////////

// Next we compute the rational points on X_0(58)/w_29 

X,w,quot:= eqs_quos(58,[[29]]);
"Nice model for X0(58) is:";
X;
Xw:=quot[1,1];  // This is the curve X_0(58)/w_29
quotMap:=quot[1,2]; // This is the quotient map from X_0(58) to X_0(58)/w_29.


RankBounds(Jacobian(Xw)); // 1 1

//The rank is 1, so we can use classical Chabauty over Q. 
J:=Jacobian(Xw);
pts:=RationalPoints(Xw:Bound:=200);  
// {@ (1 : -1 : 0), (1 : 1 : 0), (-1 : -2 : 1), (-1 : 2 : 1), (0 : -1 : 1), (0 : 1 : 1), (1 : -8 : 1), (1 : 8 : 1) @}
P:=pts[1]-pts[2];
P:=J!P;
assert Order(P) eq 0;  // Check the point has infinite order 
pts2:=Chabauty(P);  // Apply Magma's inbuilt Chabauty function.
assert #pts2 eq #pts;
// So we have found all the points.

//////////////////////////////////////

// For each of the rational points we have found on X_0(58)/w_29 we pull them back to points on X_0(58).
// We obtain 4 cusps and 6 pairs of Galois conjugate quadratic points.
// We compute their j-invariant and CM field.
// We find 5 distinct pairs of j-invariants and quadratic fields.
// Using the data from https://github.com/fsaia/least-cm-degree/tree/master/Least%20Degrees/X0, in the file "dcm_list_all_min_orders_X0_10k.m",
// if we have a quadratic CM point on X_0(58)
// then we see that it's quadratic field and j-invariant is one we have already found
// so in the code below, for each pair of j-invariant and quadratic field, we check for any additional points, and
// for K = Q(sqrt(-1)) we do in fact have additional points with j-invariant 1728, and so there is repetition in the output below.

time j:=jmap(X,58); //Time: 10.360
deg2pb:=[Pullback(quotMap,Place(Xw!p)):p in pts];
g:=Genus(X);
for i in [1..#deg2pb] do
	if Degree(ResidueClassField(Decomposition(deg2pb[i])[1,1])) gt 1 then
		K1<z>:=ResidueClassField(Decomposition(deg2pb[i])[1,1]);
		d:=SquarefreeFactorization(Discriminant(K1));
		K<T>:=QuadraticField(d);
		tr,f:=IsIsomorphic(K1,K);
		assert tr;
		P:=RepresentativePoint(Decomposition(deg2pb[i])[1,1]);
		Pw:=[f(P[i]): i in [1..#Coordinates(P)]];
		tr, CM:=HasComplexMultiplication(EllipticCurveFromjInvariant(j(P)[1]));
		assert tr;
		print "We have found a point over Q(T), where T^2=", T^2;
		print "The coordinates of the point are:", Pw;
		print "The j-invariant of the point is:", f(j(P)[1]);
		print "The corresponding elliptic curve has CM by an order of discriminant:", CM;
		if Degree(MinimalPolynomial(f(j(P)[1]))) eq 1 then 
			pts := coords_jK(X, j, f(j(P)[1]), K);
			print "The number of Galois conjugate pairs of quadratic points found with this j-invariant over this field is:", (#pts) div 2;
                        if #pts gt 2 then 
			    print "++++++++++++++++";
			    print "The complete list of points with this j-invariant over this field is:", pts;
                            print "++++++++++++++++";
			end if;
		else 
			print "The j-invariant is not rational. We use a different method";
		end if;		
		print " ";
	end if;
end for;

/* Output:

We have found a point over Q(T), where T^2= -7
The coordinates of the point are: [ 1/3*T, 0, 1/3, 1/3*T, 4/3, 1 ]
The j-invariant of the point is: -3375
The corresponding elliptic curve has CM by an order of discriminant: -7
The number of Galois conjugate pairs of quadratic points found with this 
j-invariant over this field is: 3
++++++++++++++++
The complete list of points with this j-invariant over this field is: {@ (-1 : 
-2/7*T : 1/7*T : 1/7*T : 2 : 1), (-1 : 2/7*T : -1/7*T : -1/7*T : 2 : 1), (1 : 
-2/7*T : 1/7*T : -1/7*T : 2 : 1), (1 : 2/7*T : -1/7*T : 1/7*T : 2 : 1), (-1/3*T 
: 0 : 1/3 : -1/3*T : 4/3 : 1), (1/3*T : 0 : 1/3 : 1/3*T : 4/3 : 1) @}
++++++++++++++++

We have found a point over Q(T), where T^2= -1
The coordinates of the point are: [ 2*T, -1, 1, 0, 3, 1 ]
The j-invariant of the point is: 287496
The corresponding elliptic curve has CM by an order of discriminant: -16
The number of Galois conjugate pairs of quadratic points found with this 
j-invariant over this field is: 1

We have found a point over Q(T), where T^2= -1
The coordinates of the point are: [ 2*T, 1, -1, 0, 3, 1 ]
The j-invariant of the point is: 1728
The corresponding elliptic curve has CM by an order of discriminant: -4
The number of Galois conjugate pairs of quadratic points found with this 
j-invariant over this field is: 2
++++++++++++++++
The complete list of points with this j-invariant over this field is: {@ (0 : 0 
: 0 : -T : 1 : 1), (0 : 0 : 0 : T : 1 : 1), (-2*T : 1 : -1 : 0 : 3 : 1), (2*T : 
1 : -1 : 0 : 3 : 1) @}
++++++++++++++++

We have found a point over Q(T), where T^2= -7
The coordinates of the point are: [ 1/3*T, 0, -1/3, -1/3*T, 4/3, 1 ]
The j-invariant of the point is: 16581375
The corresponding elliptic curve has CM by an order of discriminant: -28
The number of Galois conjugate pairs of quadratic points found with this 
j-invariant over this field is: 1

We have found a point over Q(T), where T^2= 29
The coordinates of the point are: [ 0, 5/29*T, 1/29*T, 1, 0, 0 ]
The j-invariant of the point is: 56147767009798464000*T + 302364978924945672000
The corresponding elliptic curve has CM by an order of discriminant: -232
The j-invariant is not rational. We use a different method

We have found a point over Q(T), where T^2= -1
The coordinates of the point are: [ 0, 0, 0, T, 1, 1 ]
The j-invariant of the point is: 1728
The corresponding elliptic curve has CM by an order of discriminant: -4
The number of Galois conjugate pairs of quadratic points found with this 
j-invariant over this field is: 2
++++++++++++++++
The complete list of points with this j-invariant over this field is: {@ (0 : 0 
: 0 : -T : 1 : 1), (0 : 0 : 0 : T : 1 : 1), (-2*T : 1 : -1 : 0 : 3 : 1), (2*T : 
1 : -1 : 0 : 3 : 1) @}
++++++++++++++++

*/

// It remains to check that the non-rational j-invariant -56147767009798464000*T + 302364978924945672000 (and its conjugate) correspond to only one point.
// We cannot check this directly using the coords_jK function as it requires a rational j-invariant as input.

// We consider two methods for checking there are no additional points with this j-invariant

K<T>:=QuadraticField(29);
jinv:=-56147767009798464000*T + 302364978924945672000;
E:=EllipticCurveFromjInvariant(jinv);
assert #TwoTorsionSubgroup(E) eq 2; //so this curve has only one 2-isogeny
// We now check that it only has one 29-isogeny by using the classical modular polynomial Phi_29(X,Y).
_<x>:=PolynomialRing(K);
Phi_jx := Evaluate(ClassicalModularPolynomial(29), [jinv,x]);
fac:=Factorization(Phi_jx);
assert Degree(fac[1,1]) eq 1; assert Degree(fac[2,1]) ge 2;

// So E has only one 29-isogeny and only one 2-isogeny. 
// Hence it has only 1 58-isogeny, so there's only one point on X_0(58) corresponding to j.

// In addition, although not necessary, we check that elliptic curves with j-invariant j are both 2-isogenoues and 29-isogenoues to their conjugates.

jinv_c:= 56147767009798464000*T + 302364978924945672000;
assert Evaluate(ClassicalModularPolynomial(29), [jinv_c,jinv]) eq 0;
assert Evaluate(ClassicalModularPolynomial(2), [jinv_c,jinv]) eq 0;

///////////////////////////////

// An alternative method is to directly pull back points with the j-map, but this is slow. The following code does this:

/*
XK := ChangeRing(X,K);
P1K := ChangeRing(Codomain(j),K);
jK := map<XK -> P1K | DefiningEquations(j)>;
jinv := P1K ! [jinv];
pb_scheme := Pullback(jK, jinv); 
time Points(pb_scheme); // 250 seconds
// {@ (0 : -5/29*T : -1/29*T : 1 : 0 : 0), (0 : 5/29*T : 1/29*T : 1 : 0 : 0) @}
// We only found the pair of known quadratic points, as expected.
*/

// This completes the case N=58 

/////////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////

// We now consider the cases 68 and 76.

// 68 //

X:=eqs_quos(68,[]);
j:=jmap(X,68);

// We have the following pairs of rational j-invariants and quadratic fields (represented by an integer d) from Ozman-Siksek's classification of quadratic points on X_0(34).

pairs := [<287496, -1>, 
	  <1728, -1>,
	  <8000, -8>];

for pair in pairs do
    jinv := pair[1];
    d := pair[2];
    K<T> := QuadraticField(d);
    pts := coords_jK(X, j, jinv, K);
    if pts eq {@ @} then 
        print "No quadratic points with j-invariant", jinv, "defined over", K;
    else 
	print "Quadratic points with j-invariant", jinv, "defined over", K, "have coordinates", pts, "where T^2 = ", d;
        _, D := HasComplexMultiplication(EllipticCurveWithjInvariant(jinv));
        print "These quadratic points have CM by", D;
    end if;
    print "+++";
end for;
    
/* Output:
Quadratic points with j-invariant 287496 defined over Quadratic Field with 
defining polynomial $.1^2 + 1 over the Rational Field
have coordinates {@ (0 : 0 : 0 : 0 : -1/2*T : -1/4*T : 1), (0 : 0 : 0 : 0 : 
    1/2*T : 1/4*T : 1), (-T : 1 : 0 : 0 : 0 : 1/2*T : 1), (T : 1 : 0 : 0 : 0 : 
-1/2*T : 1) @}
where T^2 =  -1
These quadratic points have CM by -16
+++
Quadratic points with j-invariant 1728 defined over Quadratic Field with 
defining polynomial $.1^2 + 1 over the Rational Field
have coordinates {@ (-T : -1 : 0 : 0 : 0 : -1/2*T : 1), (T : -1 : 0 : 0 : 0 : 
    1/2*T : 1) @}
where T^2 =  -1
These quadratic points have CM by -4
+++
No quadratic points with j-invariant 8000 defined over Quadratic Field with 
defining polynomial $.1^2 + 2 over the Rational Field
+++
*/

// 76 //

X:=eqs_quos(76,[]);
j:=jmap(X,76);

// We have the following pairs of j-invariants and quadratic fields (represented by an integer d) from Ozman-Siksek's classification of quadratic points on X_0(38).

pairs := [<0, -3>, 
	  <54000, -3>,
	  <8000, -2>];

for pair in pairs do
    jinv := pair[1];
    d := pair[2];
    K<T> := QuadraticField(d);
    pts := coords_jK(X, j, jinv, K);
    if pts eq {@ @} then 
        print "No quadratic points with j-invariant", jinv, "defined over", K;
    else 
	print "Quadratic points with j-invariant", jinv, "defined over", K, "have coordinates", pts, "where T^2 = ", d;
        _, D := HasComplexMultiplication(EllipticCurveWithjInvariant(jinv));
        print "These quadratic points have CM by", D;
    end if;
    print "+++";
end for;
    	
/* Output:
No quadratic points with j-invariant 0 defined over Quadratic Field with 
defining polynomial $.1^2 + 3 over the Rational Field
+++
Quadratic points with j-invariant 54000 defined over Quadratic Field with 
defining polynomial $.1^2 + 3 over the Rational Field
have coordinates {@ (-1 : 0 : 0 : -1/3*T : 0 : 1/3*T : 2 : 1), (-1 : 0 : 0 : 
    1/3*T : 0 : -1/3*T : 2 : 1), (1 : 0 : 0 : -1/3*T : 0 : -1/3*T : 2 : 1), (1 :
0 : 0 : 1/3*T : 0 : 1/3*T : 2 : 1) @}
where T^2 =  -3
These quadratic points have CM by -12
+++
No quadratic points with j-invariant 8000 defined over Quadratic Field with 
defining polynomial $.1^2 + 2 over the Rational Field
*/

////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////

////////////////////////
/// Further Examples ///
////////////////////////

// (More) examples of using the function coords_jK for curves in Najman--Vukorepa

/*
// Example 1:
// By Najman-Vukorepa (Theorem 3.2 (b)), on X_0(69), non-cuspidal quadratic points are defined over Q(sqrt(-11)) and have j-invariant -2^(15)
// data from paper:
N := 69;
jinv := -2^(15);
K<a> := QuadraticField(-11);
// We construct a model and the j-map
X := eqs_quos(N,[]); // Genus 7
time j := jmap(X, N); // 20 seconds
// We apply the function
time pts := coords_jK(X,j,jinv,K); // 20 seconds
*/

/* Output:
{@
(0 : 0 : 0 : -1/11*a : -1/11*a : 1 : 1),
(0 : 0 : 0 : -1/11*a : 1/11*a : 1 : 1),
(0 : 0 : 0 : 1/11*a : -1/11*a : 1 : 1),
(0 : 0 : 0 : 1/11*a : 1/11*a : 1 : 1)
@}
*/

// We verify that one of these points indeed has the correct j-invariant
/*
pt := X(K) ! Eltseq(pts[1]);
j(pt); // (-32768 : 1), as expected
*/
/////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////

// Example 2:

// By Najman-Vukorepa (Theorem 3.2 (c)), on X_0(92), non-cuspidal quadratic points are defined over Q(sqrt(-7)) and have j-invariant -3375 or 16581375

// This curve has genus 10, so the computations take a little longer

// data from paper:
/*
N := 92;
jinv1 := -3375;
jinv2 := 16581375;
K<a> := QuadraticField(-7);
// We construct a model and the j-map
X := eqs_quos(N,[]); // Genus 10
time j := jmap(X, N); // 111 seconds
// We apply the function
time coords_jK(X,j,jinv1,K); // 270 seconds
time coords_jK(X,j,jinv2,K); // 313 seconds
*/
/* Output:
// jinv1 = -3375
{@
(-1 : 0 : 0 : 1 : 1/4*(-a + 1) : -1 : 1/2*(a + 9) : 1/2*(a + 3) : 1/2*(a + 3) : 1),
(-1 : 0 : 0 : 1 : 1/4*(-a + 1) : 1 : 1/2*(a + 9) : 1/2*(a + 3) : 1/2*(a + 3) : 1),
(-1 : 0 : 0 : 1 : 1/4*(a + 1) : -1 : 1/2*(-a + 9) : 1/2*(-a + 3) : 1/2*(-a + 3) : 1),
(-1 : 0 : 0 : 1 : 1/4*(a + 1) : 1 : 1/2*(-a + 9) : 1/2*(-a + 3) : 1/2*(-a + 3) : 1),
(-1/7*a : 0 : 2/7*a : 1/7*a : 1/7*a : -1/7*a : 7 : 4 : 2 : 1),
(-1/7*a : 0 : 2/7*a : 1/7*a : 1/7*a : 1/7*a : 7 : 4 : 2 : 1),
(1/7*a : 0 : -2/7*a : -1/7*a : -1/7*a : -1/7*a : 7 : 4 : 2 : 1),
(1/7*a : 0 : -2/7*a : -1/7*a : -1/7*a : 1/7*a : 7 : 4 : 2 : 1)
@}
// jinv2 = 16581375
{@
(1 : 0 : 0 : -1 : 1/4*(-a - 1) : -1 : 1/2*(-a + 9) : 1/2*(-a + 3) : 1/2*(-a + 3) : 1),
(1 : 0 : 0 : -1 : 1/4*(-a - 1) : 1 : 1/2*(-a + 9) : 1/2*(-a + 3) : 1/2*(-a + 3) : 1),
(1 : 0 : 0 : -1 : 1/4*(a - 1) : -1 : 1/2*(a + 9) : 1/2*(a + 3) : 1/2*(a + 3) : 1),
(1 : 0 : 0 : -1 : 1/4*(a - 1) : 1 : 1/2*(a + 9) : 1/2*(a + 3) : 1/2*(a + 3) : 1)
@}
*/

/////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////

// Example 3:

// By Najman-Vukorepa (Theorem 3.2 (a)), on X_0(62), non-cuspidal quadratic points are defined over Q(sqrt(-3)) and have j-invariant 54000 or 0

// data from paper:
/*
N := 62;
jinv1 := 54000;
jinv2 := 0;
K<a> := QuadraticField(-3);
// We construct a model and the j-map
X := eqs_quos(N,[]); // Genus 7
time j := jmap(X, N); // 15 seconds
// We apply the function
time coords_jK(X,j,jinv1,K); // 19 seconds
time coords_jK(X,j,jinv2,K); // 16 seconds
*/
/* Output:
// jinv1 = 54000
{@
(-1/2 : 1/2 : 1/2 : 1/2 : -1/2*a : 2 : 1),
(-1/2 : 1/2 : 1/2 : 1/2 : 1/2*a : 2 : 1)
@}
// jinv2 = 0
{@
(1/2 : -1/2 : -1/2 : -1/2 : -1/2*a : 2 : 1),
(1/2 : -1/2 : -1/2 : -1/2 : 1/2*a : 2 : 1)
@}
*/
