// This file contains all computations used in the going-down method

load  "models_and_maps.m";

// We will make use of the following function

/////////////////
/// coords_jk ///
/////////////////

// Function for computing points with a given j-invariant
// Please see the examples at the end of the file for further detailed examples of usage

// Input: X, j, jinv, K

// X is a model for X_0(N) (obtained from eqs_quos) (non-hyperelliptic genus > 2)
// j is the j map on this model to P^1 (obtained from jmap)
// jinv is the j-invariant of the point of interest
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


// %%%%%%%%%%%%%%%%%%%%%%%% N=58 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
// We first deal with the case N=58. The first thing we do is that the exceptional quadratic points on $X_0(29)$ do not pull back to quadratic points on X_0(58). 
// We do this by checking that none of them have a 2-isogeny, which is quivalent to having a 2-torsion points.
// We take the exceptional j-invarinants from the Bruin-Najman paper and check whether a curvee with that j-invariant has any 2-torsion. 
// This is a quadratic-twist invaraiant property, so the choice of the twist does not matter. 

C:=SmallModularCurve(29);

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

// all checked, hence none of the exceptional quadratic points on X_0(29) lift to quadratic points on X_0(58)



///////////////////////////////////////////////
///////////////////////////////////////////////


X,w,quot:= eqs_quos(58,[[29]]);
"Nice model for X0(58) is:";
X;
Xw:=quot[1,1];
quotMap:=quot[1,2];


RankBounds(Jacobian(Xw)); // 1 1

//The rank is 1, so we can use classical Chabauty over Q. 
J:=Jacobian(Xw);
pts:=RationalPoints(Xw:Bound:=200);
// {@ (1 : -1 : 0), (1 : 1 : 0), (-1 : -2 : 1), (-1 : 2 : 1), (0 : -1 : 1), (0 : 1 : 1), (1 : -8 : 1), (1 : 8 : 1) @}
P:=pts[1]-pts[2];
P:=J!P;
assert Order(P) eq 0;
pts2:=Chabauty(P);
assert #pts2 eq #pts;
// so we have found all the points. It remains to find the j-invariants.

//////////////////////////////////////


j:=jmap(X,58);
deg2pb:=[Pullback(quotMap,Place(Xw!p)):p in pts];
g:=Genus(X);
for i in [1..#deg2pb] do
	if Degree(ResidueClassField(Decomposition(deg2pb[i])[1,1])) gt 1 then
		K1<z>:=ResidueClassField(Decomposition(deg2pb[i])[1,1]);
		d:=SquarefreeFactorization(Discriminant(K1));
		K<w>:=QuadraticField(d);
		tr,f:=IsIsomorphic(K1,K);
		assert tr;
		P:=RepresentativePoint(Decomposition(deg2pb[i])[1,1]);
		Pw:=[f(P[i]): i in [1..#Coordinates(P)]];
		tr, CM:=HasComplexMultiplication(EllipticCurveFromjInvariant(j(P)[1]));
		print "We have found a point over Q(w), where w^2=", w^2;
		print "The coordinates of the point are:", Pw;
		print "The j-invariant of the point is:", f(j(P)[1]);
		print "The corresponding elliptic curve has CM by an order of discriminant:", CM;
		print " ";
		//w^2,Pw,f(j(P)[1]),HasComplexMultiplication(EllipticCurveFromjInvariant(j(P)[1]));
	end if;
end for;

/* Output:

We have found a point over Q(w), where w^2= -7
The coordinates of the point are: [ 1/3*w, 0, 1/3, 1/3*w, 4/3, 1 ]
The j-invariant of the point is: -3375
The corresponding elliptic curve has CM by an order of discriminant: -7

We have found a point over Q(w), where w^2= -1
The coordinates of the point are: [ 2*w, -1, 1, 0, 3, 1 ]
The j-invariant of the point is: 287496
The corresponding elliptic curve has CM by an order of discriminant: -16

We have found a point over Q(w), where w^2= -1
The coordinates of the point are: [ -2*w, 1, -1, 0, 3, 1 ]
The j-invariant of the point is: 1728
The corresponding elliptic curve has CM by an order of discriminant: -4

We have found a point over Q(w), where w^2= -7
The coordinates of the point are: [ 1/3*w, 0, -1/3, -1/3*w, 4/3, 1 ]
The j-invariant of the point is: 16581375
The corresponding elliptic curve has CM by an order of discriminant: -28

We have found a point over Q(w), where w^2= 29
The coordinates of the point are: [ 0, -5/29*w, -1/29*w, 1, 0, 0 ]
The j-invariant of the point is: -56147767009798464000*w + 302364978924945672000
The corresponding elliptic curve has CM by an order of discriminant: -232

We have found a point over Q(w), where w^2= -1
The coordinates of the point are: [ 0, 0, 0, w, 1, 1 ]
The j-invariant of the point is: 1728
The corresponding elliptic curve has CM by an order of discriminant: -4

*/

// This completes the case N=58 

/////////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////

/* The list of CM points below has been sent to us by P. L. Clark, T. Genao, P. Pollack, and F. Saia, and can be obtained from their paper. 
See also: https://github.com/tgenao/least-cm-degree

The N'th element in this list has the form [* N, d_{CM}(X_0(N)), [ orders ] *], where [ orders ] is the complete sequence of imaginary quadratic orders O such that O minimizes d_{CM}(X_0(N)), i.e., d_{O,CM}(X_0(N)) = d_{CM}(X_0(N)). 

The orders O are given in the form [f, d_K, h(O)] := [conductor, fundamental discriminant, class number of O] -- the class number is only included for convenience. */


t68:=[* 68, 2,
    [   [ 1, -4, 1 ],
        [ 2, -4, 1 ]
    ]
*];


t76:=[* 76, 2,
    [
        [ 2, -3, 1 ]
    ]
*];



t108:=[* 108, 4,
    [
        [ 1, -8, 1 ],
        [ 2, -8, 2 ]
    ]
*];

// there are no degree 2 CM points on X0(108)

ComputejInvs:= function(A);
    n:=#A[3];
    ret:=[];
    for i:=1 to n do 
	    B:=A[3,i];
	    D:=B[2]*B[1]^2;
	    j:=Round(jInvariant(BinaryQuadraticForms(D)!1));
	    ret:= Append(ret, [j, D]);
    end for;
    return ret;
end function;

//this gives us the CM j-invariants which correspond to quadratic points on X_0(68)
j68:=ComputejInvs(t68); 
/* returns
[
    [ 1728, -4 ],
    [ 287496, -16 ]
]
*/
// now we want to determine a model for X_0(68) and the coordinates of corresponding points
X:=eqs_quos(68,[]);
"Nice model for X0(68) is:";
X;
j:=jmap(X,68);
time for i:= 1 to #j68 do
    d:=SquareFreeFactorization(Integers()!j68[i,2]);
    K<w>:=QuadraticField(d);
    K, coords_jK(X,j,K!(j68[i,1]),K);
end for;

/* Output:
Quadratic Field with defining polynomial $.1^2 + 1 over the Rational Field
{@ (-w : -1 : 0 : 0 : 0 : -1/2*w : 1), (w : -1 : 0 : 0 : 0 : 1/2*w : 1) @}
Quadratic Field with defining polynomial $.1^2 + 1 over the Rational Field
{@ (0 : 0 : 0 : 0 : -1/2*w : -1/4*w : 1), (0 : 0 : 0 : 0 : 1/2*w : 1/4*w : 1),
(-w : 1 : 0 : 0 : 0 : 1/2*w : 1), (w : 1 : 0 : 0 : 0 : -1/2*w : 1) @}
Time: 173.390
*/

/////////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////

// The case N=76 remains. We now deal with it 

X:=eqs_quos(76,[]);
"Nice model for X0(76) is:";
X;
j:=jmap(X,76);
j76:=ComputejInvs(t76); 
/* returns:

[
    [ 54000, -12 ]
]

*/
time for i:= 1 to #j76 do
    d:=SquareFreeFactorization(Integers()!j76[i,2]);
    K<w>:=QuadraticField(d);
    K, coords_jK(X,j,K!j76[i,1],K);
end for;

/* Output
Quadratic Field with defining polynomial $.1^2 + 3 over the Rational Field
{@ (-1 : 0 : 0 : -1/3*w : 0 : 1/3*w : 2 : 1), (-1 : 0 : 0 : 1/3*w : 0 : -1/3*w :
2 : 1), (1 : 0 : 0 : -1/3*w : 0 : -1/3*w : 2 : 1), (1 : 0 : 0 : 1/3*w : 0 : 
    1/3*w : 2 : 1) @}
Time: 18.070
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
