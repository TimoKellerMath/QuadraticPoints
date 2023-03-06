/////////////////
/// coords_jk ///
/////////////////

// Function for computing points with a given j-invariant
// Please see the examples at the end of the file to see how to use the function

load new_models.m;

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

////////////////
/// Examples ///
////////////////

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

/* Output:

{@
(0 : 0 : 0 : -1/11*a : -1/11*a : 1 : 1),
(0 : 0 : 0 : -1/11*a : 1/11*a : 1 : 1),
(0 : 0 : 0 : 1/11*a : -1/11*a : 1 : 1),
(0 : 0 : 0 : 1/11*a : 1/11*a : 1 : 1)
@}

*/

// We verify that one of these points indeed has the correct j-invariant

pt := X(K) ! Eltseq(pts[1]);
j(pt); // (-32768 : 1), as expected

/////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////

// Example 2:

// By Najman-Vukorepa (Theorem 3.2 (c)), on X_0(92), non-cuspidal quadratic points are defined over Q(sqrt(-7)) and have j-invariant -3375 or 16581375

// This curve has genus 10, so the computations take a little longer

// data from paper:

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
