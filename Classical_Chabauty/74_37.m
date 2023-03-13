// The code in this file computes all the rational points on X_0(74) / w_37

load "model_equation_finder.m";
load "coleman.m";

 P3<W,X,Y,Z> := ProjectiveSpace(Rationals(),3);
X74_w37 := X0NQuotient(74, [37]);
Q := find_and_test_model_Q_only(W, W+2*X-Y, Y, W+2*X-Y, X74_w37, x, y);

Q;
// this is one monic model for X0(74)_w37
//y^5 + (-2*x - 1)*y^4 + (2*x^2 - 3*x - 1)*y^3 + (11*x^2 + 1)*y^2 + (-3*x^4 +3*x^3 - x^2 + 5*x)*y + 2*x^5 + 6*x^4 - 14*x^3 + 6*x^2



p := 11; 
N := 12;
data := coleman_data(Q,p,N);

Qpoints := Q_points(data,1000);
//Assuming that the Q-rational points found generate a finite index subgroup of the Jacobian of X_0(74)/w37,
// the following code proves that these are all Q-points.
// This assumption is checked at the end of this file.

L, v := effective_chabauty(data : Qpoints := Qpoints, e := 40);

//printf "L = %o\nQ-points = %o\nv = %o\n", L, Qpoints, v;
//uncomment the previous line to get a bit more info
//about annihilating differentials and their zeroes (candidate points)


if #L eq #Qpoints then
  printf "found all %o Q-points!\n", #Qpoints;
else
  printf "one has to exclude additional %o points\n", #L - #Qpoints;
end if;

//found all 9 Q-points!

// We check that the differences of the rational points found generate a finite index (rank 2) subgroup.

pts := PointSearch(X74_w37, 10);
assert #pts eq 9;
// [ (-1 : 0 : 1 : 0), (-1 : -1 : 1 : 1), (0 : 1 : 1 : 0), (0 : 1 : 0 : 0), (0 : 0 : 0 : 1), (1 : -1 : -1 : 1), (0 : 1 : 0 : 1), (1 : 0 : 1 : 0), (-1 : 0 : 0 : 1) ]
pseq1 := [0,0,0,1];
pseq2 := [0,1,0,0];
pseq3 := [0,1,1,0];

// We aim to show that the divisors formed by d1 = pseq1-pseq2 and d2 = pseq1-pseq3 generate a rank 2 subgroup of the Jacobian over Q
// We do this in two steps (which we combine in the code for efficiency).
// Step 1a) We show that the divisor d1 has infinite order in the Jacobian by checking that its order mod 3 and its order mod 5 are different
// Step 1b) We repeat step 1a) with the divisor d2
// Step 2) We verify that d1 and d2 are linearly independent in the Jacobian by checking they are linearly independent mod 3

p := 3;
Xp := ChangeRing(X74_w37, GF(p));
assert IsNonsingular(Xp);
PicXp, phi, psi := ClassGroup(Xp);
JFp := TorsionSubgroup(PicXp);
d1p := psi(Place(Xp ! pseq1) - Place(Xp ! pseq2));
d2p := psi(Place(Xp ! pseq1) - Place(Xp ! pseq3));

assert Order(d1p) eq 7;
assert Order(d2p) eq 133;

A := sub<JFp | [d1p,d2p]>; // Abelian Group isomorphic to Z/7 + Z/133
// So the points are linearly independent mod 3

p := 5;
Xp := ChangeRing(X74_w37, GF(p));
assert IsNonsingular(Xp);
PicXp, phi, psi := ClassGroup(Xp);
JFp := TorsionSubgroup(PicXp);
d1p := psi(Place(Xp ! pseq1) - Place(Xp ! pseq2));
d2p := psi(Place(Xp ! pseq1) - Place(Xp ! pseq3));

assert Order(d1p) eq 8; // 8 is different from 7, so d1 is not a torsion point
assert Order(d2p) eq 152; // 152 is different from 133, so d2 is not a torsion point

