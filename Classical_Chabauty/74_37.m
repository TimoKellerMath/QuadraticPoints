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
// We do this in three steps 

// Write J for the Jacobian of the curve X_0(74)/w_37

// Step 1: We prove that J(Q)_tors is a subgroup of Z/19Z
// Step 2: We verify that d_1 and d_2 both have infinite order by considering their reductions modulo 3 and 5 
// Step 3: We verify that d_1 and d_2 are linearly independent points of the Jacobian

// Step 1: 

X3 := ChangeRing(X74_w37, GF(3));
assert IsNonsingular(X3);
PicX3, phi3, psi3 := ClassGroup(X3);
JF3 := TorsionSubgroup(PicX3);

X5 := ChangeRing(X74_w37, GF(5));
assert IsNonsingular(X5);
PicX5, phi5, psi5 := ClassGroup(X5);
JF5 := TorsionSubgroup(PicX5);

assert GCD(#JF3, #JF5) eq 19;
// So J(Q)_tors is a subgroup of Z / 19 Z.

// Step 2:

// We construct the points in the Jacobian mod 3 and mod 5:

d1_mod3 := psi3(Place(X3 ! pseq1) - Place(X3 ! pseq2));
d2_mod3 := psi3(Place(X3 ! pseq1) - Place(X3 ! pseq3));

d1_mod5 := psi5(Place(X5 ! pseq1) - Place(X5 ! pseq2));
d2_mod5 := psi5(Place(X5 ! pseq1) - Place(X5 ! pseq3));

// If d1 were a torsion point then it would have the same order mod 3 and mod 5.
assert Order(d1_mod3) ne Order(d1_mod5); // So d1 has infinite order
// Similarly for d2:
assert Order(d2_mod3) ne Order(d2_mod5); // So d2 has infinite order

// Step 3:

// If d1 and d2 were linearly dependent, 
// then they would generate a group isomorphic to Z x G. 
// Here, Z means the integers and
// G is a subgroup of J(Q)_tors, which in turn is a subgroup of Z/19Z

// It follows that the image of <d_1, d_2> in J(F_3) must be of the form:
// Z/aZ or Z/aZ x Z/19Z for some integer a > 1.

// We compute the image of <d_1, d_2> in J(F_3):

A := sub<JF3 | [d1_mod3, d2_mod3] >; 
assert IsIsomorphic(A,AbelianGroup([7,7,19]));
// This group is not of the form Z/aZ or Z/aZ x Z/19Z
// So the points d_1 and d_2 are linearly independent.





