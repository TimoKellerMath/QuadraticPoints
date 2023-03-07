
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
p := 3;
Xp := ChangeRing(X74_w37, GF(p));
assert IsNonsingular(Xp);
ptsp := [Xp!ChangeUniverse(Eltseq(pt), GF(p)) : pt in pts]; // reductions of Q-points
PicXp, phi, psi := ClassGroup(Xp);
JFp := TorsionSubgroup(PicXp);
divsp := [psi(Place(ptsp[i]) - Place(ptsp[1])) : i in [2..#ptsp]];
A := sub<JFp | divsp>; // Abelian Group isomorphic to Z/7 + Z/133, so rank is 2
