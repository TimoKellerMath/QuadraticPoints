
load "model_equation_finder.m";
load "coleman.m";

 P3<W,X,Y,Z> := ProjectiveSpace(Rationals(),3);
X86_w43 := X0NQuotient(86, [43]);
Q := find_and_test_model_Q_only(W, W+2*X-Y, Y, W+2*X-Y, X86_w43, x, y);

Q;
// this is one monic model for X0(86)_w43



p := 13; 
N := 12;
data := coleman_data(Q,p,N);

Qpoints := Q_points(data,1000);
//Assuming that the Q-rational points found generate a finite index subgroup of the Jacobian of X_0(86)/w43,
// the following code proves that these are all Q-points.
// This assumption is checked at the end of this file

L, v := effective_chabauty(data : Qpoints := Qpoints, e := 40);

//printf "L = %o\nQ-points = %o\nv = %o\n", L, Qpoints, v;

if #L eq #Qpoints then
  printf "found all %o Q-points!\n", #Qpoints;
else
  printf "one has to exclude additional %o points\n", #L - #Qpoints;
end if;

//found all 7 Q-points!

// We check that the differences of the rational points found generate a finite index (rank 2) subgroup.

pts := PointSearch(X86_w43, 10);
assert #pts eq 7;
p := 3;
Xp := ChangeRing(X86_w43, GF(p));
assert IsNonsingular(Xp);
ptsp := [Xp!ChangeUniverse(Eltseq(pt), GF(p)) : pt in pts]; // reductions of Q-points
PicXp, phi, psi := ClassGroup(Xp);
JFp := TorsionSubgroup(PicXp);
divsp := [psi(Place(ptsp[i]) - Place(ptsp[1])) : i in [2..#ptsp]];
A := sub<JFp | divsp>; // Abelian Group isomorphic to Z/6 + Z/66, so rank is 2
