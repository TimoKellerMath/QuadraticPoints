
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
// This assumption is checked in file independence.m

L, v := effective_chabauty(data : Qpoints := Qpoints, e := 40);

//printf "L = %o\nQ-points = %o\nv = %o\n", L, Qpoints, v;

if #L eq #Qpoints then
  printf "found all %o Q-points!\n", #Qpoints;
else
  printf "one has to exclude additional %o points\n", #L - #Qpoints;
end if;

//found all 7 Q-points!
