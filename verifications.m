// In this file we verify the data contained in the tables of the paper and give / check coordinates of points
// We also print the majority of this data

// For each level N and quadratic point P we:
// Give the model for X_0(N) and print it
// Give the Atkin-Lehner involutions (in ascedning index order) and print them
// Give the coordinates of P, check it lies on our model, and print the point (together with its field of definition)
// Compute the j-invariant of the point and print it
// Verify whether the point is a CM point, and if so we check the CM discriminant and print it
// Verify the Atkin-Lehner diagrams provided (no printed output)

// The output of this file is in verifications.out in the Output_files folder

// In order to reproduce the data in this file from scratch,
// one can use the functions and commands in the pullbacks.m file

load "models_and_maps.m";

// auxiliary function to compute the conjugate of a sequence of elements in a quadratic field

conj := function(PPseq);
    return [Conjugate(cc) : cc in PPseq];
end function;

// auxiliary function to extract d, when a quadratic point lies in Q(sqrt(d)
// (used for print statements)

dd := function(PP);
    return  -Coefficient(DefiningPolynomial(Ring(Parent(PP))),0);
end function;

// auxiliary function to check a j invariant is CM and extract the CM discriminant

CMdisc:= function(j);
    tf, D := HasComplexMultiplication(EllipticCurveWithjInvariant(j));
    assert tf;
    return D;
end function;


////////////////////////////////////////////

////////////////
//// N = 58 ////
////////////////

N := 58;
print "N =", N;
X, ws := eqs_quos(N,[]);
al_inds := [m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
print "Model:";
X;
for i in [1..#al_inds] do
    m := al_inds[i];
    print "w_",m, "is given by", DefiningEquations(ws[i]);
end for;
w2 := ws[1];
w29 := ws[2];
w58 := ws[3];
j := jmap(X,N);

///////////

K<T> := QuadraticField(-1);

P1seq := [-2*T, 1, -1, 0, 3, 1];
P1 := X(K) ! P1seq;
P1c := X(K) ! conj(P1seq);
jP1 := j(P1)[1];
assert jP1 eq 1728;
D :=  CMdisc(jP1);
assert D eq -4;

P2seq := [2*T, -1, 1, 0, 3, 1];
P2 := X(K) ! P2seq;
P2c := X(K) ! conj(P2seq);
jP2 := j(P2)[1];
assert jP2 eq 287496;
D :=  CMdisc(jP2);
assert D eq -16;

assert w29(P1) eq P1c;
assert w2(P1) eq P2;
assert w58(P1) eq P2c;
assert w29(P2) eq P2c;
assert w58(P2) eq P1c;
assert w2(P1c) eq P2c;

P3seq := [0, 0, 0, T, 1, 1];
P3 := X(K) ! P3seq;
P3c := X(K) ! conj(P3seq);
jP3 := j(P3)[1];
assert jP3 eq 1728;
D :=  CMdisc(jP3);
assert D eq -4;

assert w29(P3) eq P3c;
assert w58(P3) eq P3c;
assert w2(P3) eq P3;
assert w2(P3c) eq P3c;

///////////

K<T> := QuadraticField(-7);

P4seq := [1/3*T, 0, 1/3, 1/3*T, 4/3, 1];
P4 := X(K) ! P4seq;
P4c := X(K) ! conj(P4seq);
jP4 := j(P4)[1];
assert jP4 eq -3375;
D :=  CMdisc(jP4);
assert D eq -7;

P5seq := [1/3*T, 0, -1/3, -1/3*T, 4/3, 1];
P5 := X(K) ! P5seq;
P5c := X(K) ! conj(P5seq);
jP5 := j(P5)[1];
assert jP5 eq 16581375;
D :=  CMdisc(jP5);
assert D eq -28;

assert w29(P4) eq P4c;
assert w2(P4) eq P5c;
assert w58(P4) eq P5;
assert w29(P5) eq P5c;
assert w2(P5) eq P4c;
assert w58(P4c) eq P5c;

///////////

K<T> := QuadraticField(29);

P6seq := [0, -5/29*T, -1/29*T, 1, 0, 0];
P6 := X(K) ! P6seq;
P6c := X(K) ! conj(P6seq);
jP6 := j(P6)[1];
assert jP6 eq -56147767009798464000*T + 302364978924945672000;
D :=  CMdisc(jP6);
assert D eq -232;

assert w2(P6) eq P6c;
assert w29(P6) eq P6c;
assert w58(P6) eq P6;
assert w58(P6c) eq P6c;

print "P1 coordinates:", P1, "where T^2 =", dd(P1), "and j-invariant =", jP1, "and CM by", CMdisc(jP1);
print "P2 coordinates:", P2, "where T^2 =", dd(P2), "and j-invariant =", jP2, "and CM by", CMdisc(jP2);
print "P3 coordinates:", P3, "where T^2 =", dd(P3), "and j-invariant =", jP3, "and CM by", CMdisc(jP3);
print "P4 coordinates:", P4, "where T^2 =", dd(P4), "and j-invariant =", jP4, "and CM by", CMdisc(jP4);
print "P5 coordinates:", P5, "where T^2 =", dd(P5), "and j-invariant =", jP5, "and CM by", CMdisc(jP5);
print "P6 coordinates:", P6, "where T^2 =", dd(P6), "and j-invariant =", jP6, "and CM by", CMdisc(jP6);
print "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

////////////////
//// N = 68 ////
////////////////

N := 68;
print "N =", N;
X, ws := eqs_quos(N,[]);
al_inds := [m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
print "Model:";
X;
for i in [1..#al_inds] do
    m := al_inds[i];
    print "w_",m, "is given by", DefiningEquations(ws[i]);
end for;
w4 := ws[1];
w17 := ws[2];
w68 := ws[3];
j := jmap(X,N);

///////////

K<T> := QuadraticField(-1);

P1seq := [-T , -1 , 0 , 0 , 0 , -1/2*T , 1];
P1 := X(K) ! P1seq;
P1c := X(K) ! conj(P1seq);
jP1 := j(P1)[1];
assert jP1 eq 1728;
D :=  CMdisc(jP1);
assert D eq -4;

P2seq := [T , 1 , 0 , 0 , 0 , -T/2 , 1];
P2 := X(K) ! P2seq;
P2c := X(K) ! conj(P2seq);
jP2 := j(P2)[1];
assert jP2 eq 287496;
D :=  CMdisc(jP2);
assert D eq -16;

assert w17(P1) eq P1c;
assert w68(P1) eq P2c;
assert w4(P1) eq P2;
assert w17(P2) eq P2c;
assert w68(P2) eq P1c;
assert w4(P1c) eq P2c;

P3seq := [0 , 0 , 0 , 0 , -T/2 , -T/4 , 1];
P3 := X(K) ! P3seq;
P3c := X(K) ! conj(P3seq);
jP3 := j(P3)[1];
assert jP3 eq 287496;
D :=  CMdisc(jP3);
assert D eq -16;

assert w68(P3) eq P3c;
assert w17(P3) eq P3c;
assert w4(P3) eq P3;

print "P1 coordinates:", P1, "where T^2 =", dd(P1), "and j-invariant =", jP1, "and CM by", CMdisc(jP1);
print "P2 coordinates:", P2, "where T^2 =", dd(P2), "and j-invariant =", jP2, "and CM by", CMdisc(jP2);
print "P3 coordinates:", P3, "where T^2 =", dd(P3), "and j-invariant =", jP3, "and CM by", CMdisc(jP3);
print "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

////////////////
//// N = 74 ////
////////////////

N := 74;
print "N =", N;
X, ws := eqs_quos(N,[]);
al_inds := [m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
print "Model:";
X;
for i in [1..#al_inds] do
    m := al_inds[i];
    print "w_",m, "is given by", DefiningEquations(ws[i]);
end for;
w2 := ws[1];
w37 := ws[2];
w74 := ws[3];
j := jmap(X,N);

///////////

K<T> := QuadraticField(-7);

P1seq := [-1, 0, 0, 1/T, 2/T, -2/T, 1/T, 1];
P1 := X(K) ! P1seq;
P1c := X(K) ! conj(P1seq);
jP1 := j(P1)[1];
assert jP1 eq -3375;
D :=  CMdisc(jP1);
assert D eq -7;

P2seq := [1, 0, 0, 1/T, -2/T, 2/T, -1/T, 1];
P2 := X(K) ! P2seq;
P2c := X(K) ! conj(P2seq);
jP2 := j(P2)[1];
assert jP2 eq -3375;
D :=  CMdisc(jP2);
assert D eq -7;

assert w74(P1) eq P1c;
assert w2(P1) eq P2c;
assert w37(P1) eq P2;
assert w2(P2) eq P1c;
assert w74(P2) eq P2c;
assert w37(P1c) eq P2c;

///////////

K<T> := QuadraticField(-7);

P3seq := [T, -2, -2, 1, 0, 0, -T, 1];
P3 := X(K) ! P3seq;
P3c := X(K) ! conj(P3seq);
jP3 := j(P3)[1];
assert jP3 eq -3375;
D :=  CMdisc(jP3);
assert D eq -7;

P4seq := [T, 2, 2, -1, 0, 0, T, 1];
P4 := X(K) ! P4seq;
P4c := X(K) ! conj(P4seq);
jP4 := j(P4)[1];
assert jP4 eq 16581375;
D :=  CMdisc(jP4);
assert D eq -28;

assert w37(P3) eq P3c;
assert w2(P3) eq P4c;
assert w74(P3) eq P4;
assert w2(P4) eq P3c;
assert w37(P4) eq P4c;
assert w74(P3c) eq P4c;

///////////

K<T> := QuadraticField(-1);

P5seq := [0,0,0,0,-3*T/4,T/2,-T/4,1];
P5 := X(K) ! P5seq;
P5c := X(K) ! conj(P5seq);
jP5 := j(P5)[1];
assert jP5 eq 1728;
D :=  CMdisc(jP5);
assert D eq -4;

assert w2(P5) eq P5;
assert w2(P5c) eq P5c;
assert w37(P5) eq P5c;
assert w74(P5) eq P5c;

///////////

K<T> := QuadraticField(-1);

P6seq := [2,T,0,-T,1,0,1,0];
P6 := X(K) ! P6seq;
P6c := X(K) ! conj(P6seq);
jP6 := j(P6)[1];
assert jP6 eq 1728;
D :=  CMdisc(jP6);
assert D eq -4;

P7seq := [-2,T,0,-T,1,0,1,0];
P7 := X(K) ! P7seq;
P7c := X(K) ! conj(P7seq);
jP7 := j(P7)[1];
assert jP7 eq 287496;
D :=  CMdisc(jP7);
assert D eq -16;

assert w37(P6) eq P6c;
assert w2(P6) eq P7c;
assert w74(P6) eq P7;
assert w2(P7) eq P6c;
assert w37(P7) eq P7c;
assert w74(P6c) eq P7c;

///////////

K<T> := QuadraticField(-3);

P8seq := [-T,-1/2, 1/2, 1/2,-T/2,T/2,-T/2,1];
P8 := X(K) ! P8seq;
P8c := X(K) ! conj(P8seq);
jP8 := j(P8)[1];
assert jP8 eq 54000;
D :=  CMdisc(jP8);
assert D eq -12;

P9seq := [T,1/2, -1/2, -1/2,-T/2,T/2,-T/2,1];
P9 := X(K) ! P9seq;
P9c := X(K) ! conj(P9seq);
jP9 := j(P9)[1];
assert jP9 eq 0;
D :=  CMdisc(jP9);
assert D eq -3;

assert w37(P8) eq P8c;
assert w74(P8) eq P9c;
assert w2(P8) eq P9;
assert w74(P9) eq P8c;
assert w37(P9) eq P9c;
assert w2(P8c) eq P9c;

///////////

K<T> := QuadraticField(37);

P10seq := [0, 5/(2*T), -1/T,  1/(2*T), 0, 0, 0, 1];
P10 := X(K) ! P10seq;
P10c := X(K) ! conj(P10seq);
jP10 := j(P10)[1];
assert jP10 eq -3260047059360000*T + 19830091900536000;
D :=  CMdisc(jP10);
assert D eq -148;

assert w37(P10) eq P10;
assert w37(P10c) eq P10c;
assert w2(P10) eq P10c;
assert w74(P10) eq P10c;

print "P1 coordinates:", P1, "where T^2 =", dd(P1), "and j-invariant =", jP1, "and CM by", CMdisc(jP1);
print "P2 coordinates:", P2, "where T^2 =", dd(P2), "and j-invariant =", jP2, "and CM by", CMdisc(jP2);
print "P3 coordinates:", P3, "where T^2 =", dd(P3), "and j-invariant =", jP3, "and CM by", CMdisc(jP3);
print "P4 coordinates:", P4, "where T^2 =", dd(P4), "and j-invariant =", jP4, "and CM by", CMdisc(jP4);
print "P5 coordinates:", P5, "where T^2 =", dd(P5), "and j-invariant =", jP5, "and CM by", CMdisc(jP5);
print "P6 coordinates:", P6, "where T^2 =", dd(P6), "and j-invariant =", jP6, "and CM by", CMdisc(jP6);
print "P7 coordinates:", P7, "where T^2 =", dd(P7), "and j-invariant =", jP7, "and CM by", CMdisc(jP7);
print "P8 coordinates:", P8, "where T^2 =", dd(P8), "and j-invariant =", jP8, "and CM by", CMdisc(jP8);
print "P9 coordinates:", P9, "where T^2 =", dd(P9), "and j-invariant =", jP9, "and CM by", CMdisc(jP9);
print "P10 coordinates:", P10, "where T^2 =", dd(P10), "and j-invariant =", jP10, "and CM by", CMdisc(jP10);
print "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

////////////////
//// N = 76 ////
////////////////

N := 76;
print "N =", N;
X, ws := eqs_quos(N,[]);
al_inds := [m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
print "Model:";
X;
for i in [1..#al_inds] do
    m := al_inds[i];
    print "w_",m, "is given by", DefiningEquations(ws[i]);
end for;
w4 := ws[1];
w19 := ws[2];
w76 := ws[3];
j := jmap(X,N);

///////////

K<T> := QuadraticField(-3);

P1seq := [-1 , 0 , 0 , T/3, 0 , -T/3 , 2 , 1];
P1 := X(K) ! P1seq;
P1c := X(K) ! conj(P1seq);
jP1 := j(P1)[1];
assert jP1 eq 54000;
D :=  CMdisc(jP1);
assert D eq -12;

P2seq := [1 , 0 , 0 , -T/3 , 0 , -T/3 , 2 , 1];
P2 := X(K) ! P2seq;
P2c := X(K) ! conj(P2seq);
jP2 := j(P2)[1];
assert jP2 eq 54000;
D :=  CMdisc(jP2);
assert D eq -12;

assert w76(P1) eq P1c;
assert w4(P1) eq P2;
assert w19(P1) eq P2c;
assert w76(P2) eq P2c;
assert w19(P2) eq P1c;
assert w4(P1c) eq P2c;

print "P1 coordinates:", P1, "where T^2 =", dd(P1), "and j-invariant =", jP1, "and CM by", CMdisc(jP1);
print "P2 coordinates:", P2, "where T^2 =", dd(P2), "and j-invariant =", jP2, "and CM by", CMdisc(jP2);
print "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

////////////////
//// N = 80 ////
////////////////

N := 80;
print "N =", N;
X, ws := eqs_quos(N,[]);
al_inds := [m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
print "Model:";
X;
for i in [1..#al_inds] do
    m := al_inds[i];
    print "w_",m, "is given by", DefiningEquations(ws[i]);
end for;

print "No non-cuspidal quadratic points";
print "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

////////////////
//// N = 85 ////
////////////////

N := 85;
print "N =", N;
X, ws := eqs_quos(N,[]);
al_inds := [m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
print "Model:";
X;
for i in [1..#al_inds] do
    m := al_inds[i];
    print "w_",m, "is given by", DefiningEquations(ws[i]);
end for;
w5 := ws[1];
w17 := ws[2];
w85 := ws[3];
j := jmap(X,N);

///////////

K<T> := QuadraticField(-19);

P1seq := [-1,0, T/19,2*T/19, -T/19,2*T/19, 1];
P1 := X(K) ! P1seq;
P1c := X(K) ! conj(P1seq);
jP1 := j(P1)[1];
assert jP1 eq -884736;
D :=  CMdisc(jP1);
assert D eq -19;

P2seq := [1,0, T/19,2*T/19, T/19,-2*T/19, 1];
P2 := X(K) ! P2seq;
P2c := X(K) ! conj(P2seq);
jP2 := j(P2)[1];
assert jP2 eq -884736;
D :=  CMdisc(jP2);
assert D eq -19;

assert w85(P1) eq P1c;
assert w5(P1) eq P2c;
assert w17(P1) eq P2;
assert w5(P2) eq P1c;
assert w85(P2) eq P2c;
assert w17(P1c) eq P2c;

///////////

K<T> := QuadraticField(-1);

P3seq := [1/2, 1/2, T/4, -T/2, -T/2, T/4, 1];
P3 := X(K) ! P3seq;
P3c := X(K) ! conj(P3seq);
jP3 := j(P3)[1];
assert jP3 eq 1728;
D :=  CMdisc(jP3);
assert D eq -4;

P4seq := [-1/2, -1/2, T/4, -T/2, T/2, -T/4, 1];
P4 := X(K) ! P4seq;
P4c := X(K) ! conj(P4seq);
jP4 := j(P4)[1];
assert jP4 eq 1728;
D :=  CMdisc(jP4);
assert D eq -4;

assert w85(P3) eq P3c;
assert w5(P3) eq P4c;
assert w17(P3) eq P4;
assert w5(P4) eq P3c;
assert w85(P4) eq P4c;
assert w17(P3c) eq P4c;

///////////

P5seq := [1/2, 1/2, 0, T/2, T/2, 0, 1];
P5 := X(K) ! P5seq;
P5c := X(K) ! conj(P5seq);
jP5 := j(P5)[1];
assert jP5 eq 287496;
D :=  CMdisc(jP5);
assert D eq -16;

P6seq := [-1/2, -1/2, 0, T/2, -T/2, 0, 1];
P6 := X(K) ! P6seq;
P6c := X(K) ! conj(P6seq);
jP6 := j(P6)[1];
assert jP6 eq 287496;
D :=  CMdisc(jP6);
assert D eq -16;

assert w85(P5) eq P5c;
assert w5(P5) eq P6c;
assert w17(P5) eq P6;
assert w5(P6) eq P5c;
assert w85(P6) eq P6c;
assert w17(P5c) eq P6c;

print "P1 coordinates:", P1, "where T^2 =", dd(P1), "and j-invariant =", jP1, "and CM by", CMdisc(jP1);
print "P2 coordinates:", P2, "where T^2 =", dd(P2), "and j-invariant =", jP2, "and CM by", CMdisc(jP2);
print "P3 coordinates:", P3, "where T^2 =", dd(P3), "and j-invariant =", jP3, "and CM by", CMdisc(jP3);
print "P4 coordinates:", P4, "where T^2 =", dd(P4), "and j-invariant =", jP4, "and CM by", CMdisc(jP4);
print "P5 coordinates:", P5, "where T^2 =", dd(P5), "and j-invariant =", jP5, "and CM by", CMdisc(jP5);
print "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

////////////////
//// N = 86 ////
////////////////

N := 86;
print "N =", N;
X, ws := eqs_quos(N,[]);
al_inds := [m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
print "Model:";
X;
for i in [1..#al_inds] do
    m := al_inds[i];
    print "w_",m, "is given by", DefiningEquations(ws[i]);
end for;
w2 := ws[1];
w43 := ws[2];
w86 := ws[3];
j := jmap(X,N);

///////////

K<T> := QuadraticField(-7);

P1seq := [T, -1, 0, -1, 1, T, -T, T, -1, 1];
P1 := X(K) ! P1seq;
P1c := X(K) ! conj(P1seq);
jP1 := j(P1)[1];
assert jP1 eq -3375;
D :=  CMdisc(jP1);
assert D eq -7;

P2seq := [T, 1, 0, 1, -1, -T, T, -T, -1, 1];
P2 := X(K) ! P2seq;
P2c := X(K) ! conj(P2seq);
jP2 := j(P2)[1];
assert jP2 eq 16581375;
D :=  CMdisc(jP2);
assert D eq -28;

assert w43(P1) eq P1c;
assert w2(P1) eq P2c;
assert w86(P1) eq P2;
assert w2(P2) eq P1c;
assert w43(P2) eq P2c;
assert w86(P1c) eq P2c;

///////////

K<T> := QuadraticField(-3);

P3seq := [T, 0, 1/2, 1/2, 0, 0, -T/2, T/2, 1, 0];
P3 := X(K) ! P3seq;
P3c := X(K) ! conj(P3seq);
jP3 := j(P3)[1];
assert jP3 eq 54000;
D :=  CMdisc(jP3);
assert D eq -12;

P4seq := [T, 0, -1/2, -1/2, 0, 0, T/2, -T/2, 1, 0];
P4 := X(K) ! P4seq;
P4c := X(K) ! conj(P4seq);
jP4 := j(P4)[1];
assert jP4 eq 0;
D :=  CMdisc(jP4);
assert D eq -3;

assert w43(P3) eq P3c;
assert w2(P3) eq P4c;
assert w86(P3) eq P4;
assert w2(P4) eq P3c;
assert w43(P4) eq P4c;
assert w86(P3c) eq P4c;

///////////

K<T> := QuadraticField(-2);

P5seq := [0, 0, 0, 0, 0, 0, T/2, 0, 2, 1];
P5 := X(K) ! P5seq;
P5c := X(K) ! conj(P5seq);
jP5 := j(P5)[1];
assert jP5 eq 8000;
D :=  CMdisc(jP5);
assert D eq -8;

assert w2(P5) eq P5;
assert w2(P5c) eq P5c;
assert w43(P5) eq P5c;
assert w86(P5) eq P5c;

///////////

K<T> := QuadraticField(-7);

P6seq := [T, -1, 0, 1, 1, -1, 1, 1, T, T];
P6 := X(K) ! P6seq;
P6c := X(K) ! conj(P6seq);
jP6 := j(P6)[1];
assert jP6 eq -3375;
D :=  CMdisc(jP6);
assert D eq -7;

P7seq := [T, 1, 0, -1, -1, -1, 1, 1, -T, -T];
P7 := X(K) ! P7seq;
P7c := X(K) ! conj(P7seq);
jP7 := j(P7)[1];
assert jP7 eq -3375;
D :=  CMdisc(jP7);
assert D eq -7;

assert w86(P6) eq P6c;
assert w2(P6) eq P7c;
assert w43(P6) eq P7;
assert w2(P7) eq P6c;
assert w86(P7) eq P7c;
assert w43(P6c) eq P7c;

///////////

P8seq := [T, 1, 0, -1, -1, 1, -1, -1, T, T];
P8 := X(K) ! P8seq;
P8c := X(K) ! conj(P8seq);
jP8 := j(P8)[1];
assert jP8 eq -3375;
D :=  CMdisc(jP8);
assert D eq -7;

P9seq := [T, -1, 0, 1, 1, 1, -1, -1, -T, -T];
P9 := X(K) ! P9seq;
P9c := X(K) ! conj(P9seq);
jP9 := j(P7)[1];
assert jP9 eq -3375;
D :=  CMdisc(jP9);
assert D eq -7;

assert w86(P8) eq P8c;
assert w2(P8) eq P9c;
assert w43(P8) eq P9;
assert w2(P9) eq P8c;
assert w86(P9) eq P9c;
assert w43(P8c) eq P9c;

print "P1 coordinates:", P1, "where T^2 =", dd(P1), "and j-invariant =", jP1, "and CM by", CMdisc(jP1);
print "P2 coordinates:", P2, "where T^2 =", dd(P2), "and j-invariant =", jP2, "and CM by", CMdisc(jP2);
print "P3 coordinates:", P3, "where T^2 =", dd(P3), "and j-invariant =", jP3, "and CM by", CMdisc(jP3);
print "P4 coordinates:", P4, "where T^2 =", dd(P4), "and j-invariant =", jP4, "and CM by", CMdisc(jP4);
print "P5 coordinates:", P5, "where T^2 =", dd(P5), "and j-invariant =", jP5, "and CM by", CMdisc(jP5);
print "P6 coordinates:", P6, "where T^2 =", dd(P6), "and j-invariant =", jP6, "and CM by", CMdisc(jP6);
print "P7 coordinates:", P7, "where T^2 =", dd(P7), "and j-invariant =", jP7, "and CM by", CMdisc(jP7);
print "P8 coordinates:", P8, "where T^2 =", dd(P8), "and j-invariant =", jP8, "and CM by", CMdisc(jP8);
print "P9 coordinates:", P9, "where T^2 =", dd(P9), "and j-invariant =", jP9, "and CM by", CMdisc(jP9);
print "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/////////////////
//// N = 97 ////
/////////////////

N := 97;
print "N =", N;
X, ws := eqs_quos(N,[]);
al_inds := [m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
print "Model:";
X;
for i in [1..#al_inds] do
    m := al_inds[i];
    print "w_",m, "is given by", DefiningEquations(ws[i]);
end for;
w97 := ws[1];
j := jmap(X,N);

///////////

K<T> := QuadraticField(-3);

P1seq := [T , 0 , T , -1 , 0 , 1 , 0];
P1 := X(K) ! P1seq;
P1c := X(K) ! conj(P1seq);
jP1 := j(P1)[1];
assert jP1 eq 54000;
D :=  CMdisc(jP1);
assert D eq -12;

assert w97(P1) eq P1c;

///////////

K<T> := QuadraticField(-163);

P2seq := [12*T/5 , T , 2*T/5 , 37/5 , 11 , 13/5 , 1];
P2 := X(K) ! P2seq;
P2c := X(K) ! conj(P2seq);
jP2 := j(P2)[1];
assert jP2 eq -262537412640768000;
D :=  CMdisc(jP2);
assert D eq -163;

assert w97(P2) eq P2c;

///////////

K<T> := QuadraticField(-1);

P3seq := [4*T , 4*T , 4*T , 1 , 0 , 1 , 1];
P3 := X(K) ! P3seq;
P3c := X(K) ! conj(P3seq);
jP3 := j(P3)[1];
assert jP3 eq 1728;
D :=  CMdisc(jP3);
assert D eq -4;

assert w97(P3) eq P3c;

///////////

K<T> := QuadraticField(-2);

P4seq := [4*T , 2*T , 2*T , 1 , 0 , -1 , 1];
P4 := X(K) ! P4seq;
P4c := X(K) ! conj(P4seq);
jP4 := j(P4)[1];
assert jP4 eq 8000;
D :=  CMdisc(jP4);
assert D eq -8;

assert w97(P4) eq P4c;

///////////

K<T> := QuadraticField(-43);

P5seq := [0 , T , 0 , -3 , -1 , 3 , 1];
P5 := X(K) ! P5seq;
P5c := X(K) ! conj(P5seq);
jP5 := j(P5)[1];
assert jP5 eq -884736000;
D :=  CMdisc(jP5);
assert D eq -43;

assert w97(P5) eq P5c;

///////////

K<T> := QuadraticField(-11);

P6seq := [T , T , 0 , -2 , 1 , 1 , 1];
P6 := X(K) ! P6seq;
P6c := X(K) ! conj(P6seq);
jP6 := j(P6)[1];
assert jP6 eq -32768;
D :=  CMdisc(jP6);
assert D eq -11;

assert w97(P6) eq P6c;

///////////

K<T> := QuadraticField(-3);

P7seq := [3*T/2 , 3*T , 3*T/2 , 1/2 , -1 , 3/2 , 1];
P7 := X(K) ! P7seq;
P7c := X(K) ! conj(P7seq);
jP7 := j(P7)[1];
assert jP7 eq 0;
D :=  CMdisc(jP7);
assert D eq -3;

assert w97(P7) eq P7c;

///////////

K<T> := QuadraticField(-1);

P8seq := [6*T , 2*T , 2*T , -1 , 2 , -1 , 1];
P8 := X(K) ! P8seq;
P8c := X(K) ! conj(P8seq);
jP8 := j(P8)[1];
assert jP8 eq 287496;
D :=  CMdisc(jP8);
assert D eq -16;

assert w97(P8) eq P8c;

///////////

K<T> := QuadraticField(-3);

P9seq := [4*T , 2*T , T , -1 , 2 , 0 , 1];
P9 := X(K) ! P9seq;
P9c := X(K) ! conj(P9seq);
jP9 := j(P9)[1];
assert jP9 eq -12288000;
D :=  CMdisc(jP9);
assert D eq -27;

assert w97(P9) eq P9c;

print "P1 coordinates:", P1, "where T^2 =", dd(P1), "and j-invariant =", jP1, "and CM by", CMdisc(jP1);
print "P2 coordinates:", P2, "where T^2 =", dd(P2), "and j-invariant =", jP2, "and CM by", CMdisc(jP2);
print "P3 coordinates:", P3, "where T^2 =", dd(P3), "and j-invariant =", jP3, "and CM by", CMdisc(jP3);
print "P4 coordinates:", P4, "where T^2 =", dd(P4), "and j-invariant =", jP4, "and CM by", CMdisc(jP4);
print "P5 coordinates:", P5, "where T^2 =", dd(P5), "and j-invariant =", jP5, "and CM by", CMdisc(jP5);
print "P6 coordinates:", P6, "where T^2 =", dd(P6), "and j-invariant =", jP6, "and CM by", CMdisc(jP6);
print "P7 coordinates:", P7, "where T^2 =", dd(P7), "and j-invariant =", jP7, "and CM by", CMdisc(jP7);
print "P8 coordinates:", P8, "where T^2 =", dd(P8), "and j-invariant =", jP8, "and CM by", CMdisc(jP8);
print "P9 coordinates:", P9, "where T^2 =", dd(P9), "and j-invariant =", jP9, "and CM by", CMdisc(jP9);
print "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

////////////////
//// N = 98 ////
////////////////

N := 98;
print "N =", N;
X, ws := eqs_quos(N,[]);
al_inds := [m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
print "Model:";
X;
for i in [1..#al_inds] do
    m := al_inds[i];
    print "w_",m, "is given by", DefiningEquations(ws[i]);
end for;
w2 := ws[1];
w49 := ws[2];
w98 := ws[3];
j := jmap(X,N);

///////////

K<T> := QuadraticField(-3);

P1seq := [-T , 1 , 0 , -1/2 , 0 , T/2 , 1];
P1 := X(K) ! P1seq;
P1c := X(K) ! conj(P1seq);
jP1 := j(P1)[1];
assert jP1 eq 54000;
D :=  CMdisc(jP1);
assert D eq -12;

P2seq := [T , -1 , 0 , 1/2 , 0 , T/2 , 1];
P2 := X(K) ! P2seq;
P2c := X(K) ! conj(P2seq);
jP2 := j(P2)[1];
assert jP2 eq 0;
D :=  CMdisc(jP2);
assert D eq -3;

assert w98(P1) eq P2c;
assert w2(P1) eq P2;
assert w49(P1) eq P1c;
assert w98(P2) eq P1c;
assert w49(P2) eq P2c;
assert w2(P1c) eq P2c;

print "P1 coordinates:", P1, "where T^2 =", dd(P1), "and j-invariant =", jP1, "and CM by", CMdisc(jP1);
print "P2 coordinates:", P2, "where T^2 =", dd(P2), "and j-invariant =", jP2, "and CM by", CMdisc(jP2);
print "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

////////////////
//// N = 100 ////
////////////////

N := 100;
print "N =", N;
X, ws := eqs_quos(N,[]);
al_inds := [m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
print "Model:";
X;
for i in [1..#al_inds] do
    m := al_inds[i];
    print "w_",m, "is given by", DefiningEquations(ws[i]);
end for;
w4 := ws[1];
w25 := ws[2];
w100 := ws[3];
j := jmap(X,N);

///////////

K<T> := QuadraticField(-1);

P1seq := [-T , 1 , 0 , T/2 , T/2 , 2 , 1];
P1 := X(K) ! P1seq;
P1c := X(K) ! conj(P1seq);
jP1 := j(P1)[1];
assert jP1 eq 1728;
D :=  CMdisc(jP1);
assert D eq -4;

P2seq := [-T , -1 , 0 , -T/2 , -T/2 , 2,1];
P2 := X(K) ! P2seq;
P2c := X(K) ! conj(P2seq);
jP2 := j(P2)[1];
assert jP2 eq 287496;
D :=  CMdisc(jP2);
assert D eq -16;

assert w25(P1) eq P1c;
assert w100(P1) eq P2;
assert w4(P1) eq P2c;
assert w25(P2) eq P2c;
assert w4(P2) eq P1c;
assert w100(P1c) eq P2c;

P3seq := [0 , 0 , 0 , T/4 , -T/4 , 1 , 0];
P3 := X(K) ! P3seq;
P3c := X(K) ! conj(P3seq);
jP3 := j(P3)[1];
assert jP3 eq 287496;
D :=  CMdisc(jP3);
assert D eq -16;

assert w100(P3) eq P3c;
assert w25(P3) eq P3c;
assert w4(P3) eq P3;

print "P1 coordinates:", P1, "where T^2 =", dd(P1), "and j-invariant =", jP1, "and CM by", CMdisc(jP1);
print "P2 coordinates:", P2, "where T^2 =", dd(P2), "and j-invariant =", jP2, "and CM by", CMdisc(jP2);
print "P3 coordinates:", P3, "where T^2 =", dd(P3), "and j-invariant =", jP3, "and CM by", CMdisc(jP3);
print "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/////////////////
//// N = 103 ////
/////////////////

N := 103;
print "N =", N;
X, ws := eqs_quos(N,[]);
al_inds := [m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
print "Model:";
X;
for i in [1..#al_inds] do
    m := al_inds[i];
    print "w_",m, "is given by", DefiningEquations(ws[i]);
end for;
w103 := ws[1];
j := jmap(X,N);

///////////

K<T> := QuadraticField(-3);

P1seq := [T, T, -2, 1, 2, 1, 1, 1];
P1 := X(K) ! P1seq;
P1c := X(K) ! conj(P1seq);
jP1 := j(P1)[1];
assert jP1 eq 54000;
D :=  CMdisc(jP1);
assert D eq -12;

P2seq := [0, T, -2, 1, 0, 1, 1, 0];
P2 := X(K) ! P2seq;
P2c := X(K) ! conj(P2seq);
jP2 := j(P2)[1];
assert jP2 eq -12288000;
D :=  CMdisc(jP2);
assert D eq -27;

P3seq := [3*T, T, -4/3, -1/3, 2, -1/3, 5/3, 1];
P3 := X(K) ! P3seq;
P3c := X(K) ! conj(P3seq);
jP3 := j(P3)[1];
assert jP3 eq 0;
D :=  CMdisc(jP3);
assert D eq -3;

assert w103(P1) eq P1c;
assert w103(P2) eq P2c;
assert w103(P3) eq P3c;

///////////

K<T> := QuadraticField(-11);

P4seq := [T, T, 1, 0, 0, -1, 0, 1];
P4 := X(K) ! P4seq;
P4c := X(K) ! conj(P4seq);
jP4 := j(P4)[1];
assert jP4 eq -32768;
D :=  CMdisc(jP4);
assert D eq -11;

assert w103(P4) eq P4c;

///////////

K<T> := QuadraticField(-67);

P5seq := [T, 0, 3, -4, 5, -1, 3, 1];
P5 := X(K) ! P5seq;
P5c := X(K) ! conj(P5seq);
jP5 := j(P5)[1];
assert jP5 eq -147197952000;
D :=  CMdisc(jP5);
assert D eq -67;

assert w103(P5) eq P5c;

///////////

K<T> := QuadraticField(2885);

P6seq := [3*T, T, 461, 196, 78, 25, 8, 1];
P6 := X(K) ! P6seq;
P6c := X(K) ! conj(P6seq);
jP6 := j(P6)[1];
assert jP6 eq -669908635472124980731701532753920*T + 35982263935929364331785036841779200;
tf := HasComplexMultiplication(EllipticCurveWithjInvariant(jP6));
assert tf eq false;

assert w103(P6) eq P6c;

print "P1 coordinates:", P1, "where T^2 =", dd(P1), "and j-invariant =", jP1, "and CM by", CMdisc(jP1);
print "P2 coordinates:", P2, "where T^2 =", dd(P2), "and j-invariant =", jP2, "and CM by", CMdisc(jP2);
print "P3 coordinates:", P3, "where T^2 =", dd(P3), "and j-invariant =", jP3, "and CM by", CMdisc(jP3);
print "P4 coordinates:", P4, "where T^2 =", dd(P4), "and j-invariant =", jP4, "and CM by", CMdisc(jP4);
print "P5 coordinates:", P5, "where T^2 =", dd(P5), "and j-invariant =", jP5, "and CM by", CMdisc(jP5);
print "P6 coordinates:", P6, "where T^2 =", dd(P6), "and j-invariant =", jP6, "and no CM";
print "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/////////////////
//// N = 107 ////
/////////////////

N := 107;
print "N =", N;
X, ws := eqs_quos(N,[]);
al_inds := [m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
print "Model:";
X;
for i in [1..#al_inds] do
    m := al_inds[i];
    print "w_",m, "is given by", DefiningEquations(ws[i]);
end for;
w107 := ws[1];
j := jmap(X,N);

///////////

K<T> := QuadraticField(-7);

P1seq := [0 , -T , 0 , 0 , 0 , 0 , 0 , 0 , 1];
P1 := X(K) ! P1seq;
P1c := X(K) ! conj(P1seq);
jP1 := j(P1)[1];
assert jP1 eq -3375;
D :=  CMdisc(jP1);
assert D eq -7;

P2seq := [-2*T , -T , -4 , 2 , 4 , 4 , 2 , 2, 1];
P2 := X(K) ! P2seq;
P2c := X(K) ! conj(P2seq);
jP2 := j(P2)[1];
assert jP2 eq 16581375;
D :=  CMdisc(jP2);
assert D eq -28;

assert w107(P1) eq P1c;
assert w107(P2) eq P2c;

///////////

K<T> := QuadraticField(-2);

P3seq := [-2*T , 0 , -2 , 1 , 1 , 1 , 1 , 1 , 1];
P3 := X(K) ! P3seq;
P3c := X(K) ! conj(P3seq);
jP3 := j(P3)[1];
assert jP3 eq 8000;
D :=  CMdisc(jP3);
assert D eq -8;

assert w107(P3) eq P3c;

///////////

K<T> := QuadraticField(-43);

P4seq := [0 , -T , 3 , -2 , 1 , -2 , 0 , -1 , 1];
P4 := X(K) ! P4seq;
P4c := X(K) ! conj(P4seq);
jP4 := j(P4)[1];
assert jP4 eq -884736000;
D :=  CMdisc(jP4);
assert D eq -43;

assert w107(P4) eq P4c;

///////////

K<T> := QuadraticField(-67);

P5seq := [-2*T , -T , -5 , 6 , 9 , 8 , 4 , 3 , 1];
P5 := X(K) ! P5seq;
P5c := X(K) ! conj(P5seq);
jP5 := j(P5)[1];
assert jP5 eq -147197952000;
D :=  CMdisc(jP5);
assert D eq -67;

assert w107(P5) eq P5c;

print "P1 coordinates:", P1, "where T^2 =", dd(P1), "and j-invariant =", jP1, "and CM by", CMdisc(jP1);
print "P2 coordinates:", P2, "where T^2 =", dd(P2), "and j-invariant =", jP2, "and CM by", CMdisc(jP2);
print "P3 coordinates:", P3, "where T^2 =", dd(P3), "and j-invariant =", jP3, "and CM by", CMdisc(jP3);
print "P4 coordinates:", P4, "where T^2 =", dd(P4), "and j-invariant =", jP4, "and CM by", CMdisc(jP4);
print "P5 coordinates:", P5, "where T^2 =", dd(P5), "and j-invariant =", jP5, "and CM by", CMdisc(jP5);
print "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/////////////////
//// N = 109 ////
/////////////////

N := 109;
print "N =", N;
X, ws := eqs_quos(N,[]);
al_inds := [m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
print "Model:";
X;
for i in [1..#al_inds] do
    m := al_inds[i];
    print "w_",m, "is given by", DefiningEquations(ws[i]);
end for;
w109 := ws[1];
j := jmap(X,N);

///////////

K<T> := QuadraticField(-43);

P1seq := [-T , -1/2*T , -1/2*T , -1 , 3/2 , -1 , 1/2 , 1];
P1 := X(K) ! P1seq;
P1c := X(K) ! conj(P1seq);
jP1 := j(P1)[1];
assert jP1 eq -884736000;
D :=  CMdisc(jP1);
assert D eq -43;

assert w109(P1) eq P1c;

///////////

K<T> := QuadraticField(-3);

P2seq := [-T , -T , 0 , -1 , 0 , 1 , 0 , 0];
P2 := X(K) ! P2seq;
P2c := X(K) ! conj(P2seq);
jP2 := j(P2)[1];
assert jP2 eq 54000;
D :=  CMdisc(jP2);
assert D eq -12;

assert w109(P2) eq P2c;

///////////

K<T> := QuadraticField(-1);

P3seq := [0 , 0 , -4*T , 2 , -1 , -2 , 2 , 1];
P3 := X(K) ! P3seq;
P3c := X(K) ! conj(P3seq);
jP3 := j(P3)[1];
assert jP3 eq 1728;
D :=  CMdisc(jP3);
assert D eq -4;

assert w109(P3) eq P3c;

///////////

K<T> := QuadraticField(-7);

P4seq := [-1/2*T , -3/2*T , -1/2*T , -1/2 , -1/2 , 1 , -1/2 , 1];
P4 := X(K) ! P4seq;
P4c := X(K) ! conj(P4seq);
jP4 := j(P4)[1];
assert jP4 eq 16581375;
D :=  CMdisc(jP4);
assert D eq -28;

assert w109(P4) eq P4c;

///////////

K<T> := QuadraticField(-3);

P5seq := [0 , -T , -T , 0 , -1 , 0 , 1 , 0];
P5 := X(K) ! P5seq;
P5c := X(K) ! conj(P5seq);
jP5 := j(P5)[1];
assert jP5 eq -12288000;
D :=  CMdisc(jP5);
assert D eq -27;

assert w109(P5) eq P5c;

///////////

K<T> := QuadraticField(-7);

P6seq := [-T , -T , -T , 1 , -1 , 0 , 1 , 0];
P6 := X(K) ! P6seq;
P6c := X(K) ! conj(P6seq);
jP6 := j(P6)[1];
assert jP6 eq -3375;
D :=  CMdisc(jP6);
assert D eq -7;

assert w109(P6) eq P6c;

///////////

K<T> := QuadraticField(-3);

P7seq := [-3/2*T , -5/2*T , -T , -3/2 , 1/3 , 1/2 , -1/3 , 1];
P7 := X(K) ! P7seq;
P7c := X(K) ! conj(P7seq);
jP7 := j(P7)[1];
assert jP7 eq 0;
D :=  CMdisc(jP7);
assert D eq -3;

assert w109(P7) eq P7c;

///////////

K<T> := QuadraticField(-1);

P8seq := [-4*T , -4*T , -2*T , -2 , 1 , 0 , 0 , 1];
P8 := X(K) ! P8seq;
P8c := X(K) ! conj(P8seq);
jP8 := j(P8)[1];
assert jP8 eq 287496;
D :=  CMdisc(jP8);
assert D eq -16;

assert w109(P8) eq P8c;

print "P1 coordinates:", P1, "where T^2 =", dd(P1), "and j-invariant =", jP1, "and CM by", CMdisc(jP1);
print "P2 coordinates:", P2, "where T^2 =", dd(P2), "and j-invariant =", jP2, "and CM by", CMdisc(jP2);
print "P3 coordinates:", P3, "where T^2 =", dd(P3), "and j-invariant =", jP3, "and CM by", CMdisc(jP3);
print "P4 coordinates:", P4, "where T^2 =", dd(P4), "and j-invariant =", jP4, "and CM by", CMdisc(jP4);
print "P5 coordinates:", P5, "where T^2 =", dd(P5), "and j-invariant =", jP5, "and CM by", CMdisc(jP5);
print "P6 coordinates:", P6, "where T^2 =", dd(P6), "and j-invariant =", jP6, "and CM by", CMdisc(jP6);
print "P7 coordinates:", P7, "where T^2 =", dd(P7), "and j-invariant =", jP7, "and CM by", CMdisc(jP7);
print "P8 coordinates:", P8, "where T^2 =", dd(P8), "and j-invariant =", jP8, "and CM by", CMdisc(jP8);
print "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/////////////////
//// N = 113 ////
/////////////////

N := 113;
print "N =", N;
X, ws := eqs_quos(N,[]);
al_inds := [m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
print "Model:";
X;
for i in [1..#al_inds] do
    m := al_inds[i];
    print "w_",m, "is given by", DefiningEquations(ws[i]);
end for;
w113 := ws[1];
j := jmap(X,N);

///////////

K<T> := QuadraticField(-1);

P1seq := [-2*T , 0 , -2*T , -3 , 1 , 1 , 0 , 0 , 1];
P1 := X(K) ! P1seq;
P1c := X(K) ! conj(P1seq);
jP1 := j(P1)[1];
assert jP1 eq 287496;
D :=  CMdisc(jP1);
assert D eq -16;

P2seq := [-12*T , -8*T , -4*T , -7 , 1 , 3 , 4 , 2 , 1];
P2 := X(K) ! P2seq;
P2c := X(K) ! conj(P2seq);
jP2 := j(P2)[1];
assert jP2 eq 1728;
D :=  CMdisc(jP2);
assert D eq -4;

assert w113(P1) eq P1c;
assert w113(P2) eq P2c;

///////////

K<T> := QuadraticField(-7);

P3seq := [-2*T , -T , -2*T , -2 , 2 , 0 , -1 , 0 , 1];
P3 := X(K) ! P3seq;
P3c := X(K) ! conj(P3seq);
jP3 := j(P3)[1];
assert jP3 eq 16581375;
D :=  CMdisc(jP3);
assert D eq -28;

P4seq := [0 , -T , 0 , -2 , 0 , 0 , 1 , 0 , 1];
P4 := X(K) ! P4seq;
P4c := X(K) ! conj(P4seq);
jP4 := j(P4)[1];
assert jP4 eq -3375;
D :=  CMdisc(jP4);
assert D eq -7;

assert w113(P3) eq P3c;
assert w113(P4) eq P4c;

///////////

K<T> := QuadraticField(-11);

P5seq := [-T , -T , 0 , -1 , 1 , 1 , 1 , 1 , 0];
P5 := X(K) ! P5seq;
P5c := X(K) ! conj(P5seq);
jP5 := j(P5)[1];
assert jP5 eq -32768;
D :=  CMdisc(jP5);
assert D eq -11;

assert w113(P5) eq P5c;

///////////

K<T> := QuadraticField(-163);

P6seq := [-6*T , -3*T , -T , 21/2 , 22 , 35/2 , 23/2 , 5 , 1];
P6 := X(K) ! P6seq;
P6c := X(K) ! conj(P6seq);
jP6 := j(P6)[1];
assert jP6 eq -262537412640768000;
D :=  CMdisc(jP6);
assert D eq -163;

assert w113(P6) eq P6c;

///////////

K<T> := QuadraticField(-2);

P7seq := [-4*T , -2*T , -2*T , -1 , 0 , 1 , 1 , 0 , 0];
P7 := X(K) ! P7seq;
P7c := X(K) ! conj(P7seq);
jP7 := j(P7)[1];
assert jP7 eq 8000;
D :=  CMdisc(jP7);
assert D eq -8;

assert w113(P7) eq P7c;

print "P1 coordinates:", P1, "where T^2 =", dd(P1), "and j-invariant =", jP1, "and CM by", CMdisc(jP1);
print "P2 coordinates:", P2, "where T^2 =", dd(P2), "and j-invariant =", jP2, "and CM by", CMdisc(jP2);
print "P3 coordinates:", P3, "where T^2 =", dd(P3), "and j-invariant =", jP3, "and CM by", CMdisc(jP3);
print "P4 coordinates:", P4, "where T^2 =", dd(P4), "and j-invariant =", jP4, "and CM by", CMdisc(jP4);
print "P5 coordinates:", P5, "where T^2 =", dd(P5), "and j-invariant =", jP5, "and CM by", CMdisc(jP5);
print "P6 coordinates:", P6, "where T^2 =", dd(P6), "and j-invariant =", jP6, "and CM by", CMdisc(jP6);
print "P7 coordinates:", P7, "where T^2 =", dd(P7), "and j-invariant =", jP7, "and CM by", CMdisc(jP7);
print "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/////////////////
//// N = 121 ////
/////////////////

N := 121;
print "N =", N;
X, ws := eqs_quos(N,[]);
al_inds := [m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
print "Model:";
X;
for i in [1..#al_inds] do
    m := al_inds[i];
    print "w_",m, "is given by", DefiningEquations(ws[i]);
end for;
w121 := ws[1];
j := jmap(X,N);

///////////

K<T> := QuadraticField(-19);

P1seq := [T, T, 2, 0, -1, 1];
P1 := X(K) ! P1seq;
P1c := X(K) ! conj(P1seq);
jP1 := j(P1)[1];
assert jP1 eq -884736;
D :=  CMdisc(jP1);
assert D eq -19;

assert w121(P1) eq P1c;

///////////

K<T> := QuadraticField(-43);

P2seq := [T, T, 3, 2, 0, 1];
P2 := X(K) ! P2seq;
P2c := X(K) ! conj(P2seq);
jP2 := j(P2)[1];
assert jP2 eq -884736000;
D :=  CMdisc(jP2);
assert D eq -43;

assert w121(P2) eq P2c;

///////////

K<T> := QuadraticField(-2);

P3seq := [2*T, 0, 1, -1, -1, 1];
P3 := X(K) ! P3seq;
P3c := X(K) ! conj(P3seq);
jP3 := j(P3)[1];
assert jP3 eq 8000;
D :=  CMdisc(jP3);
assert D eq -8;

assert w121(P3) eq P3c;

///////////

K<T> := QuadraticField(-7);

P4seq := [0, T, 1, 0, -1, 1];
P4 := X(K) ! P4seq;
P4c := X(K) ! conj(P4seq);
jP4 := j(P4)[1];
assert jP4 eq -3375;
D :=  CMdisc(jP4);
assert D eq -7;

assert w121(P4) eq P4c;

print "P1 coordinates:", P1, "where T^2 =", dd(P1), "and j-invariant =", jP1, "and CM by", CMdisc(jP1);
print "P2 coordinates:", P2, "where T^2 =", dd(P2), "and j-invariant =", jP2, "and CM by", CMdisc(jP2);
print "P3 coordinates:", P3, "where T^2 =", dd(P3), "and j-invariant =", jP3, "and CM by", CMdisc(jP3);
print "P4 coordinates:", P4, "where T^2 =", dd(P4), "and j-invariant =", jP4, "and CM by", CMdisc(jP4);
print "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/////////////////
//// N = 127 ////
/////////////////

N := 127;
print "N =", N;
X, ws := eqs_quos(N,[]);
al_inds := [m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
print "Model:";
X;
for i in [1..#al_inds] do
    m := al_inds[i];
    print "w_",m, "is given by", DefiningEquations(ws[i]);
end for;
w127 := ws[1];
j := jmap(X,N);

///////////

K<T> := QuadraticField(-67);

P1seq := [-4*T , -2*T , -T , -11 , 4 , 10 , 8 , 8 , 4 , 1];
P1 := X(K) ! P1seq;
P1c := X(K) ! conj(P1seq);
jP1 := j(P1)[1];
assert jP1 eq -147197952000;
D :=  CMdisc(jP1);
assert D eq -67;

assert w127(P1) eq P1c;

///////////

K<T> := QuadraticField(-3);

P2seq := [-T , -T , 0 , -2 , 0 , 1 , 1 , 1 , 1 , 0];
P2 := X(K) ! P2seq;
P2c := X(K) ! conj(P2seq);
jP2 := j(P2)[1];
assert jP2 eq 54000;
D :=  CMdisc(jP2);
assert D eq -12;

P3seq := [-T , 0 , -T , -3 , 1 , 1 , 1 , 1 , 1 , 1];
P3 := X(K) ! P3seq;
P3c := X(K) ! conj(P3seq);
jP3 := j(P3)[1];
assert jP3 eq -12288000;
D :=  CMdisc(jP3);
assert D eq -27;

assert w127(P2) eq P2c;
assert w127(P3) eq P3c;

///////////

K<T> := QuadraticField(-7);

P4seq := [0 , -T/2 , -T/2 , -3 , 2 , 1/2 , -1/2 , 3/2 , 0 , 1];
P4 := X(K) ! P4seq;
P4c := X(K) ! conj(P4seq);
jP4 := j(P4)[1];
assert jP4 eq 16581375;
D :=  CMdisc(jP4);
assert D eq -28;

P5seq := [-2*T , -T , -T , -2 , 0 , 1 , 1 , 1 , 0 , 0];
P5 := X(K) ! P5seq;
P5c := X(K) ! conj(P5seq);
jP5 := j(P5)[1];
assert jP5 eq -3375;
D :=  CMdisc(jP5);
assert D eq -7;

assert w127(P4) eq P4c;
assert w127(P5) eq P5c;

///////////

K<T> := QuadraticField(-3);

P6seq := [-15*T/2 , -9*T/2 , -3*T , -3 , -2 , -1/2 , -1/2, 5/2 , 5/2 , 1];
P6 := X(K) ! P6seq;
P6c := X(K) ! conj(P6seq);
jP6 := j(P6)[1];
assert jP6 eq 0;
D :=  CMdisc(jP6);
assert D eq -3;

assert w127(P6) eq P6c;

///////////

K<T> := QuadraticField(-43);

P7seq := [0 , -T , 0 , 3 , 1 , -2 , -1 , 0 , -2 , 1];
P7 := X(K) ! P7seq;
P7c := X(K) ! conj(P7seq);
jP7 := j(P7)[1];
assert jP7 eq -884736000;
D :=  CMdisc(jP7);
assert D eq -43;

assert w127(P7) eq P7c;

print "P1 coordinates:", P1, "where T^2 =", dd(P1), "and j-invariant =", jP1, "and CM by", CMdisc(jP1);
print "P2 coordinates:", P2, "where T^2 =", dd(P2), "and j-invariant =", jP2, "and CM by", CMdisc(jP2);
print "P3 coordinates:", P3, "where T^2 =", dd(P3), "and j-invariant =", jP3, "and CM by", CMdisc(jP3);
print "P4 coordinates:", P4, "where T^2 =", dd(P4), "and j-invariant =", jP4, "and CM by", CMdisc(jP4);
print "P5 coordinates:", P5, "where T^2 =", dd(P5), "and j-invariant =", jP5, "and CM by", CMdisc(jP5);
print "P6 coordinates:", P6, "where T^2 =", dd(P6), "and j-invariant =", jP6, "and CM by", CMdisc(jP6);
print "P7 coordinates:", P7, "where T^2 =", dd(P7), "and j-invariant =", jP7, "and CM by", CMdisc(jP7);
print "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";
