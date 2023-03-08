// In this file we verify all the data contained in the Tables of the paper
// We also print the models, and the output can be found in the file verifications.out in the Output_files folder

load "models_and_maps.m";

// auxiliary function to compute the conjugate of a sequence of elements in a quadratic field

conj := function(PPseq);
    return [Conjugate(cc) : cc in PPseq];
end function;

////////////////////////////////////////////

////////////////
//// N = 74 ////
////////////////

N := 74;
X, ws := eqs_quos(N,[]);
X, ws;
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
tf, D := HasComplexMultiplication(EllipticCurveWithjInvariant(jP1));
assert tf and D eq -7;

P2seq := [1, 0, 0, 1/T, -2/T, 2/T, -1/T, 1];
P2 := X(K) ! P2seq;
P2c := X(K) ! conj(P2seq);
jP2 := j(P2)[1];
assert jP2 eq -3375;
tf, D := HasComplexMultiplication(EllipticCurveWithjInvariant(jP2));
assert tf and D eq -7;

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
tf, D := HasComplexMultiplication(EllipticCurveWithjInvariant(jP3));
assert tf and D eq -7;

P4seq := [T, 2, 2, -1, 0, 0, T, 1];
P4 := X(K) ! P4seq;
P4c := X(K) ! conj(P4seq);
jP4 := j(P4)[1];
assert jP4 eq 16581375;
tf, D := HasComplexMultiplication(EllipticCurveWithjInvariant(jP4));
assert tf and D eq -28;

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
tf, D := HasComplexMultiplication(EllipticCurveWithjInvariant(jP5));
assert tf and D eq -4;

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
tf, D := HasComplexMultiplication(EllipticCurveWithjInvariant(jP6));
assert tf and D eq -4;

P7seq := [-2,T,0,-T,1,0,1,0];
P7 := X(K) ! P7seq;
P7c := X(K) ! conj(P7seq);
jP7 := j(P7)[1];
assert jP7 eq 287496;
tf, D := HasComplexMultiplication(EllipticCurveWithjInvariant(jP7));
assert tf and D eq -16;

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
tf, D := HasComplexMultiplication(EllipticCurveWithjInvariant(jP8));
assert tf and D eq -12;

P9seq := [T,1/2, -1/2, -1/2,-T/2,T/2,-T/2,1];
P9 := X(K) ! P9seq;
P9c := X(K) ! conj(P9seq);
jP9 := j(P9)[1];
assert jP9 eq 0;
tf, D := HasComplexMultiplication(EllipticCurveWithjInvariant(jP9));
assert tf and D eq -3;

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
tf, D := HasComplexMultiplication(EllipticCurveWithjInvariant(jP10));
assert tf and D eq -148;

assert w37(P10) eq P10;
assert w37(P10c) eq P10c;
assert w2(P10) eq P10c;
assert w74(P10) eq P10c;

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

////////////////
//// N = 76 ////
////////////////

N := 76;
X, ws := eqs_quos(N,[]);
X, ws;
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
tf, D := HasComplexMultiplication(EllipticCurveWithjInvariant(jP1));
assert tf and D eq -12;

P2seq := [1 , 0 , 0 , -T/3 , 0 , -T/3 , 2 , 1];
P2 := X(K) ! P2seq;
P2c := X(K) ! conj(P2seq);
jP2 := j(P2)[1];
assert jP2 eq 54000;
tf, D := HasComplexMultiplication(EllipticCurveWithjInvariant(jP2));
assert tf and D eq -12;

assert w76(P1) eq P1c;
assert w4(P1) eq P2;
assert w19(P1) eq P2c;
assert w76(P2) eq P2c;
assert w19(P2) eq P1c;
assert w4(P1c) eq P2c;

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

////////////////
//// N = 80 ////
////////////////

// No noncuspidal quadratic points

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

////////////////
//// N = 86 ////
////////////////

N := 86;
X, ws := eqs_quos(N,[]);
X, ws;
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
tf, D := HasComplexMultiplication(EllipticCurveWithjInvariant(jP1));
assert tf and D eq -7;

P2seq := [T, 1, 0, 1, -1, -T, T, -T, -1, 1];
P2 := X(K) ! P2seq;
P2c := X(K) ! conj(P2seq);
jP2 := j(P2)[1];
assert jP2 eq 16581375;
tf, D := HasComplexMultiplication(EllipticCurveWithjInvariant(jP2));
assert tf and D eq -28;

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
tf, D := HasComplexMultiplication(EllipticCurveWithjInvariant(jP3));
assert tf and D eq -12;

P4seq := [T, 0, -1/2, -1/2, 0, 0, T/2, -T/2, 1, 0];
P4 := X(K) ! P4seq;
P4c := X(K) ! conj(P4seq);
jP4 := j(P4)[1];
assert jP4 eq 0;
tf, D := HasComplexMultiplication(EllipticCurveWithjInvariant(jP4));
assert tf and D eq -3;

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
tf, D := HasComplexMultiplication(EllipticCurveWithjInvariant(jP5));
assert tf and D eq -8;

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
tf, D := HasComplexMultiplication(EllipticCurveWithjInvariant(jP6));
assert tf and D eq -7;

P7seq := [T, 1, 0, -1, -1, -1, 1, 1, -T, -T];
P7 := X(K) ! P7seq;
P7c := X(K) ! conj(P7seq);
jP7 := j(P7)[1];
assert jP7 eq -3375;
tf, D := HasComplexMultiplication(EllipticCurveWithjInvariant(jP7));
assert tf and D eq -7;

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
tf, D := HasComplexMultiplication(EllipticCurveWithjInvariant(jP8));
assert tf and D eq -7;

P9seq := [T, -1, 0, 1, 1, 1, -1, -1, -T, -T];
P9 := X(K) ! P9seq;
P9c := X(K) ! conj(P9seq);
jP9 := j(P7)[1];
assert jP9 eq -3375;
tf, D := HasComplexMultiplication(EllipticCurveWithjInvariant(jP9));
assert tf and D eq -7;

assert w86(P8) eq P8c;
assert w2(P8) eq P9c;
assert w43(P8) eq P9;
assert w2(P9) eq P8c;
assert w86(P9) eq P9c;
assert w43(P8c) eq P9c;

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/////////////////
//// N = 103 ////
/////////////////

N := 103;
X, ws := eqs_quos(N,[]);
X, ws;
w103 := ws[1];
j := jmap(X,N);

///////////

K<T> := QuadraticField(-3);

P1seq := [T, T, -2, 1, 2, 1, 1, 1];
P1 := X(K) ! P1seq;
P1c := X(K) ! conj(P1seq);
jP1 := j(P1)[1];
assert jP1 eq 54000;
tf, D := HasComplexMultiplication(EllipticCurveWithjInvariant(jP1));
assert tf and D eq -12;

P2seq := [0, T, -2, 1, 0, 1, 1, 0];
P2 := X(K) ! P2seq;
P2c := X(K) ! conj(P2seq);
jP2 := j(P2)[1];
assert jP2 eq -12288000;
tf, D := HasComplexMultiplication(EllipticCurveWithjInvariant(jP2));
assert tf and D eq -27;

P3seq := [3*T, T, -4/3, -1/3, 2, -1/3, 5/3, 1];
P3 := X(K) ! P3seq;
P3c := X(K) ! conj(P3seq);
jP3 := j(P3)[1];
assert jP3 eq 0;
tf, D := HasComplexMultiplication(EllipticCurveWithjInvariant(jP3));
assert tf and D eq -3;

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
tf, D := HasComplexMultiplication(EllipticCurveWithjInvariant(jP4));
assert tf and D eq -11;

assert w103(P4) eq P4c;

///////////

K<T> := QuadraticField(-67);

P5seq := [T, 0, 3, -4, 5, -1, 3, 1];
P5 := X(K) ! P5seq;
P5c := X(K) ! conj(P5seq);
jP5 := j(P5)[1];
assert jP5 eq -147197952000;
tf, D := HasComplexMultiplication(EllipticCurveWithjInvariant(jP5));
assert tf and D eq -67;

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