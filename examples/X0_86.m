_<x> := PolynomialRing(Rationals());

 K7<r7> := NumberField(x^2+1/7);

 seqP1 := [-1, r7,0, -r7, -r7, -r7, r7, r7, 1, 1];
 seqP1conj := [-1, -r7,0, r7, r7, r7, -r7, -r7, 1, 1];
 seqP2 := [1, -r7,0, r7, r7, -r7, r7, r7, 1, 1];
 seqP2conj := [1, r7, 0, -r7, -r7, r7, -r7, -r7, 1, 1];

 tup1 := <K7, [-1, r7,0, -r7, -r7, -r7, r7, r7, 1, 1]>;
 tup2 := <K7, [-1, -r7,0, r7, r7, r7, -r7, -r7, 1, 1]>;
 tup3 := <K7, [1, -r7,0, r7, r7, -r7, r7, r7, 1, 1]>;
 tup4 := <K7, [1, r7, 0, -r7, -r7, r7, -r7, -r7, 1, 1]>;


 nonpbs := [tup1, tup3]; //, tup5, tup6, tup7, tup8;

 load "main.m";
 ProvablyComputeQuadPts_X0N(86 : d:=43, nonpullbacks:=nonpbs, badPrimes:={7});