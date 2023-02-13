_<x> := PolynomialRing(Rationals());

 K7<r7> := NumberField(x^2+1/7);

 tup1 := <K7, [-1, r7,0, -r7, -r7, -r7, r7, r7, 1, 1]>;
 //tup2 := <K7, [-1, -r7,0, r7, r7, r7, -r7, -r7, 1, 1]>;
 tup3 := <K7, [1, -r7,0, r7, r7, -r7, r7, r7, 1, 1]>;
 //tup4 := <K7, [1, r7, 0, -r7, -r7, r7, -r7, -r7, 1, 1]>;
 //the commented points are conjugates of other two


 nonpbs := [tup1, tup3]; //

 load "main.m";
//7 is not really a bad prime, but it doesn't contribute to sieving, so it's skipped to speed up the computation
 ProvablyComputeQuadPts_X0N(86 : d:=43, nonpullbacks:=nonpbs, badPrimes:={7});