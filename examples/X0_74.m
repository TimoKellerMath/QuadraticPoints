
K7<r7> := QuadraticField(-7);

P1 := <K7, [-1, 0, 0, 1/r7, 2/r7, -2/r7, 1/r7, 1]>;
P2 := <K7, [-1, 0, 0, -1/r7, 2/r7, -2/r7, 1/r7, -1]>;
nonpbs := [P1, P2];
load "main.m";
 ProvablyComputeQuadPts_X0N(74 : d:=37, nonpullbacks := nonpbs);
exit;
