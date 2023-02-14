SetLogFile("main.log");
load "new_models.m";
load "auxiliary.m";
load "Chabauty_MWSieve_new.m";
load "rank_calcs.m";

SetDebugOnError(true);

SetMemoryLimit(35579344000);

N := 86;

// we look at quotient X_0(86)/w43 because it has rank 2 as X_0(86)
assert rank_quo(86, []) eq rank_quo(86, [43]);

XN, ws, _, _, cuspInf := eqs_quos(N, []);

XN_Cusps := compute_cusps(XN, N, ws, cuspInf, []);

printf "Nice model for X_0(%o) is: %o\n\n", N, XN;

wN := ws[#ws - 1]; //this is because ALs are returned in ascending index, pre-last is w37
printf "w_%o on X_0(%o) is given by: %o\n", N/2, N, wN;

_<x> := PolynomialRing(Rationals());
K7<r3> := NumberField(x^2+1/7);

P1 := XN(K7)! [-1, r3,0, -r3, -r3, -r3, r3, r3, 1, 1];
P2 := XN(K7) ! [1, -r3,0, r3, r3, -r3, r3, r3, 1, 1];


j_map := jmap(XN, 86);
print j_map(P1);
print j_map(P2);

printf "Genus of X_0(%o) is %o\n", N, Genus(XN);
printf "We have found these points on X_0(%o):\n%o\n", N, XN_Cusps;
P1;
P2;

//known degree 1 places
pls1 := [XN_Cusps[i] : i in [1..#XN_Cusps] | Degree(XN_Cusps[i]) eq 1];

//known degree 2 rational effective divisors
deg2 := [1*XN_Cusps[i] : i in [1..#XN_Cusps] | Degree(XN_Cusps[i]) eq 2];
Append(~deg2, 1*Place(P1));
Append(~deg2, 1*Place(P2));

deg2pb := [];

for i in [1..#pls1] do
	for j in [i..#pls1] do
		Append(~deg2, 1*pls1[i] + 1*pls1[j]);
			
		if wN(RepresentativePoint(pls1[i])) eq RepresentativePoint(pls1[j]) then
			Append(~deg2pb, 1*pls1[i] + 1*pls1[j]);
		end if;

	end for;
end for;

printf "We have found %o points on X_0(%o)^2(Q).\n", #deg2, N;

//Finally, we do the sieve.

A, divs := GetTorsion(N, XN, XN_Cusps);
torsBound := TorsionBound(XN, [2, 43] : PrimesBound := 25);

//this proves we have the correct torsion
assert torsBound eq #A;

genusC := genus_quo(N, [N/2]);

printf "Genus of X_0(%o)/w%o is %o.\n", N, N/2, genusC;

bp := deg2pb[1];
wNMatrix := Matrix(wN);

primes := PrimesInInterval(3, 35); // TODO: find suitable primes
B0, iA0 := sub<A | Generators(A)>;
W0 := {0*A.1};

B, iA, W := MWSieve(XN, wNMatrix, genusC, primes, A, divs, bp, B0, iA0, W0, deg2);

printf "\nFor unknown Q in X_0(%o)^2(\Q) we have (1 - w_%o)[Q - bp] is in a coset of %o represented by an element of %o.\n", N, N/2, B, W;

if #W eq 1 and IsIdentity(W[1]) then
	printf "It follows that if there is an unknown Q in X_0(%o)^2(\Q), then (1 - w_%o)[Q - bp] == 0.\n", N, N/2;
	printf "This implies that [Q - bp] is fixed by w_%o\n", N/2;
	printf "Then Q ~ w_%o(Q), which implies that Q = w_%o(Q) because X_0(%o) is not hyperelliptic.\n", N/2, N/2, N;
	printf "Then either Q is a pullback, or it is fixed by w_%o pointwise.\n", N/2;
	printf "If P = (X_i) is fixed by w_%o,\n", N/2;
	printf "either the coordinates at indices 2, 3, 4, 8 are 0 or the other 4 coordinates are 0\n\n";

	I := IdentityMatrix(Rationals(), Genus(XN));
	CR<[x]> := CoordinateRing(AmbientSpace(XN));

	// all coordinates where there is a -1 in w_N must be 0 for a point fixed by w_N
	J1 := &+[ideal<CR | &+[v[i]*x[i] : i in [1..Genus(XN)]]> : v in Basis(Kernel(wNMatrix + I))];
	J2 := &+[ideal<CR | &+[v[i]*x[i] : i in [1..Genus(XN)]]> : v in Basis(Kernel(wNMatrix - I))];

	Z1 := Scheme(XN, J1);
	Z2 := Scheme(XN, J2);
	Z := Union(Z1, Z2);
	printf "We find all such P by imposing these conditions and finding points on the scheme:\n%o\n\n", Z;

	pts := PointsOverSplittingField(Z);
	printf "All such P are:\n%o\n", pts;

	pts_of_deg_le_2 := [P : P in pts | forall{i : i in [1..Dimension(AmbientSpace(Z))] | Degree(MinimalPolynomial(P[i])) le 2}];
	ptsclstr := [Cluster(Z, P) : P in pts_of_deg_le_2];
	degrees := [Degree(P) : P in ptsclstr];
	printf "The degrees of these points are %o (or > 2).\n", degrees;

	if forall{deg: deg in degrees | deg ne 2} then
		printf "Hence there are no quadratic points on X_0(%o) not coming from pullbacks of rationals.\n", N;
	else
		printf "Apart from pullbacks of rational points on X_0(%o)/w%o, we have these quadratic points on X_0(%o):", N, N/2, N;
		P1;
		P2;
		pts;
		for pt in pts do
			printf "%o has j-invariant %o\n", pt, j_map(pt);
		end for;
	end if;
else 
	error "TODO: Sieve did not prove what we wanted.";
end if;

