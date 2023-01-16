//SetLogFile("main.log");
//load "X0p_NiceModel.m";
load "new_models.m";
load "auxiliary.m";
load "Chabauty_MWSieve_new.m";
load "rank_calcs.m";

ProvablyComputeQuadPts_X0N := function(N : d := N, badPrimes := {})
	printf "Genus of X_0(%o) is: %o\n", N, Dimension(CuspForms(N));
	printf "Considering the quotient X_0(%o)/w_%o.\n", N, d;
	//  Check rk J_0(N)(Q) = rk J_0(N)^+(Q)
	time if d eq N then
		if not IsRankOfALQuotEqual(N) then
			error "One needs rk J_0(N)(Q) = rk J_0(N)^+(Q) for our algorithm to work.";
		else
			printf "rk J_0(N)(Q) = rk J_0(N)^+(Q).\n";
		end if;
	else
		if rank_quo(N, [d]) ne rank_quo(N, []) then
			error "One needs rk J_0(N)(Q) = rk J_0(N)(Q)/w_d for our algorithm to work.";
		else
			printf "rk J_0(%o)(Q) = rk J_0(%o)(Q)/w_%o.\n", N, N, d;
		end if;
	end if;

	printf "Computing equations for X_0(%o) ...\n", N;
	time XN, ws, _, _, cuspInf := eqs_quos(N, []);
	printf "Nice model for X_0(%o) is: %o\n", N, XN;
	printf "Genus of X_0(%o) is %o.\n", N, Genus(XN);

	printf "Computing cusps ...\n";
	time if IsSquarefree(N) then
		XN_Cusps := compute_cusps(XN, N, ws, cuspInf, []);
	else
		jMap, numDenom := jmap(XN, N);
		XN_Cusps := compute_cusps(XN, N, ws, cuspInf, numDenom);
	end if;
	printf "We have found these %o cusps on X_0(%o):\n%o\n", #XN_Cusps, N, XN_Cusps;

	// note that ALs are returned in ascending index
	ListOfDivs := [Q : Q in Divisors(N) | GCD(Q, ExactQuotient(N,Q)) eq 1 and Q ne 1];
	wd := ws[Index(ListOfDivs, d)];
	printf "w_%o on X_0(%o) is given by: %o\n", d, N, wd;

	//gens := [Divisor(c1) - Divisor(c2) : c1,c2 in XN_Cusps | c1 ne c2];

	//known degree 1 places
	pls1 := [XN_Cusps[i] : i in [1..#XN_Cusps] | Degree(XN_Cusps[i]) eq 1];

	//known degree 2 rational effective divisors
	deg2 := [1*XN_Cusps[i] : i in [1..#XN_Cusps] | Degree(XN_Cusps[i]) eq 2];
	deg2pb := [];

	for i in [1..#pls1] do
		for j in [i..#pls1] do
			Append(~deg2, 1*pls1[i] + 1*pls1[j]);
			
			if wd(RepresentativePoint(pls1[i])) eq RepresentativePoint(pls1[j]) then
				Append(~deg2pb, 1*pls1[i] + 1*pls1[j]);
			end if;
		end for;
	end for;

	printf "We have found %o points on X_0(%o)^2(Q).\n", #deg2, N;

	//Finally, we do the sieve.

	printf "Computing torsion subgroup ...\n";
	time A, divs := GetTorsion(N, XN, XN_Cusps);
	genusC := genus_quo(N, [d]);
	printf "Genus of the quotient X_0(%o)/w_%o is %o.\n", N, d, genusC;
	bp := deg2pb[1];
	wdMatrix := Matrix(wd);

	primes := []; // TODO: find suitable primes -- in practice, small primes yield good results

	for p in PrimesInInterval(3, 30) do
		if p in badPrimes then
			continue;
		end if;
		if N mod p ne 0 then
			Append(~primes, p);
		end if;
	end for;

	printf "Performing Mordell--Weil Sieve ...\n";
	B0, iA0 := sub<A | Generators(A)>;
	W0 := {0*A.1};

	B, iA, W := MWSieve(XN, wdMatrix, genusC, primes, A, divs, bp, B0, iA0, W0, deg2);

	printf "\nFor unknown Q in X_0(%o)^2(Q) we have (1 - w_%o)[Q - bp] is in a coset of %o represented by an element of %o.\n", N, N, B, W;

	if #W eq 1 and IsIdentity(W[1]) then
		printf "It follows that if there is an unknown Q in X_0(%o)^2(Q), then (1 - w_%o)[Q - bp] == 0.\n", N, N;
		printf "This implies that [Q - bp] is fixed by w_%o\n", N;
		printf "Then Q ~ w_%o(Q), which implies that Q = w_%o(Q) because X_0(%o) is not hyperelliptic.\n", N, N, N;
		printf "Then either Q is a pullback, or it is fixed by w_%o pointwise.\n", N;
		printf "If P = (X_i) is fixed by w_%o,\n", N;
		printf "either the first %o coordinates are 0 or the last %o coordinates are 0\n\n", genusC, Dimension(CuspForms(N)) - genusC;

		I := IdentityMatrix(Rationals(), Genus(XN));
		CR<[x]> := CoordinateRing(AmbientSpace(XN));

		// all coordinates where there is a -1 in w_N must be 0 for a point fixed by w_N
		J1 := &+[ideal<CR | &+[v[i]*x[i] : i in [1..Genus(XN)]]> : v in Basis(Kernel(wdMatrix + I))];
		J2 := &+[ideal<CR | &+[v[i]*x[i] : i in [1..Genus(XN)]]> : v in Basis(Kernel(wdMatrix - I))];

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
			error "TODO: Sieve worked, but we still need to analyze quadratic points (there are some).";
		end if;
	else 
		error "TODO: Sieve did not prove what we wanted.";
	end if;

	return "done";
end function;