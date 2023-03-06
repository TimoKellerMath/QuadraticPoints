load "rank_0_auxiliary.m";
load "rel_symm_chab.m";
load "models_and_maps.m";

//This function computes J_X(F_p) for curve X

JacobianFp := function(X)
	CC, phi, psi := ClassGroup(X); //Algorithm of Hess
	//Z := FreeAbelianGroup(1);
	//degr := hom<CC->Z | [ Degree(phi(a))*Z.1 : a in OrderedGenerators(CC)]>;
	//JFp := Kernel(degr); // This is isomorphic to J_X(\F_p).
	JFp := TorsionSubgroup(CC);
	return JFp, phi, psi;
end function;

//This function computes the discriminant of the field a place is defined over.

discQuadPlace := function(P);
        assert Degree(P) eq 2;
        K := ResidueClassField(P);
    	D := Discriminant(MaximalOrder(K));

    	if IsDivisibleBy(D, 4) then
           D := D div 4;
    	end if;

        return D;
end function;

///////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////

upper_bound_tors := function(N: largest_prime := 50, lower_bound := 1);
    J := JZero(N);
    ub := 0;    
    for p in [p : p in PrimesInInterval(3,largest_prime) | IsZero(N mod p) eq false] do
        Jp := ChangeRing(J,GF(p));
        ub := GCD([ub,#Jp]); 
        if ub eq lower_bound then 
            break p;   
        end if;   
    end for;  
    return ub, Factorisation(ub);    
end function;

function GetTorsion(N, XN, XN_Cusps)

	if IsPrime(N) then
		// sanity check
		assert #XN_Cusps eq 2;

		Dtor := Divisor(XN_Cusps[1]) - Divisor(XN_Cusps[2]);
		order := Integers()!((N - 1) / GCD(N - 1, 12));
		
		A := AbelianGroup([order]);
		divs := [Dtor];
	else
		p := 3;
		while IsDivisibleBy(N, p) do
			p := NextPrime(p);
		end while;

		// compute the cuspidal torsion subgroup (= J(Q)_tors assuming the generalized Ogg conjecture)
		XN_Cusps_rational := [c : c in XN_Cusps | Degree(c) eq 1];
		assert #XN_Cusps_rational ge 1;
		cusp := XN_Cusps_rational[1];
		h, Ksub, bas, divsNew := findGenerators(XN, XN_Cusps, cusp, p);

		// Ksub == abstract group isomorphic to cuspidal
		// "It also returns a subset divsNew such that [[D-deg(D) P_0] : D in divsNew] generates the same subgroup."

		A := Ksub;

		//prove that the cuspidal torsion   subgroup = J(Q)_tors   for our curve
		torBound := upper_bound_tors(N);
		assert torBound eq #Ksub;

		D := [divisor - Degree(divisor) * Divisor(cusp) where divisor := Divisor(divsNew[i]) : i in [1..#divsNew]];
		divs := [&+[coeffs[i] * D[i] : i in [1..#coeffs]] : coeffs in bas];
	end if;

	return A, divs;

end function;


///////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////

//D is an element of an abstract group iso. to JFp which we want to map to divisor class
//JFpGenerators are generators of JFp - Jacobian modulo p
//PhiActionTable is the value of phi() on generators

//example how I checked that this works as intended:
//table := [Decomposition(phi(g)) : g in OrderedGenerators(JFp)];
//assert BetterPhi(z + k, OrderedGenerators(JFp), table, JFp) eq phi(z + k);

//not used in code yet because we might want to discuss it first
//testing showed significant speed gains for X0(137)

BetterPhi := function(D, JFpGenerators, PhiActionTable, JFp)
	rep := Representation(JFpGenerators, D);
		
	for j in [1..#JFpGenerators] do
		for i in [1..#PhiActionTable[j]] do
			PhiActionTable[j][i][2] := PhiActionTable[j][i][2] * (rep[j] mod Order(JFp.j));
		end for;
	end for;

	divNew := &+[Divisor(PhiActionTable[j]) : j in [1..#JFpGenerators]];

	return divNew;
end function;

// Called by MWSieve, performs step for p_i described in the article

ChabautyInfo := function(X, AtkinLehner, genusC, p, A, divs, Dpull, B, iA, W, deg2)
	//first get J(X_p)
	Fp := GF(p);
	Xp := ChangeRing(X, Fp);

	//We reduce the divisors and the basepoint
	JFp, phi, psi := JacobianFp(Xp);
	divsp := [reduce(X, Xp, divi) : divi in divs];
	Dpull_p := reduce(X, Xp, Dpull);
	
	"Getting deg 1 places on Xp ...";
	places_of_degree_1_mod_p := Places(Xp, 1);   // The degree 1 places on Xp

	"Getting deg 2 places on Xp ...";
	places_of_degree_2_mod_p := Places(Xp, 2);   // The degree 2 places on Xp 

	// degree 2 divisors on Xp
	"Combining them into divisors ...";
	degree2divisors_mod_p := {1*place1 + 1*place2 : place1, place2 in places_of_degree_1_mod_p} join {1*place : place in places_of_degree_2_mod_p};
	"There are", #degree2divisors_mod_p, "of them!";

	deg2Divs_p_set := Setseq(degree2divisors_mod_p);	// turn them into set
	Abstracts := [JFp!psi(deg2Divs_p_set[i] - Dpull_p) : i in [1..#deg2Divs_p_set]];	// elements on JFp (as abstract group)

	//The map A -> J_X(\F_p).
	h := hom<A -> JFp | [(JFp!psi(divp)) : divp in divsp]>;

	//reduce known degree 2 divisors
	deg2p := [1*reduce(X, Xp, DDD) : DDD in deg2];
	deg2p2 := [psi(DD - Dpull_p) : DD in deg2p];

	//We now split our cosets represented by elements of W
	//into smaller cosets on which h takes a single value.
	Bp, iAp := sub<A | Kernel(h)>;
	newB, newiA := sub<A | iA(B) meet iAp(Bp)>; 
	AmodnewB, pi1 := quo< A | newiA(newB)>;
	AmodB, pi2 := quo<AmodnewB | pi1(iA(B))>;
	W := [(x + w)@@pi1 : x in Kernel(pi2), w in pi1(W)]; 
	B := newB;
	iA := newiA;

	gensJFp := OrderedGenerators(JFp);
	table := [Decomposition(phi(g)) : g in gensJFp];
	// we use that h(W) must be subset of Image(mI)
	mI := hom<JFp -> JFp | [JFp!psi(OneMinusWmodp(Xp, BetterPhi(g, gensJFp, table, JFp), AtkinLehner, p)) : g in gensJFp]>;
	imW := {@ h(x) : x in W | h(x) in Image(mI) @}; 
	K := Kernel(mI);
	jposP := [];

	//For each z such that (1 - w)*z = x, we check whether z can come from a rational point on X^(2).
	//We try to eliminate z as described in the article.
	//If we can't eliminate at least one z such that (1 - w)*z = x, we keep x.
	printf "out of %o: ", #imW;
	
	for x in imW do
    	z := x@@mI;
		
		// we check if z + k is one of the candidate divisors from above
		// this avoids calling phi() and/or Dimension() which can be slow
		// this can be improved further by avoiding the above preimage x@@mI
		
		/*if &or[(z + k in Abstracts) and (not z + k in deg2p2 or not IsLonely(deg2[Index(deg2p2, z + k)], p, X, AtkinLehner, genusC)) : k in K] then
			Append(~jposP, x);
    	end if;*/

		for k in K do 
			/*if (z + k in Abstracts) and (not z + k in deg2p2 or not IsLonely(deg2[Index(deg2p2, z + k)], p, X, AtkinLehner, genusC)) then 
				Append(~jposP, x);
				break;
			end if;*/
			if z + k in Abstracts then
				if not z + k in deg2p2 or not IsLonely(deg2[Index(deg2p2, z + k)], p, X, AtkinLehner, genusC) then
					Append(~jposP, x);
					break;
				end if;
			end if;
		end for;
	end for;

	//We keep those x in W which we were unable to eliminate
	W := [x : x in W | h(x) in jposP]; 
	return W, B, iA; 
end function;


// INPUT:
// model 'X' for projective curve X/\Q;
// set 'deg2' of degree 2 divisors on X (known points on X^(2)(\Q));
// matrix 'AtkinLehner' defining Atkin-Lehner operator on X such that C = X/<AtkinLehner>, rk(J(C)(\Q))=rk(J(X)(\Q));
// set 'divs' of degree 0 divisors that generate a subgroup G \subset J(X)(\Q), such that (1-w)(J(X)(\Q)) <= G;
// abstract abelian group 'A' isomorphic to G such that A.i corresponds to divs[i];
// number 'genusC' that is the genus of C;
// a degree 2 divisor 'Dpull' on X that is the pullback of a rational point on C, to be used to embed X^{(2)} in J;
// subgroup 'B0' <= A, inclusion 'iA0': A -> B0, set 'W0' of B0-coset representatives such that B0 + W0 = A.

MWSieve := function(X, AtkinLehner, genusC, primes, A, divs, Dpull, B0, iA0, W0, deg2)
	B := B0;
	iA := iA0;
	W := W0;
	
	// Together, B+W \subset A consists of the possible images of unknown (rational)
	// points in A. The map X^(2)(\Q) \to A is composition of X^(2)(\Q) \to J(X)(\Q) and
	// multiplication by (1-Atkinlehner) such that (1-Atkinlehner)*J(X)(\Q) \subset A.
	
	for i -> p in primes do
		printf "p = %o (%o/%o): ", p, i, #primes;
		W, B, iA := ChabautyInfo(X, AtkinLehner, genusC, p, A, divs, Dpull, B, iA, W, deg2);

		// We get B<=A and W a set of B-coset representatives such that
		// hypothetical unknown points map to one of those cosets

		printf "The number of possible cosets unknown points can land in is %o.\n", #W;

		if W eq [] then
			return true;
		end if;
		
		//this is actually our goal
		if #W eq 1 and IsIdentity(W[1]) then
			return B, iA, W;
		end if;
	end for;
	return B, iA, W;
end function;

/////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////



//ProvablyComputeQuadPts_X0N requires only level N as its input
// but it also contains a number of optional parameters:
// d: the code will use the quotient X0(N)/w_d (defaults to d:=N)
// nonpullbacks: you can provide the list of quadratic points which are not pullbacks from X0(N)/w_d
//	if you use it, nonpullbacks must be the sequence of elements of the following shape
// 		<K, P> where K is the field over which P is defined
//	for example, look at X0_74.m
// badPrimes: list of primes you want to skip the sieving on
// printTorsion: boolean parameter, if true, the code will output the torsion of J_0(N)(Q)

// The function does not return anything, but outputs a lot of information about modular curve X_0(N):
//	first it checks if the ranks of the curve and its quotient are equal (and outputs confirmation),
//	then it outputs a nice model of the curve (with Atkin-Lehner's diagonalized),
//		the action of w_d on the curve,
//	then on its Jacobian (cusps, and if printTorsion is set to true, the full torsion structure over Q),
//	and finally on the sieving process.

// In all cases where all the quadratic points are pullbacks from X_0+(N),
// it is sufficient to simply run ProvablyComputeQuadPts_X0N(N).

AL_sieve := function(N : d := N, nonpullbacks := {}, badPrimes := {}, printTorsion := false)
	printf "Genus of X_0(%o) is: %o\n", N, Dimension(CuspForms(N));
	printf "Considering X_0(%o)/w_%o.\n", N, d;
	
	//  Check rk J_0(N)(Q) = rk J_0(N)^+(Q)
	tf1, tf2 := equal_rank(N, [d]);
	if tf1 and tf2 then 
	    printf "rk J_0(%o)(Q) = rk J_0(%o)(Q)/w_%o \n", N, N, d;
        else 
	    error "One needs rk J_0(N)(Q) = rk J_0(N)^+(Q) for our algorithm to work.";
	end if;
	
	XN, ws, _, _, cuspInf := eqs_quos(N, []);

	if IsSquarefree(N) then
		XN_Cusps := compute_cusps(XN, N, ws, cuspInf, []);
	else
		jMap, numDenom := jmap(XN, N);
		XN_Cusps := compute_cusps(XN, N, ws, cuspInf, numDenom);
	end if;

	printf "Nice model for X_0(%o) is: %o\n\n", N, XN;

	// note that ALs are returned in ascending index
	ListOfDivs := [Q : Q in Divisors(N) | GCD(Q, ExactQuotient(N,Q)) eq 1 and Q ne 1];
	wd := ws[Index(ListOfDivs, d)];
	printf "w_%o on X_0(%o) is given by: %o\n", d, N, wd;

	printf "Genus of X_0(%o) is %o\n", N, Genus(XN);
	printf "We have found these %o cusps on X_0(%o):\n%o\n", #XN_Cusps, N, XN_Cusps;

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

	additional_points := [];

	for tup in nonpullbacks do
		nonpb := XN(tup[1])!tup[2];
		Append(~deg2, 1*Place(nonpb));
		Append(~additional_points, nonpb);
	end for;

	printf "We have found %o points on X_0(%o)^2(Q).\n", #deg2, N;

	//Finally, we do the sieve.

	printf "Computing torsion subgroup ...\n";
	A, divs := GetTorsion(N, XN, XN_Cusps);
	if printTorsion then printf "The torsion is %o\n", A;
	end if;

	genusC := genus_quo(N, [d]);
	printf "Genus of the quotient is %o.\n", genusC;
	bp := deg2pb[1];
	wdMatrix := Matrix(wd);

	primes := []; // TODO: find suitable primes

	for p in PrimesInInterval(3, 30) do
		if p in badPrimes then
			continue;
		end if;
		if N mod p ne 0 then
			Append(~primes, p);
		end if;
	end for;

	printf "Performing Mordell-Weil sieve ...\n";
	B0, iA0 := sub<A | Generators(A)>;
	W0 := {0*A.1};

	B, iA, W := MWSieve(XN, wdMatrix, genusC, primes, A, divs, bp, B0, iA0, W0, deg2);

	printf "\nFor unknown Q in X_0(%o)^2(\Q) we have (1 - w_%o)[Q - bp] is in a coset of %o represented by an element of %o.\n", N, N, B, W;

	if #W eq 1 and IsIdentity(W[1]) then
		printf "It follows that if there is an unknown Q in X_0(%o)^2(\Q), then (1 - w_%o)[Q - bp] == 0.\n", N, d;
		printf "This implies that [Q - bp] is fixed by w_%o\n", N;
		printf "Then Q ~ w_%o(Q), which implies that Q = w_%o(Q) because X_0(%o) is not hyperelliptic.\n", d, d, N;
		printf "Then either Q is a pullback, or it is fixed by w_%o pointwise.\n", d;
		printf "If P = (X_i) is fixed by w_%o,\n", d;
		//printf "either the first %o coordinates are 0 or the last %o coordinates are 0\n\n", genusC, Dimension(CuspForms(N)) - genusC;
		print "then certain coordinates must be 0.";
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
			printf "Hence there are no quadratic points on X_0(%o) not coming from pullbacks of rationals, except the points you forwarded: %o.\n", N, additional_points;
		else
			printf "Sieve worked, but we still need to analyze quadratic points (there are some).";
		end if;
	else 
		error "Sieve did not prove what we wanted.";
	end if;

	return "done";
end function;


