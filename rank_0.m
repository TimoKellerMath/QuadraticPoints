// This file contains the main function for the rank 0 method

// The output of this function for N = 80, 98, and 100 is included in the rank_0.log file in the Output_files folder

// Input: N
// No output, but function computes and returns information about the quadratic points found

load "models_and_maps.m";
load "rank_0_auxiliary.m";
load "rank_calcs.m";

rank_0_quad_pts :=function(N)

	printf "Genus of X_0(%o) is: %o\n", N, Dimension(CuspForms(N));
	//check the rank is 0
	assert 0 eq rank_quo(N,[]);

	//computing equations of X0(N) and the jmap
	X, _, _, _, cusp := eqs_quos(N, []);
	jinvN, num_denom := jmap(X, N); 


	//computing cusps
	cusps := compute_cusps(X, N, [], [], num_denom);

	// Sanity check!
	// The cusp degrees as predicted by theory.
	cuspDegrees := [EulerPhi(GCD(m, N div m)) : m in Divisors(N)]; 
	// Check if the degrees of the cusps we have found agree with theory.
	assert Sort(cuspDegrees) eq Sort([Degree(c) : c in cusps]); 
	cusps1 := [P : P in cusps | Degree(P) eq 1];
	assert #cusps1 ge 2; 
				// There are always at least two cusps 
				// of degree 1 corresponding to the
				// factors 1 and N of N.
	P0 := cusps1[1]; // This will be our base point for the Abel-Jacobi map.
	cusps2:=[P : P in cusps | Degree(P) eq 2]; 
	deg2:=[cusps1[i]+cusps1[j] : i,j in [1..#cusps1] | i le j] cat [1*P : P in cusps2];


	//finding explicit gens for the cuspidal subgroup
	p0:=3;
	h,Ksub,bas,divs:=findGenerators(X,N,cusps,P0,p0);

	// Here Ksub is an abstract group isomorphic to the
		// subgroup of J(\Q) generated by [D-degree(D)*P0 : D in cusps] (i.e. the cuspidal subgroup).
		// divs is a subset of cusps that generates the same group.
		// h is the homomorphism \Z^r-->Ksub where r=#divs
		// and i-th standard basis vector is mapped to the image of
		// D-degree(D)*P0 where D=cusps[r].
		// bas is a subset of \Z^r which maps to a basis of Ksub
		// and is therefore (morally) a basis for the cuspidal  
		// subgroup of J(\Q).

	//the following two lines are to make sure that we are not assuming generalized ogg's conjecture
	if N eq 80 then 
		I:=4; 
	end if;
	if N eq 98 or N eq 100 then 
		I:=1;
	end if;

	//here starts the sieve part
	UB:=23; 
	additionalBadPrimes:=[];
	prs:=[p : p in PrimesInInterval(3,UB) | IsDivisibleBy(N,p) eq false and p notin additionalBadPrimes];
	deg2New:=rank_0_sieve(X,N,deg2,divs,P0,h,Ksub,bas,[p0],1);
	// Trying to find additional degree 2 divisors by sieve modulo p0.
	deg2New:=[D : D in deg2New | D in deg2 eq false];
	print "The Mordell--Weil sieve found", #deg2New, "new effective degree 2 divisors.";

	deg2:=deg2 cat deg2New;
	degtwoI:=rank_0_sieve(X,N,deg2,divs,P0,h,Ksub,bas,prs,I);
	// This uses the Mordell--Weil sieve (with primes in prs) 
		// to return a set of effective divisors of degree 2*I 
		// such that if D is an effective degree 2 divisor not
		// in deg2 then I*D is linearly equivalent to some element of degtwoI.
		//since #degtwoI eq 0 then we can say "succeeded in determining all effective divisors of degree 2";
	assert #degtwoI eq 0;        

	pls:=[pr[1] : pr in &cat[Decomposition(D) : D in deg2]];
	// Places of degree 1.
	pls1:=SetToSequence(Set([D : D in pls | Degree(D) eq 1])); 
	// Places of degree 2.
	pls2:=SetToSequence(Set([D : D in pls | Degree(D) eq 2])); 

	for P in pls2 do
		K:=ResidueClassField(P);
		D:=Discriminant(MaximalOrder(K));
		if IsDivisibleBy(D,4) then
			D:=D div 4;
		end if;	
		L<t>:=QuadraticField(D);
		assert IsIsomorphic(K,L);
		PP:=RepresentativePoint(P);
		if jinvN(PP)[2] eq 0 then 
		    print "This quadratic point is cuspidal";
		    print "Coordinates", X(L) ! PP;
		    continue;
		end if;
		j:=jinvN(PP)[1];
		M:=MinimalPolynomial(j);
		rts:=Roots(M,L);
		assert #rts ge 1;
		jinv:=rts[1,1];
		E:=EllipticCurveWithjInvariant(jinv);
		print "The place P is defined over", L;
		print "The j-invariant is", j;
		print "Complex multiplication?";
		print HasComplexMultiplication(E);
		print "Coordinates", X(L) ! PP;
		print "++++++++++++++++++++++++++";
	end for;
	return "done";
end function;

// for N in [80,98,100] do rank_0_quad_pts(N); end for; // See rank_0.log in the Output_files folder
    




