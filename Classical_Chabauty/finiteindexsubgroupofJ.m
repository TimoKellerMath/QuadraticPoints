// The main function in this file is IsFiniteIndexSubgroupOfJacobian which takes as input
// a curve X, whether it is hyperelliptic, the MW rank of its Jacobian J, a list of rational points
// and returns whether the differences of that points generate a finite index subgroup of J(Q)

load "../rank_calcs.m";

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

//////////////////
/// JacobianFp ///
//////////////////

// This function computes Jac(X)(F_q) for a curve X defined over a finite field F_q
// Input: X - a curve defined over F_q
// Output:
// - A finite abelian group A isomorphic to Jac(X)(F_q)
// - a map from A to the group of divisors of X
// - a map from the group of divisors of X to A, which sends a divisor to its divisor class.
JacobianFp := function(X);
	CC, phi, psi := ClassGroup(X); //Algorithm of Hess
	JFp := TorsionSubgroup(CC);
	return JFp, phi, psi;
end function;


////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

/////////////////
/// NewReduce ///
/////////////////

// Input:
// - A projective curve X over Q
// - Basechange of X to F_p for a prime p of good reduction
// - a divisor on X
// Output:
// - The given divisor reduced to X/F_p.
// Note: This code assumes that X/\Q is a non-hyperelliptic curve (genus \ge 3) with Mordell-Weil rank 0.

NewReduce := function(X, Xp, D);
	if Type(D) eq DivCrvElt then
		decomp := Decomposition(D);
		return &+[pr[2]*$$(X, Xp, pr[1]) : pr in decomp]; // Reduce the problem to reducing places.
	end if;

	Fp := BaseRing(Xp);
	p := Characteristic(Fp);
	
	Qa := Type(D) eq Pt select Coordinates(D) else Coordinates(RepresentativePoint(D));
	K := Parent(Qa[1]);
	if IsIsomorphic(K, Rationals()) then
		K := RationalsAsNumberField();
	end if;

	OK := RingOfIntegers(K);
	dec := Factorization(p * OK);
	ret := Zero(DivisorGroup(Xp));

	for factor in dec do
		pp := factor[1];                   // A prime above the rational prime p
		assert factor[2] eq 1;

		f := InertiaDegree(pp);            
		Fpp<t> := ResidueClassField(pp); 
		Xpp := ChangeRing(X,Fpp);

		unif := UniformizingElement(pp);   // Use to reduce point modulo p
		m := Minimum([Valuation(K!a, pp) : a in Qa | not a eq 0]);  
		Qared := [unif^(-m)*(K!a) : a in Qa]; 
		Qtaa := Xpp![Evaluate(a,Place(pp)) : a in Qared]; // Reduction of point to Xpp
		Qta := Xp(Fpp) ! Eltseq(Qtaa);      

		ret := ret + 1*Place(Qta);
  	end for;

	return ret;
end function;

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

//////////////
/// reduce ///
//////////////

// This is an old version of the function NewReduce above.
// Input:
// - A projective curve X over Q
// - Basechange of X to F_p for a prime p of good reduction
// - a divisor on X
// Output:
// - The given divisor reduced to X/F_p.
// Note: This code assumes that X/\Q is a non-hyperelliptic curve (genus \ge 3) with Mordell-Weil rank 0.

reduce := function(X,Xp,D);
	if Type(D) eq DivCrvElt then
		decomp:=Decomposition(D);
		return &+[ pr[2]*$$(X,Xp,pr[1]) : pr in decomp]; // Reduce the problem to reducing places.
	end if;
	assert Type(D) eq PlcCrvElt;
	if  Degree(D) eq 1 then
		P:=D;
		R<[x]>:=CoordinateRing(AmbientSpace(X));
		n:=Rank(R);
		KX:=FunctionField(X);
		inds:=[i : i in [1..n] | &and[Valuation(KX!(x[j]/x[i]),P) ge 0 : j in [1..n]]];	
		assert #inds ne 0;
		i:=inds[1];
		PP:=[Evaluate(KX!(x[j]/x[i]),P) : j in [1..n]];
		denom:=LCM([Denominator(d) : d in PP]);
		PP:=[Integers()!(denom*d) : d in PP];
		g:=GCD(PP);
		PP:=[d div g : d in PP];
		Fp:=BaseRing(Xp);
		PP:=Xp![Fp!d : d in PP];
		return Place(PP);
	end if;
	I:=Ideal(D);
	Fp:=BaseRing(Xp);
	p:=Characteristic(Fp);
	B:=Basis(I) cat DefiningEquations(X);
	n:=Rank(CoordinateRing(X));
	assert Rank(CoordinateRing(Xp)) eq n;
	R:=PolynomialRing(Integers(),n);
	BR:=[];
	for f in B do
		g:=f*p^-(Minimum([Valuation(c,p) : c in Coefficients(f)]));
		g:=g*LCM([Denominator(c) : c in Coefficients(g)]);
		Append(~BR,g);
	end for;
	J:=ideal<R | BR>;
	J:=Saturation(J,R!p);
	BR:=Basis(J);
	Rp:=CoordinateRing(AmbientSpace(Xp));
	assert Rank(Rp) eq n;
	BRp:=[Evaluate(f,[Rp.i : i in [1..n]]) : f in BR];
	Jp:=ideal<Rp| BRp>;
	Dp:=Divisor(Xp,Jp);
	return Dp;
end function;

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

/////////////////
/// relations ///
/////////////////

// This function returns the space of relations between a given sequence xs of
// elements in an abelian group A
// Input: An abelian group A, a list xs of elements of A
// Output: The space of relations between the given elements in A, as a subspace of Z^(#xs).

relations := function(A,xs);
    R := FreeAbelianGroup(#xs);
    f := hom<R -> A | xs>;
    return Kernel(f);
end function;


////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

//////////////////////
/// relations_divs ///
//////////////////////

// This function returns a space containing the space of relations between a
// given sequence of divisors on a curve X defined over Q.
// This is done by reducing the divisors modulo a bunch of primes p,
// finding the relations between the reduced divisors in Jac(X_p)(F_p),
// and intersecting the space of relations found for the various primes.

// Input:
// - A curve X defined over Q
// - A list of divisors of X, (not necessarily of degree 0)
// - A rational base point of X
// - (optional) list of primes to work with
// - (optional) a bound for deciding between small height relations (which most likely come from Q),
// and large height relations (which exist only over the various finite fields F_p for the primes tried).
// Output:
// - a list consisting of the relations found between the degree zero divisors D-deg(D)*bp
// Note: The relations outputted are checked to be correct using IsPrincipal().
// Note: But, the space spanned by the output could be strictly smaller than the actual space of relations.

relations_divs := function(X, divs, bp : primes := PrimesUpTo(30), bd := 1000);
    fullrelsspace := FreeAbelianGroup(#divs);
	relsspace := fullrelsspace;
	printf "Starting with %o divisors/relations.\n\n", TorsionFreeRank(fullrelsspace);
    for p in primes do
        try
            Xp := ChangeRing(X,GF(p));
			bpp := NewReduce(X,Xp,bp);
			printf "Computing Jacobian of the curve over F_%o\n", p;
            Jfp, phi, psi := JacobianFp(Xp);
			printf "Done computing Jacobian\n";
            divsp := [];
			printf "Trying to reduce %o divisors modulo %o\n", #divs, p;
            for D in divs do
                Append(~divsp,NewReduce(X,Xp,D));
				printf ".";
            end for;
			printf "Reduced divisors\nCalculating relations between the reduced divisors\n";
			psibpp := psi(bpp);
			divspzero := [psi(D) - Degree(D)*psibpp : D in divsp];
            relsp := relations(Jfp,divspzero);
			printf "Done calculating relations.\n";
        catch e
			printf "Prime %o is bad.\n\n", p;
            Exclude(~primes,p);
            continue;
        end try;
		printf "Found %o relations.\n", TorsionFreeRank(relsp);
		n_oldrelsspace := TorsionFreeRank(relsspace);
        relsspace meet:= relsp;
		if TorsionFreeRank(relsspace) lt n_oldrelsspace then
			printf "Reducing mod %o has cut down the relation space by %o.\n", p, n_oldrelsspace - TorsionFreeRank(relsspace);
		end if;
		printf "\n";
    end for;
	
	printf "Removing the relations that don't hold over the number field ...\n";
    L := Lattice(#divs, &cat[Eltseq(fullrelsspace ! relsspace.i) : i in [1..#divs]]);
	Lprime, T := LLL(L);
	small_rels := [Eltseq(Lprime.i) : i in [1..#divs] | Norm(Lprime.i) lt bd*#divs]; // only consider small relations
	for r in small_rels do
		D := &+[r[i]*divs[i] : i in [1..#divs]] - &+[r[i]*Degree(divs[i]) : i in [1..#divs]] * Place(bp);
		if not IsPrincipal(D) then
			Exclude(~small_rels,r);
			printf ".";
		end if;
	end for;
	printf "Found %o relations.\n", #small_rels;
	return small_rels;
end function;

////////////////////////////////////////////////////////
// +++++++++++++++++++++++++++++++++++++++++++++++++++++
////////////////////////////////////////////////////////

///////////////////////////////////////
/// IsFiniteIndexSubgroupOfJacobian ///
///////////////////////////////////////

// This function attempts to decide whether the differences of rational points generate a finite index subgroup of a Jacobian

// Input: The curve X, whether it is hyperelliptic, the MW rank of its Jacobian J, a list of rational points
// Output: true iff the differences of the given rational points generate a finite index subgroup of J(Q)

IsFiniteIndexSubgroupOfJacobian := function(X, curvhyp, r, X_pts : primes := PrimesUpTo(30));
		if r eq 0 then
			return true;
		end if;
		if curvhyp then
			X_simp, isom := SimplifiedModel(X);
			J := Jacobian(X_simp);
			if Genus(X_simp) eq 2 then
				ptsJ := Points(J : Bound := 100);
			else
				ptsX_simp := Points(X_simp : Bound := 1000);
				ptsJ := [ptsX_simp[i] - ptsX_simp[1] : i in [2..#ptsX_simp]];
			end if;
			try
				bas, htpair := ReducedBasis(ptsJ); // for hyperelliptic curves, we can compute in the MW group of the Jacobian
			catch e
				error "Couldn't compute a reduced basis.";
			end try;
			return #bas eq r;
		else // for non-hyperelliptic curves, we have to compute in the Jacobian mod p, i.e., in class groups, which we can.
            bp := X_pts[1];
			divs := [Divisor(pt) : pt in X_pts[2..#X_pts]];
			rels := relations_divs(X, divs, bp : primes := primes, bd := 1000); // we find relations in J(F_p) for small p
			printf "There are %o relations between %o divisors.\n", #rels, #divs;
            return (#divs - #rels) ge r;
		end if;
end function;