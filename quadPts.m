// Let N be a positive integer and n be a proper divisor.
// Suppose X_0(N) has genus \ge 3 and is not hyperelliptic.
// It is assumed that X_0(n) is in the Small Modular Curves database (n=1 is allowed).
// The function returns
// X,Z,phi,j, al, <num,denom>.
// X is the modular curve X_0(N)
// Z is the modular curve X_0(n) (exactly the same model as given by the Small Modular Curve package).
// \phi : X_0(N) \rightarrow X_0(n) is the degeneracy map.
// j is the j-function on X_0(N) as an element of its function field.
// al is a list of matrices whose action on the ambient projective space
// correspond to Atkin-Lehner involutions on X.
// num and denom are elements of the coordinate ring of the ambient
// space of X, such that num/denom restricted to X is the j-map.
modeqns:=function(N,n);
	assert IsDivisibleBy(N,n);
	gen0:=[1..10] cat [12, 13, 16, 18, 25]; // Values of N for which X_0(N) has genus 0.
	gen1:=[11, 14, 15, 17, 19, 20, 21, 24, 27, 32, 36, 49]; // Values of N for which X_0(N) has genus 1.
	hyp:=[37] cat [40,48] cat [22,23,26,28,29,30,31,33,35,39,41,46,47,50,59,71]; // Values of N for which X_0(N) is hyperelliptic.
	// These values are taken from Ogg's paper, "Hyperelliptic Modular Curves", Bull. Soc. math. France, 102, 1974, p. 449-462.
	assert #gen0 eq 15;
	assert #gen1 eq 12;
	assert #hyp eq 19;
	assert N in (gen0 cat gen1 cat hyp) eq false;
	// Thus X_0(N) has genus \ge 3 and is non-hyperelliptic, so the canonical map is an embedding.
	// We use this to construct the equations for X_0(N).
	prec:=500;
	L<q> := LaurentSeriesRing(Rationals(),prec);
	S:=CuspForms(N);
	dim:=Dimension(S);
	if dim eq 3 then
		R<x_0,x_1,x_2>:=PolynomialRing(Rationals(),dim);
	elif dim eq 4 then 
		R<x_0,x_1,x_2,x_3>:=PolynomialRing(Rationals(),dim);
	elif dim eq 5 then
		R<x_0,x_1,x_2,x_3,x_4>:=PolynomialRing(Rationals(),dim);
	else
		R<[x]>:=PolynomialRing(Rationals(),dim);
	end if;
	Bexp:=[L!qExpansion(S.i,prec) : i in [1..dim]];
	eqns:=[R | ];
	d:=1;
	tf:=false;
	while tf eq false do
		d:=d+1;
		mons:=MonomialsOfDegree(R,d);
		monsq:=[Evaluate(mon,Bexp) : mon in mons];
		V:=VectorSpace(Rationals(),#mons);
		W:=VectorSpace(Rationals(),prec-10);
		h:=hom<V->W | [W![Coefficient(monsq[i],j) : j in [1..(prec-10)]] : i in [1..#mons]]>;
		K:=Kernel(h);
		eqns:=eqns cat [ &+[Eltseq(V!k)[j]*mons[j] : j in [1..#mons] ] : k in Basis(K)  ];
		X:=Scheme(ProjectiveSpace(R),eqns);
		if Dimension(X) eq 1 then
			if IsSingular(X) eq false then
				X:=Curve(ProjectiveSpace(R),eqns);
				if Genus(X) eq dim then
					tf:=true;
				end if;
			end if;
		end if;
	end while;
	eqns:=GroebnerBasis(ideal<R | eqns>); // Simplifying the equations.
	tf:=true;
	repeat
		t:=#eqns;
		tf:=(eqns[t] in ideal<R | eqns[1..(t-1)]>);
		if tf then 
			Exclude(~eqns,eqns[t]);
		end if;
	until tf eq false;
	t:=0;
	repeat
		t:=t+1;
		tf:=(eqns[t] in ideal<R | Exclude(eqns,eqns[t])>);	
		if tf then
			Exclude(~eqns,eqns[t]);
			t:=0;
		end if;
	until tf eq false and t eq #eqns;
	X:=Curve(ProjectiveSpace(R),eqns); // Our model for X_0(N) discovered via the canonical embedding.
	assert Genus(X) eq dim;
	assert IsSingular(X) eq false;
	// We now check the equations for X rigorously, i.e.
	// up to the Sturm bound.
	indexGam:=N*&*[Rationals() | 1+1/p : p in PrimeDivisors(N)];	
	indexGam:=Integers()!indexGam; // Index of Gamma_0(N) in SL_2(Z)
	for eqn in eqns do
		eqnScaled:=LCM([Denominator(c) : c in Coefficients(eqn)])*eqn;
		wt:=2*Degree(eqn); // Weight of eqn as a cuspform.
		hecke:=Ceiling(indexGam*wt/12);  // Hecke=Sturm bound.
										// See Stein's book, Thm 9.18.
		Bexp1:=[qExpansion(S.i,hecke+10) : i in [1..dim]]; // q-expansions
                        // of basis for S 
                        // up to precision hecke+10.
		assert Valuation(Evaluate(eqnScaled,Bexp1)) gt hecke+1;
	end for; // We have now checked the correctness of the equations for X.
	Z:=SmallModularCurve(n); 
	KZ:=FunctionField(Z);
	qEZ:=qExpansionsOfGenerators(n,L,prec); // This gives gives qExpansions of the generators
						// of the function field of Z=X_0(n) as Laurent series in q. 
	KX:=FunctionField(X);
	KXgens:=[KX!(R.i/R.dim) : i in [1..(dim-1)]] cat [KX!1]; // The functions x_i/x_dim as elements of the function field of X.
	coords:=[]; // This will contain the generators of the function field of Z as element of the function of X.
	for u in qEZ do
		//We want to express u as an element of the function field of X=X_0(N).
		Su:={};
		d:=0;
		while #Su eq 0 do
			d:=d+1;
			mons:=MonomialsOfDegree(R,d);
			monsq:=[Evaluate(mon,Bexp) : mon in mons];
			V:=VectorSpace(Rationals(),2*#mons);
			W:=VectorSpace(Rationals(),prec-10);
			h:=hom<V->W | 
				[W![Coefficient(monsq[i],j) : j in [1..(prec-10)]] : i in [1..#mons]] 
				cat  [ W![Coefficient(-u*monsq[i],j) : j in [1..(prec-10)]  ]  : i in [1..#mons] ]>;
			K:=Kernel(h);
			for a in [1..Dimension(K)] do
				num:=&+[Eltseq(V!K.a)[j]*mons[j] : j in [1..#mons] ];
				denom:=&+[Eltseq(V!K.a)[j+#mons]*mons[j] : j in [1..#mons] ];
				numK:=Evaluate(num,KXgens); 
				denomK:=Evaluate(denom,KXgens);
				if numK ne KX!0 and denomK ne KX!0 then
					Su:=Su join {numK/denomK};
				end if;
			end for;
		end while;
		assert #Su eq 1;
		coords:=coords cat SetToSequence(Su);
	end for;
	phi:=map<X -> Z | coords cat [1]>;
	jd:=Pullback(phi,jFunction(Z,n));
		P:=AmbientSpace(X);
		R:=CoordinateRing(P);
		assert Rank(R) eq dim;
		num:=Numerator(FunctionField(P)!jd);
		denom:=Denominator(FunctionField(P)!jd);
		num:=Evaluate(num,[R.i : i in [1..(dim-1)]]);
		denom:=Evaluate(denom,[R.i : i in [1..(dim-1)]]);
		deg:=Max([Degree(num),Degree(denom)]);
		num:=Homogenization(num,R.dim,deg);
		denom:=Homogenization(denom,R.dim,deg);
		assert Evaluate(num,KXgens)/Evaluate(denom,KXgens) eq jd;	
		// We compute the degree of j : X_0(N) --> X(1) using the formula
		// in Diamond and Shurman, pages 106--107.
		assert N gt 2;
		dN:=(1/2)*N^3*&*[Rationals() | 1-1/p^2 : p in PrimeDivisors(N)];
		dN:=Integers()!dN;
		degj:=(2*dN)/(N*EulerPhi(N));
		degj:=Integers()!degj; // Degree j : X_0(N)-->X(1)
		degjd:=&+[-Valuation(jd,P)*Degree(P) : P in Poles(jd)];
		assert degj eq degjd;
		// Now if j \ne jd then the the difference j-jd is a rational
		// function of degree at most 2*degj (think about the poles).
		// Hence to prove that j=jd all we have to check is that their
		// q-Expansions agree up to 2*degj+1.
		jdExpansion:=Evaluate(num,Bexp)/Evaluate(denom,Bexp);
		jdiff:=jdExpansion-jInvariant(q);
		assert Valuation(jdiff) ge 2*degj+1; // We have proven the corrections of the
										// j-map jd on X_0(N).
	// Next we want to write down the matrices for the Atkin-Lehner
	// operators on X_0(N)
	alindices:=[ m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
	al:=[AtkinLehnerOperator(S,m) : m in alindices];
	return X, Z, phi, jd, al, <num,denom>;
end function;



//load "modEqns.m";  // For the equations of modular curves.

//-----------------------------------------------------------
//
// Programs for computing quadratic points on X_0(N)
// which are non-hyperelliptic of genus \ge 3, for which J_0(N)
// has rank 0.
//
//----------------------------------------------------------

// The code is in three sections:
//
// Section 1: Functions for Abelian group theory.
//
// Section 2: Functions for general non-hyperelliptic curves X/\Q 
//	      of genus \ge 3 with Mordell--Weil rank 0.
//
// Section 3 : The Mordell--Weil Sieve, and functions 
// 	       for searching for quadratic points.
//
// Section 4: Functions for writing down all degree 2 effective
//            divisors on X_0(N) under the above assumptions.

//---------------------------------------------------------
//
// Section 1: Functions for Abelian group theory. 
//
//-------------------------------------------------------- 


//                i1       pi1
// Given 0--> C1 -----> A1 -----> B1 -->0
//            |                   |                              
//            phi                mu  
//            |                   |
//            V                   V
//      0--> C2 -----> A2 -----> B2 -->0
//               i2         pi2
// with top and bottom row exact sequence of finite abelian groups
// and phi, mu isomorphisms, is there an isomorphism psi : A1 --> A2
// making the diagram commute?
extenProb:=function(phi,mu,i1,i2,pi1,pi2);
    C1:=Domain(i1);
    C2:=Domain(i2);
    assert C1 eq Domain(phi);
    assert C2 eq Codomain(phi);
    A1:=Domain(pi1);
    A2:=Domain(pi2);
    assert A1 eq Codomain(i1);
    assert A2 eq Codomain(i2);
B1:=Codomain(pi1);
    B2:=Codomain(pi2);
    assert B1 eq Domain(mu);
    assert B2 eq Codomain(mu);
    assert #Kernel(i1) eq 1;
    assert #Kernel(i2) eq 1;
    assert Image(pi1) eq B1;
    assert Image(pi2) eq B2;
    assert Kernel(pi1) eq Image(i1);
    assert Kernel(pi2) eq Image(i2);
    assert #Kernel(phi) eq 1;
    assert #Kernel(mu) eq 1;
    assert #C1 eq #C2;
    assert #B1 eq #B2;
    if #B1 eq 1 then
        // In this case i1 and i2 are isomorphisms.
        return true, hom<A1->A2 | [ i2(phi(a@@i1)) : a in OrderedGenerators(A1)]>;
    end if;
    Q,modC1:=quo< A1 | sub<A1  | [i1(c) : c in OrderedGenerators(C1)]> >;
    Qgens:=OrderedGenerators(Q);
    r:=#Qgens;
	xs:=[q@@modC1 : q in Qgens]; // x1,..xr together with i1(C1) generates A1.
    ys:=[(mu(pi1(x)))@@pi2 : x in xs];
    Zr:=FreeAbelianGroup(r);
    pretau:=hom<Zr->A1 | xs>;
    Astar,j1,j2,pj1,pj2:=DirectSum(Zr,C1); //Z^r x C_1.
    // j1, j2 are the inclusion maps Z^r --> A^*, C_1 --> A^*.
    // pj1, pj2 are the projection maps A^* --> Z^r, A^* --> C_1.
    //tau:=hom<Astar->A1 | [ pretau(pj1(d))+(pj2(d))@@i1 : d in OrderedGenerators(Astar)]>;
    tau:=hom<Astar->A1 | [ pretau(pj1(d))+(pj2(d))@i1 : d in OrderedGenerators(Astar)]>;
    K:=Kernel(tau);
    Kgens:=OrderedGenerators(K);
    s:=#Kgens;
    clist:=[ i2(phi(pj2(Astar!k))) : k in Kgens];
    nlist:=[ Eltseq(pj1(Astar!k)) : k in Kgens];
    Cr,Crinjs,Crprojs:=DirectSum([C2 : i in [1..r]]);
    Cs,Csinjs,Csprojs:=DirectSum([C2 : i in [1..s]]);
    Crgens:=[ [Crprojs[i](delta) : i in [1..r]] : delta in OrderedGenerators(Cr)];
    dotprod:=func<nn,tt | &+[ nn[i]*tt[i] : i in [1..#tt]]>;
	eta:=hom<Cr->Cs | [  &+[ Csinjs[j](dotprod(nlist[j],crgen)) : j in [1..s]   ]      : crgen in Crgens ]  >;
    testelt:=-1*&+[ Csinjs[j]((clist[j]+dotprod(nlist[j],ys))@@i2) : j in [1..s]];
    I:=Image(eta);
    if testelt in I then
        tlist:=testelt@@eta;
        tlist:=[Crprojs[i](tlist) : i in [1..r]];
        presigma:=hom<Zr->A2 | [ys[i]+i2(tlist[i]) : i in [1..r]]>;
        sigma:=hom<Astar->A2 | [presigma(pj1(d))+i2(phi(pj2(d))) : d in OrderedGenerators(Astar)]>;
        psi:=hom<A1->A2 | [ sigma(a@@tau) : a in OrderedGenerators(A1)]>;
        assert #Kernel(psi) eq 1;
        assert #A1 eq #A2; // psi is really an isomorphism.
        assert &and[psi(i1(c)) eq i2(phi(c)) : c in OrderedGenerators(C1)];
        assert &and[mu(pi1(a)) eq pi2(psi(a)) : a in OrderedGenerators(A1)];
        // And it really makes the diagram commutative.
        return true, psi;
    else
        return false;
    end if;
end function;

/*

Derek Holt's example. The extension problem is impossible:

A:=AbelianGroup([2,4,8]);
C1:=sub<A | [A.1,2*A.3]>;
C2:=sub<A | [4*A.3,A.2]>;  
i1:=hom<C1->A | [A!(C1.1),A!(C1.2)]>;
i2:=hom<C2->A | [A!(C2.1),A!(C2.2)]>;
B1,pi1:=quo<A | C1>;
B2,pi2:=quo<A | C2>;
phi:=hom<C1->C2 | [C2.1,C2.2]>;
mu:=hom<B1->B2 | [B2.1,B2.2]>; 
extenProb(phi,mu,i1,i2,pi1,pi2); 
==================================================================

Random example

A:=AbelianGroup([2,4,8]);
C1:=sub<A | [A.1,A.2]>;
C2:=sub<A | [A.1,A.2]>;  
i1:=hom<C1->A | [A!(C1.1),A!(C1.2)]>;
i2:=hom<C2->A | [A!(C2.1),A!(C2.2)]>;
B1,pi1:=quo<A | C1>;
B2,pi2:=quo<A | C2>;
phi:=hom<C1->C2 | [C2.1,-C2.2]>;
mu:=hom<B1->B2 | [-B2.1]>; 
tf,psi:=extenProb(phi,mu,i1,i2,pi1,pi2);
assert tf;
assert &and[psi(i1(c)) eq i2(phi(c)) : c in C1];
assert &and[mu(pi1(b)) eq pi2(psi(b)) : b in A];

*/

// i1 : C --> A1
// i2 : C --> A2
// injective homomorphisms of finite abelian groups.
// Is there an isomomorphism psi: A1 --> A2
// making the triangle commute? 
homExtend:=function(i1,i2);
    assert Domain(i1) eq Domain(i2);
    C:=Domain(i1);
    assert #Kernel(i1) eq 1;
    assert #Kernel(i2) eq 1;
    A1:=Codomain(i1);
    A2:=Codomain(i2);
    if IsIsomorphic(A1,A2) eq false then
            return false;
    end if;
    B1,pi1:=quo<A1 | Image(i1)>;
    B2,pi2:=quo<A2 | Image(i2)>;
    tf,mu1:=IsIsomorphic(B1,B2);
    if tf eq false then
        return false;
    end if;
	phi:=hom<C->C | [c : c in OrderedGenerators(C)]>; // The
    // identity map C-->C.
    mapautB2,autB2:=PermutationRepresentation(AutomorphismGroup(B2));
    for kappa in autB2 do // autB2 is a permutation group that
                        // is isomorphic to the automorphism group of B2.
        eta:=kappa@@mapautB2; // This converts the permutation into an
                            // an automorphism of B2.
        mu:=hom<B1->B2 | [  eta(mu1(b)) : b in OrderedGenerators(B1) ]>;
                        // As kappa runs through the elements of autB2
                        // mu runs through the isomorphisms B1-->B2.
        tf:=extenProb(phi,mu,i1,i2,pi1,pi2);
        if tf then
            return true;
        end if;
    end for;
    return false;
end function;



//---------------------------------------------------------
//
// Section 2: Functions for general non-hyperelliptic curves
//		of genus \ge 3.
//
//-------------------------------------------------------- 

// This code assumes that X/\Q is a non-hyperelliptic
// curve (genus \ge 3) with Mordell-Weil rank 0.

// X is a projective curve over rationals,
// p prime of good reduction,
// D divisor on X,
// This reduces to a divisor on X/F_p.

reduce:=function(X,Xp,D);
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






	
// divs are a bunch of known effective divisors,
// P0 is a base point of degree 1,
// p>2 is a prime of good reduction.
// This determines an abstract abelian group Ksub
// isomorphic to the group spanned by [D-deg(D) P_0] 
// where D runs through the elements of divs.  
// It also returns a subset divsNew such that [[D-deg(D) P_0] : D in divsNew]
// generates the same subgroup.
// It also determines a homomorphism 
// h : \Z^r --> Ksub
// where divsNew=[D_1,..,D_r]
// and h([a_1,..,a_r]) is the image of 
// a_1 (D_1-deg(D_1) P_0)+\cdots + a_r (D_r-deg(D_r) P_0)
// in Ksub.

findGenerators:=function(X,divs,P0,p);
	fn:=func<A,B| Degree(A)-Degree(B)>;
	Sort(~divs,fn); // Sort the divisors by degree.
	assert IsPrime(p);
	assert p ge 3;
	Xp:=ChangeRing(X,GF(p));
	assert IsSingular(Xp) eq false; // Now we know that
	// J_X(Q)-->J_X(\F_p) is injective (we're assuming rank 0).
	C,phi,psi:=ClassGroup(Xp);
	Z:=FreeAbelianGroup(1);
	degr:=hom<C->Z | [ Degree(phi(a))*Z.1 : a in OrderedGenerators(C)]>;
	A:=Kernel(degr); // This is isomorphic to J_X(\F_p).
	Pp0:=reduce(X,Xp,P0);
	divsRed:=[reduce(X,Xp,D) : D in divs];
	divsRedA:=[psi(D-Degree(D)*Pp0) : D in divsRed]; // The image of the divisors in A;
	Ksub1:=sub<A | divsRedA>; // The subgroup of J(\F_p) generated by
							// [D-deg(D)*P_0] with D in divs.	
	// Next we eliminate as many of the divisors as possible
	// while keeping the same image.
	r:=#divs;
	inds:=[i : i in [1..r]];
	i:=r+1;
	repeat
		i:=i-1;
		indsNew:=Exclude(inds,i);
		if sub<A | [divsRedA[j] : j in indsNew]> eq Ksub1 then
			inds:=indsNew;
		end if;
	until i eq 1;
	divsNew:=[divs[j] : j in inds];
	divsRedA:=[divsRedA[j] : j in inds];
	r:=#divsNew;	
	Zr:=FreeAbelianGroup(r);
	h:=hom<Zr->A | divsRedA>;
	Ksub:=Image(h); // Stands from known subgroup.
	assert Ksub eq Ksub1;
	h:=hom<Zr->Ksub | [ Ksub!h(Zr.i) :  i in [1..r] ]>;
	// Restrict the codomain of h so that it is equal to Ksub.
	bas:=[Eltseq(i@@h) : i in OrderedGenerators(Ksub)];
	return h,Ksub,bas,divsNew;
end function;


// Determine the homomorphism from Ksub-->J(F_p)
reduceHom:=function(X,divs,P0,Xp,Ksub,bas);
	C,phi,psi:=ClassGroup(Xp);
	Z:=FreeAbelianGroup(1);
	degr:=hom<C->Z | [ Degree(phi(a))*Z.1 : a in OrderedGenerators(C)]>;
	A:=Kernel(degr); // This is isomorphic to J_X(\F_p).
	Pp0:=reduce(X,Xp,P0);
	divsRed:=[reduce(X,Xp,D) : D in divs];
	r:=#divsRed;
	Zr:=FreeAbelianGroup(r);
	eta:=hom<Zr->A | [psi(D-Degree(D)*Pp0) : D in divsRed]>;
	pi:=hom<Ksub->A | [ eta(Zr!g) : g in bas]>;
	return pi,phi,psi;
end function;

// Determine all possible subgroups A of J(F_p) 
// that contain the image of Ksub-->J(F_p)
// and return the induced injective maps Ksub-->A.
reduceHoms:=function(X,divs,P0,Xp,Ksub,bas);
    C,phi,psi:=ClassGroup(Xp);
    Z:=FreeAbelianGroup(1);
    degr:=hom<C->Z | [ Degree(phi(a))*Z.1 : a in OrderedGenerators(C)]>;
    J:=Kernel(degr); // This is isomorphic to J_X(\F_p).
    Pp0:=reduce(X,Xp,P0);
    divsRed:=[reduce(X,Xp,D) : D in divs];
    r:=#divsRed;
    Zr:=FreeAbelianGroup(r);
    eta:=hom<Zr->J | [psi(D-Degree(D)*Pp0) : D in divsRed]>;
    pi:=hom<Ksub->J | [ eta(Zr!g) : g in bas]>;
    I:=Image(pi);
    Q,mu:=quo<J | I>;
    subs:=Subgroups(Q);
    subs:=[H`subgroup : H in subs];
    subs:=[ sub<J | [g@@mu : g in OrderedGenerators(H) ] cat OrderedGenerators(I)> : H in subs ];
    homs:=[ hom<Ksub -> H | [H!(pi(g)) : g in OrderedGenerators(Ksub)]> : H in subs ];
    return homs;
end function;

// This function uses reduction modulo the primes in prs
// to determine a set of injections Ksub --> A
// such that for one of these injections, A is isomorphic
// to J(\Q), and Ksub --> A is the natural injection.
possibleJList:=function(X,divs,P0,Ksub,bas,prs);
    p:=prs[1];
    hms:=[* reduceHoms(X,divs,P0,ChangeRing(X,GF(p)),Ksub,bas) : p in prs *];
    homs:=hms[1];
    n:=#prs;
    for i in [2..n] do
        homsi:=hms[i];
        homsNew:=homs;
        for h in homs do
            if &and[homExtend(h,hi) eq false : hi in homsi] then
                Exclude(~homsNew,h);
            end if;
        end for;
        homs:=homsNew;
    end for;
    return homs;
end function;


//---------------------------------------------------------
//
// Section 3 : The Mordell--Weil Sieve, and functions 
// 	       for searching for quadratic points.
//
//-------------------------------------------------------- 

// To find all effective degree 2 divisors D
// such that [D-2P0] is in the span of [D^\prime-deg(D^\prime) P0 : D^\prime in Divs].
// Here h, Ksub and bas are as in the output of findGenerators. 
// TOO SLOW! DO NOT USE!!

findDeg2Divisors:=function(X,P0,divs,h,Ksub,bas);
	basis:=[&+[b[i]*divs[i] : i in [1..#b]]  : b in bas];
	basis:=[b-Degree(b)*P0 : b in basis];
	deg2:=[];
	for k in Ksub do
		print k;
		ek:=Eltseq(k);
		assert #ek eq #basis;
		D:=&+[ek[i]*basis[i] : i in [1..#basis]]+2*P0;
		assert Degree(D) eq 2;
		L,phi:=RiemannRochSpace(D);
		if Dimension(L) gt 0 then
			assert Dimension(L) eq 1; // Curve is non-hyperelliptic
									// so the Riemann-Roch space
									// of a degree 2 divisor has dimension 
									// at most 1.
			D:=D+Divisor(phi(L.1));
			assert IsEffective(D);
			deg2:=deg2 cat [D];
		end if;
	end for;
	return deg2;
end function;

// Search for divisors of degree 2
// Given a curve X/\Q as before, and a bound bd and a true/false tf
// this function returns
// deg2,pls1,pls2,plsbig
// Here pls1 is a set of places of degree 1
// pls2 is a set of places of degree 2 and
// plsbig is a set of places of degree at least 3 but less than genus.
// pls1 are found by a search for rational points on X
// pls2, plsbig are found by intersecting hyperplanes with X.
// deg 2 are the known degree 2 effective divisors: sums of pairs of
// elements of pls1, and elements of pls2.
// If tf=true then the automorphism group of X is used
// to enlarge the sets pls1 and pls2 (if possible).

searchDiv2:=function(X,bd,tf);
	g:=Genus(X);
	//
	// First we find degree 1 points
	pts:=PointSearch(X , 1000);
	pls1:={Place(P) : P in pts};
	pls2:={};
	plsbig:={};
	R:=CoordinateRing(AmbientSpace(X));
	n:=Rank(R);
	// Next we intersect X with hyperplanes with coefficients bounded by bd
	// and see what divisors we obtain.
	C:=CartesianPower([-bd..bd],n);
	ctr:=0;
	for a in C do
		ctr:=ctr+1;
		//print #C,ctr,#pls1, #pls2,#plsbig;
		b:=[a[i] : i in [1..n]];
		if &or[b[i] ne 0 : i in [1..n]] then
			if GCD(b) eq 1 and b[1] ge 0 then
				f:=&+[b[i]*R.i : i in [1..n]];
				D:=Divisor(X,ideal<R | f>);
				decomp:=Decomposition(D);
				for pr in decomp do
					P:=pr[1];
					if Degree(P) eq 1 then
						pls1:=pls1 join {P};
					else
						if Degree(P) eq 2 then
							pls2:=pls2 join {P};
						else
							if Degree(P) le g then
								plsbig:=plsbig join {P};
							end if;
						end if;
					end if;
				end for;
			end if;
		end if;
	end for;
	if tf then
		A:=Automorphisms(X); // We will use the automorphisms of X
						// to enlarge the sets pls1, pls2.
		for phi in A do
			for P in pls1 do
				D:=Pullback(phi,P);
				pls1:=pls1 join {Decomposition(D)[1,1]};
			end for;
			for P in pls2 do
				D:=Pullback(phi,P);
				pls2:=pls2 join {Decomposition(D)[1,1]};
			end for;
		end for;
	end if;
	pls1:=SetToSequence(pls1);
	pls2:=SetToSequence(pls2);
	plsbig:=SetToSequence(plsbig);
	deg2:=[];
	for i,j in [1..#pls1] do
		if i le j then
			Append(~deg2,1*pls1[i]+1*pls1[j]);
		end if;
	end for;
	deg2:=deg2 cat [1*P : P in pls2];
	return deg2,pls1,pls2,plsbig;
end function;

// Xp is a projective curve over finite field F_p
// D an degree 2 divisor of Xp
// Write D=d_1 y_1+\cdots+d_r y_r
// where y_i are degree 1 places over an extension.
// Let \omega_1,\dots,\omega_g be a basis for regular differentials.
// This function determines the matrix whose i-th row
// is [a(omega_i,y_1,d_1), a(omega_i,y_2,d_2),...],
// where a(omega_i,y_j,d) is the first d coefficients in the 
// expansion of omega_i around y_j.

matrixDerickx:=function(Xp,D);
	omegas:=BasisOfHolomorphicDifferentials(Xp);
	Fp:=BaseRing(Xp);
	p:=Characteristic(Fp);
	assert IsEffective(1*D);
	assert Degree(D) eq 2;
	decomp:=Decomposition(1*D);
	M:=[];
	if Degree(decomp[1,1]) eq 1 then
		if decomp[1,2] eq 1 then
			P:=decomp[1,1];
			Q:=decomp[2,1];
			t:=UniformizingParameter(P);
			s:=UniformizingParameter(Q);
			dt:=Differential(t);
			ds:=Differential(s);
			for w in omegas do
				a1:=GF(p^2)!Evaluate(w/dt,P);
				a2:=GF(p^2)!Evaluate(w/ds,Q);
				Append(~M,[a1,a2]);
			end for;
		else
			P:=decomp[1,1];
			t:=UniformizingParameter(P);	
			dt:=Differential(t);
			for w in omegas do
				wbydt:=w/dt;
				a1:=Evaluate(wbydt,P);
				a2:=Evaluate((wbydt-a1)/t,P);
				Append(~M,[GF(p^2) | a1,a2]);
			end for;	
		end if;
	else
		P:=decomp[1,1];
		t:=UniformizingParameter(P);
		dt:=Differential(t);
		for w in omegas do
			a:=Evaluate(w/dt,P);
			Append(~M,[a,a^p]);
		end for;	
	end if;
	return Matrix(M);
end function;

// deg2 are the known elements of X^{(2)}(\Q) 
// This function determines a subset of X^{(2)}(\F_p) 
// such that the reduction of any unknown element of X^{(2)}(\Q)
// is contained in this set. 
missingImage:=function(X,deg2,Xp);
	plsp1:=Places(Xp,1);
	plsp2:=Places(Xp,2);
	degp2:=[];
	for i,j in [1..#plsp1] do
		if i le j then
			Append(~degp2,1*plsp1[i]+1*plsp1[j]);
		end if;
	end for;
	degp2:=degp2 cat [1*P : P in plsp2]; // X^{(2)}(\F_p)
	redImage:={reduce(X,Xp,D) : D in deg2};
	formalImmersion:=[D : D in redImage | Rank(matrixDerickx(Xp,D)) eq 2]; 
	// These are the residue classes in X^{(2)} which contain
	// a rational point and we know from the Derickx formal immersion criterion
	// that there is no other rational points.
	return [D : D in degp2 | D in formalImmersion eq false],formalImmersion,redImage,degp2;		
end function;

// Assume that I*J(\Q) is contained in Ksub.
// prms is a set of primes of > 2 of good reduction.
// This returns a set of effective divisors of degree 2*I
// such that if D is a degree 2 rational divisor on X not 
// belonging to deg2 (i.e. an unknown degree 2 divisor)
// then I*D is linearly equivalent to one of these divisors.
MWSieve:=function(X,deg2,divs,P0,h,Ksub,bas,prms,I);
	miss:={k : k in Ksub};
	for p in prms do
		assert IsPrime(p);
		assert p ge 3;
		Xp:=ChangeRing(X,GF(p));
		assert IsSingular(Xp) eq false; // Now we know that
		// J_X(Q)-->J_X(\F_p) is injective (we're assuming rank 0).
		missp:=missingImage(X,deg2,Xp);
		pip,_,psip:=reduceHom(X,divs,P0,Xp,Ksub,bas);
		piIm:=Image(pip);
		assert #Kernel(pip) eq 1;
		Pp0:=reduce(X,Xp,P0);
		missp:=[ I*psip(D-Degree(D)*Pp0) : D in missp];	
		missp:=[ C : C in missp | C in piIm];	
		missp:={ C@@pip : C in missp};
		miss:=miss meet missp;
		//print #miss;	
	end for;
	miss:=[Eltseq(m@@h) : m in miss];
	miss:=[&+[d[i]*(divs[i]) : i in [1..#divs]] : d in miss ];
	miss:=[ D-(Degree(D)-2*I)*P0 : D in miss];
	missNew:=[];
	for D in miss do
		if IsEffective(D) then
			Append(~missNew,D);
		else
			L,eta:=RiemannRochSpace(D);
			if Dimension(L) gt 0 then
				Append(~missNew,D+Divisor(eta(L.1)));
			end if;
		end if;
	end for;
	return missNew;
end function;



//---------------------------------------------------------
//
// Section 4: Functions for writing down all degree 2 effective
//            divisors on X_0(N) under the above assumptions.
//
//-------------------------------------------------------- 


// If P is a degree 2 place on X/\Q
// then this returns squarefree D such
// that Q(\sqrt{D}) is the class field of P.
discQuadPlace:=function(P);
	assert Degree(P) eq 2;
	K:=ResidueClassField(P);
    D:=Discriminant(MaximalOrder(K));
    if IsDivisibleBy(D,4) then
           D:=D div 4;
    end if;
	return D;
end function;

discsQuadPlaces:=function(pls2);
	disclist:=[discQuadPlace(P) : P in pls2];
	disclist:=Sort(SetToSequence(Set(disclist)));
	return disclist;
end function;

graphQuadPlaces:=function(X,N,al,numdenom,pls2,D);
	pls:=[P : P in pls2 | discQuadPlace(P) eq D];
	K<t>:=QuadraticField(D);
	alK:=[Matrix(NumberOfRows(M),NumberOfColumns(M),[K!a : a in Eltseq(M)]) : M in al];
	XK:=ChangeRing(X,K);
	RK<[x]>:=CoordinateRing(AmbientSpace(XK));
	dim:=Rank(RK);
	numK:=Evaluate(numdenom[1], [RK.i : i in [1..dim]]);
	denomK:=Evaluate(numdenom[2], [RK.i : i in [1..dim]]);
	KXK:=FunctionField(XK);
    	KXgens:=[KXK!(x[i]/x[dim]) : i in [1..(dim-1)]] cat [KXK!1];
	jinvXK:=Evaluate(numK,KXgens)/Evaluate(denomK,KXgens);	
	pts:=[];
	for P in pls do
		PP:=Eltseq(RepresentativePoint(P));
		LP:=Universe(PP);
		tf,i:=IsIsomorphic(LP,K);
		assert tf;
		PP:=[i(a) : a in PP];
		Append(~pts,XK!PP);
	end for;	
	ptsConj := [ XK![ Conjugate(a) : a in Eltseq(PP) ]	: PP in pts ];	
	assert #(Set(pts) meet Set(ptsConj)) eq 0;
	assert #Set(pts) eq #pts;
	assert #Set(ptsConj) eq #ptsConj;
	alindices:=[ m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
	assert #alindices eq #alK;
	graph:=[];
	for i in [1..#pts] do
		PP:=pts[i];
		for k in [1..#alK] do
			m:=alindices[k];
			wm:=alK[k];
			PPwm:=XK!(Eltseq(Vector(Eltseq(PP))*Transpose(wm)));
			tf1:=PPwm in pts;	
			tf2:=PPwm in ptsConj;
			assert tf1 xor tf2;
			if tf1 then
				j:=[j : j in [1..#pts] | PPwm eq pts[j]][1];
				Append(~graph,<i,j,m,0>);
			end if;
			if tf2 then
				j:=[j : j in [1..#ptsConj] | PPwm eq ptsConj[j]][1];
				Append(~graph,<i,j,m,1>);
			end if;
		end for;
	end for;		
	return pts, ptsConj, [Evaluate(jinvXK,Place(P)) : P in pts], graph;
end function;

// This a programme to compute the effective degree 2 divisors on X_0(N)
// assuming that J_0(N) has analytic rank 0
// and that X_0(N) is non-hyperelliptic of genus at least 3.
// Here n is some divisor of N such that the equations for X_0(n)
// is in the "Small Modular Forms Database".
// UB is an upper bound for the primes used in the Mordell--Weil sieve.
// mw is an optional input. The default is [] which means that the 
// Mordell--Weil group is unknown. If the Mordell--Weil group
// is known it should be given in the form of mw:=[d_1,d_2,..,d_r];
// which stands for Z/d_1\oplus \cdots \oplus \Z/d_1.
	
// The output is:
// X,jinvN,I,Ksub,cusps,deg2,degtwoI,pls1,pls2;
// X is a model for X_0(N) as smooth curve in projective space,
// jinvN is the j-map as an element of the function field of X,
// I is a positive integer such that I*J_X(\Q) is contained
// in the cuspidal subgroup,
// Ksub is an abstract abelian group isomorphic to the rational cuspidal subgroup,
// quos is a list of possibilities for J_X(\Q) as an abstract abelian group,
// cusps is a list of the cusp places on X,
// deg2 is a list of effective degree 2 divisors on X,
// degtwoI is a list of effective degree 2I divisors on X.
// If degtwoI is empty then deg2 is the list of ALL effective degree 2 
// divisors on X.
// In general, if D is an effective degree 2 divisor not in deg2
// then I*D is linearly equivalent to some element of degtwoI.
// pls1 is a list of places of degree 1, 
// and pls2 is a list of places of degree 2.
// These will be complete if degtwoI is empty.



quadPts:=function(N,n,UB : vb:=true, mw:=[], search:=true); 
	// vb is a verbose flag.
	// If it is set to true it will print intermediate steps.
	// If search is set to true, the command will search
	// for additional degree 2 divisors using the command
	// searchDiv2 
	if vb then
		print "N=", N;
	end if;
	L:=LSeries(JZero(N));
	l,v:=LeadingCoefficient(L,1,10);
	assert v eq 0;
	if vb then
		print "checked that the analytic rank of J_0(N) is zero";
	end if;
	// The analytic rank of J_0(N) is 0, therefore the Mordell--Weil group of J_0(N) is torsion.
	//
	//
	X,Z,phi,jinvN,al,numdenom:=modeqns(N,n); // This command is from the file "modEqns.m";
	if vb then
		print "X_0(N) is the curve", X, "with genus", Genus(X);
	end if; 
	 // X=X_0(N)
 	// Z=X_0(n)
	// and phi : X --> Z is the degeneracy map
	// jinvN is the j-function as an element of the function field of X. 
	//
	//
	// We construct the cusps on X_0(N)
	cusps:=Poles(jinvN);
	if vb then
		print "Thus cusps are these places", cusps;
	end if;
	// Sanity check!
	cuspDegrees:=[EulerPhi(GCD(m,N div m)) :  m in Divisors(N)];  // The cusp degrees as predicted by theory.
	assert Sort(cuspDegrees) eq Sort([Degree(d) : d in cusps]); // The degrees of the cusps we have found agree with theory.
	cusps1:=[P : P in cusps | Degree(P) eq 1];
	assert #cusps1 ge 2; 
				// There are always at least two cusps 
				// of degree 1 corresponding to the
				// factors 1 and N of N.
	P0:=cusps1[1]; // This will our base for the Abel-Jacobi map.
	if vb then
		print "The base point for the Abel-Jacobi map is", P0;
	end if;
	cusps2:=[P : P in cusps | Degree(P) eq 2]; 
	deg2:=[cusps1[i]+cusps1[j] : i,j in [1..#cusps1] | i le j] cat [1*P : P in cusps2];
	// These are the degree 2 divisors we know from the cusps.
	if vb then
		print "There are", #deg2, "effective degree 2 divisors that are composed of cusps";
	end if;
	p0:=3;
	while IsDivisibleBy(N,p0) do
		p0:=NextPrime(p0);
	end while;
	// Now p0 will be an odd prime of good reduction for X_0(N).
	h,Ksub,bas,divs:=findGenerators(X,cusps,P0,p0);
	if mw ne [] then
		MW:=AbelianGroup(mw);
		assert IsIsomorphic(MW,Ksub);
		print "The given Mordell--Weil group is indeed isomorphic to
				the cuspidal subgroup.";
	end if; 
	if vb then
		print "The cuspidal group is isomorphic to", Ksub;
	end if;
	// Here Ksub is an abstract group isomorphic to the
	// subgroup of J(\Q) generated by [D-degree(D)*P0 : D in cusps] (i.e. the cuspidal subgroup).
	// divs is a subset of cusps that generates the same group.
	// h is the homomorphism \Z^r-->Ksub where r=#divs
	// and i-th standard basis vector is mapped to the image of
	// D-degree(D)*P0 where D=cusps[r].
	// bas is a subset of \Z^r which maps to a basis of Ksub
	// and is therefore (morally) a basis for the cuspidal  
	// subgroup of J(\Q).
	prs:=[p : p in PrimesInInterval(3,UB) | IsDivisibleBy(N,p) eq false];
	if mw eq [] then
		homs:=possibleJList(X,divs,P0,Ksub,bas,prs);
		// homs is a list of injective homomorphisms
		// with domain Ksub such that for one
		// of them the codomain is isomorphic to J(\Q).
		assert &and[Domain(h) eq Ksub : h in homs];
		assert &and[#Kernel(h) eq 1 : h in homs];
		quos:=[quo<Codomain(h) | Image(h)> : h in homs];
		if vb then
			print "The possibilities for J(Q)/C are", quos;
		end if;
		I:=LCM([Exponent(Q) : Q in quos]);  // I*J(\Q) belongs to the cuspidal.
	else
		quos:=[AbelianGroup([1])];
		I:=1;
	end if;
	if vb then
		print "I*J(Q) is contained in the cuspidal subgroup where I=", I;
	end if;
	if search then
		deg2New:=searchDiv2(X,1,false); // Searching for degree 2 effective divisors.
		deg2New:=[D : D in deg2New | D in deg2 eq false];
		if vb then
			if #deg2New gt 0 then
				print "A search found", #deg2New, "new effective degree 2 divisors.";
			end if;
		end if;
		deg2:=deg2 cat deg2New;
	end if;
	deg2New:=MWSieve(X,deg2,divs,P0,h,Ksub,bas,[p0],1);
	// Trying to find additional degree 2 divisors by sieve modulo p0.
	deg2New:=[D : D in deg2New | D in deg2 eq false];
	if vb then
		if #deg2New gt 0 then
			print "The Mordell--Weil sieve found", #deg2New, "new effective degree 2 divisors.";
		end if;
	end if;
	deg2:=deg2 cat deg2New;
	if vb then
		print "The following is a list of degree 2 effective divisors D
			such that [D-2P_0] belongs to the cuspidal subgroup";
		print deg2;
	end if;
	degtwoI:=MWSieve(X,deg2,divs,P0,h,Ksub,bas,prs,I);
	// This uses the Mordell--Weil sieve (with primes in prs) 
	// to return a set of effective divisors of degree 2*I 
	// such that if D is an effective degree 2 divisor not
	// in deg2 then I*D is linearly equivalent to some element of degtwoI.
	if #degtwoI eq 0 then
		print "succeeded in determining all effective divisors of degree 2";
		//pls:=[pr[1] : pr in &cat[Decomposition(D) : D in deg2]];
		//pls1:=SetToSequence(Set([D : D in pls | Degree(D) eq 1]));
		//pls2:=SetToSequence(Set([D : D in pls | Degree(D) eq 2]));
		//return X,jinvN,I,Ksub,S,cusps,deg2,degtwoI,pls1,pls2;
	else
		print "if D is an unknown effective divisor of degree 2 then I*D is equivalent to one of the list:", degtwoI;
		degtwoINew:=degtwoI;
		for i in [1..#degtwoI] do
			D:=degtwoI[i];
			assert IsEffective(D);
			assert Degree(D) eq 2*I;
			L,phi:=RiemannRochSpace(D);
			assert Dimension(L) ge 1; // As D is effective.
			if Dimension(L) eq 1 then
				print "For the", i, "-th divisor the RR space has dimension 1
								and we can simply divide by I";
				assert Divisor(phi(L.1)) eq D!0;
				decomp:=Decomposition(D);
				if &and [IsDivisibleBy(d[2],I) : d in decomp] then
					DoverI:=&+[(d[2] div I)*d[1] : d in decomp ];		 	
					if DoverI in deg2 eq false then
						Append(~deg2,DoverI);
					end if;
				end if;
				Exclude(~degtwoINew,D);
			else	//Dimension(L) at least 2.
				if Dimension(L) ge 3 then
					print "For the", i, "-th divisor the RR space 
							has dimension", Dimension(L);
					print "This case is not programmed yet.";
				else
					ID:=Ideal(D);
					B:=Basis(ID);
					Qalpha<alpha>:=FunctionField(Rationals());
					Xalpha:=ChangeRing(X,Qalpha);
					Ralpha:=CoordinateRing(AmbientSpace(Xalpha));
					IDalpha:=ideal< Ralpha | [Ralpha!f : f in B]>;	
					Dalpha:=Divisor(Xalpha,IDalpha);
					L,phi:=RiemannRochSpace(Dalpha);
					assert Dimension(L) eq 2;
					f1:=phi(L.1);
					f2:=phi(L.2);
					D1:=Dalpha+Divisor(f1+alpha*f2);
					decomp:=Decomposition(D1);
					assert #decomp eq 1;
					assert decomp[1,2] eq 1;
					Palpha:=decomp[1,1];
					assert Degree(Palpha) eq 2*I;
					Falpha:=ResidueClassField(Palpha);
					falpha:=MinimalPolynomial(Falpha.1);
					if Degree(falpha) lt 2*I then
						falpha:=Norm(falpha); // In this case the residue class field of Palpha
									// is an extension of an extension of Qalpha.
					end if;
					assert Degree(falpha) eq 2*I;
					disc:=PolynomialRing(Rationals())!Numerator(Discriminant(falpha)); 
					// This discriminant must vanish
					// at the values of alpha where D1 is I*divisor. 
					rts:=[r[1] : r in Roots(disc)];
					if  #rts gt 0 then // If there are no roots in \Q, then D1 is not
						// I*(effective divisor) for any (finite) value of alpha.
						for r in rts do
							E:=Dalpha+Divisor(f1+r*f2);
							assert &and[IsDivisibleBy(pr[2],I) : pr in Decomposition(E)] eq false;
							// Therefore E is not I*(effective divisor).
						end for;	
					end if;
					// We next have to do the same of alpha=infty (projectively speaking).
					E:=Dalpha+Divisor(f2);
					assert &and[IsDivisibleBy(pr[2],I) : pr in Decomposition(E)] eq false;
					// Therefore E is not I*(effective divisor).
					print "Succeeded in eliminating one of the divisors.";
					Exclude(~degtwoINew,D);	
				end if;
			end if;
		end for;		
		degtwoI:=degtwoINew;
		if #degtwoI eq 0 then
			print "Succeeded in determining all effective divisors of degree 2.";
		else
			print "There are still", #degtwoI, "divisors of degree", 2*I, "we cannot eliminate.";
		end if;
	end if;
	print "We know", #deg2, "effective degree 2 divisors";
	pls:=[pr[1] : pr in &cat[Decomposition(D) : D in deg2]];
	pls1:=SetToSequence(Set([D : D in pls | Degree(D) eq 1])); // Places of degree 1.
	pls2:=SetToSequence(Set([D : D in pls | Degree(D) eq 2])); // Places of degree 2.
	print "++++++++++++++++++++++++++++++++++++++++++++++++++";
	print "We now print the places of degree 1 and their j-invariants,
			and whether or not they are CM";
	for P in pls1 do
		if Valuation(jinvN,P) lt 0 then
			print P, "is a cusp.";
		else
			j:=Evaluate(jinvN,P);
			E:=EllipticCurveWithjInvariant(j);
			print P,j,HasComplexMultiplication(E);
		end if;
		print "+++++++++++++++++++++++++++++++";
	end for;
	print "We now print the places of degree 2 and their j-invariants,
			and whether or not they are CM";
	for P in pls2 do
		if Valuation(jinvN,P) lt 0 then
			print P, "is a cusp.";
		else
			K:=ResidueClassField(P);
			D:=Discriminant(MaximalOrder(K));
			if IsDivisibleBy(D,4) then
				D:=D div 4;
			end if;	
			L<t>:=QuadraticField(D);
			j:=Evaluate(jinvN,P);
			M:=MinimalPolynomial(j);
			rts:=Roots(M,L);
			assert #rts ge 1;
			j:=rts[1,1];
			E:=EllipticCurveWithjInvariant(j);
			print "The place P is defined over", L;
			print "The j-invariant is", j;
			print HasComplexMultiplication(E);
			print "++++++++++++++++++++++++++";
		end if;
		pls2NonCusp:=[ P : P in pls2 | Valuation(jinvN,P) ge 0];
		disclist:=discsQuadPlaces(pls2NonCusp);
	end for;
	for D in disclist do
		print "Considering points defined over Q(sqrt(D)) where D=", D;
		pts,ptsConj,jinvs, graph:=graphQuadPlaces(X,N,al,numdenom,pls2NonCusp,D);
		print pts, ptsConj, jinvs, graph;
		print "+++++++++++++++++++++++++++++++++++";
	end for;
	return X,jinvN,I,Ksub,quos,cusps,deg2,degtwoI,pls1,pls2;
end function;	



