// The functions in this file are auxiliary files used for the rank 0 method
// some functions are also used for the AL sieve method.

// The functions in this file are copied from the accompanying files of the paper
// Ozman--Siksek, Quadratic Points on Modular Curves
// The original files are available here: https://arxiv.org/abs/1806.08192
// We have adapted the code in one or two places to make use of the is_nonsing_p function from models_and_maps.m
// which verifies nonsingularity mod p much more quickly than the inbuilt Magma function

//////////////////////////////////////////
//////////////////////////////////////////

load "models_and_maps.m";

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

//////////////////////////////////////////
//////////////////////////////////////////

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

//////////////////////////////////////////
//////////////////////////////////////////

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

findGenerators:=function(X,N,divs,P0,p);
	fn:=func<A,B| Degree(A)-Degree(B)>;
	Sort(~divs,fn); // Sort the divisors by degree.
	assert IsPrime(p);
	assert p ge 3;
	Xp:=ChangeRing(X,GF(p));
	assert is_nonsing_p(X,N,p,[]); // Now we know that
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

//////////////////////////////////////////
//////////////////////////////////////////

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

//////////////////////////////////////////
//////////////////////////////////////////

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

rank_0_sieve:=function(X,N,deg2,divs,P0,h,Ksub,bas,prms,I);
	miss:={k : k in Ksub};
	for p in prms do
		assert IsPrime(p);
		assert p ge 3;
		Xp:=ChangeRing(X,GF(p));
		assert is_nonsing_p(X,N,p,[]); // Now we know that
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
