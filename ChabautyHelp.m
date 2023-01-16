//for a given divisor D in Jp = J(Xp) and Atkin-Lehner operator (w_N) matrix AL_mat, calculates (1 - w_N)(D), mod p

OneMinusWmodp := function(Xp, D, AL_mat, p)
	RRp<[up]> := CoordinateRing(AmbientSpace(Xp));
	np := Dimension(AmbientSpace(Xp));

	Hp := ChangeRing(AL_mat, GF(p));
	rows_p := [[&+[RowSequence(Hp)[i][j]*up[j] : j in [1..np+1]] : i in [1..np+1]]];
	wp := iso<Xp -> Xp | rows_p, rows_p>;

	decomp := Decomposition(D);
	retD := D;

	for i in [1..#decomp] do
		repPt := RepresentativePoint(decomp[i][1]);
		retD := retD - decomp[i][2]*Place(wp(repPt));
	end for;

	return retD;
end function;


//This function verifies the conditions of Theorem 2.1 from Box - quadratic points on modular curves
//Input: degree 2 divisor QQ, prime p of good reduction for X,
//AtkinLehner matrix on X, genus of X/<AtkinLehner>

IsLonely := function(QQ, p, X, AtkinLehner, genusC)
	// Condition in Theorem is p > 2
	if p eq 2 then
		return false;
	end if;

	ptlist := [];
	d := 2; // Just there to emphasize that we work on X^{(d)} for d = 2.

	// We now distinguish between a pair of rational points and a quadratic point
	if #Decomposition(QQ) eq 1 then //Quadratic point or double rational point case
		Q := Decomposition(QQ)[1][1];
		if not IsIsomorphic(ResidueClassField(Q),Rationals()) then //Quadratic point case
			dd := [1, 1]; //This encodes that QQ = Q_1 + Q_2 with Q_1 and Q_2 distinct
			disc := discQuadPlace(Q);
			K := QuadraticField(disc); //The quadratic field over which QQ is defined
			F := ResidueClassField(Q);
			tf, ii := IsIsomorphic(F, K);
			assert tf; //Sanity check
			Q := [ii(x) : x in Eltseq(RepresentativePoint(Q))]; 
			conjQ := [Conjugate(x) : x in Q];
			Append(~ptlist, Q);
			Append(~ptlist, conjQ);
		else
			dd := [2]; //Double rational point case
			K := RationalsAsNumberField();
			Q := [K!a : a in Eltseq(RepresentativePoint(Q))];
			Append(~ptlist, Q);
		end if;
	else
		dd := [1, 1]; //Two distinct rational points case
		K := RationalsAsNumberField();
		ptlist := [Eltseq(RepresentativePoint(Decomposition(QQ)[1][1])), Eltseq(RepresentativePoint(Decomposition(QQ)[2][1]))];
		ptlist := [[K!a : a in pt] : pt in ptlist];
	end if;

	OK := RingOfIntegers(K); //K is the number field over which Q_1, Q_2 are defined
	dec := Factorization(p*OK);
	pp := dec[1][1]; //A prime of K above p
	f := InertiaDegree(pp);

	//Condition in theorem
	if p eq 3 and f eq 1 then
		return false;
	end if;

	Fp, pi := ResidueClassField(pp);
	Xp := ChangeRing(X, Fp);
	Rp<[u]> := CoordinateRing(AmbientSpace(Xp));
	n := Dimension(AmbientSpace(X)); //Assuming X is given in projective space
	
	// mod p Atkin-Lehner involution
    row := [&+[RowSequence(AtkinLehner)[i][j]*u[j] : j in [1..n+1]] : i in [1..n+1]];
    wp := iso<Xp -> Xp | row, row>;

	//We find the space of vanishing differentials (T)
	V, phi := SpaceOfDifferentialsFirstKind(Xp);
	tp := hom<V -> V | [ (Pullback(wp, phi(V.i)))@@phi - V.i : i in [1..Genus(X)] ]>;
	T := Image(tp);

	//check that dimesion of space of annihilating differentials is as expected
	assert Dimension(T) eq Genus(X) - genusC;

	omegas := [phi(T.i) : i in [1..Dimension(T)]]; //A basis of vanishing differentials
	unif := UniformizingElement(pp);
	matrixseq := [];

	KA, K_to_KA := AlgorithmicFunctionField(FunctionField(Xp));

	//We now construct the matrix Atilde from Theorem
	for pt in ptlist do 
		printf ".";
		m := Minimum([Valuation(a, pp) : a in pt | not a eq 0]);
		Qred := [unif^(-m)*a : a in pt]; 
		Qtilde := Xp![Evaluate(a, Place(pp)) : a in Qred]; //The mod p reduction of Q
		tQtilde := UniformizingParameter(Qtilde);
		
		funs := [K_to_KA(omega/Differential(tQtilde)) : omega in omegas];
		func_tQtilde := K_to_KA(tQtilde);
		place := FunctionFieldPlace(Place(Qtilde));
		values := [Evaluate(fun, place) : fun in funs];
		Append(~matrixseq, values);
		if dd eq [1, 1] then
			//Append(~matrixseq, [(omega/Differential(tQtilde))(Qtilde) : omega in omegas]);
		else 
			//Append(~matrixseq, [(omega/Differential(tQtilde))(Qtilde) : omega in omegas]);
			Append(~matrixseq, [Evaluate((funs[i] - KA!values[i])/func_tQtilde, place) : i in [1..#funs]]); 
			//Append(~matrixseq, [((omega/Differential(tQtilde) - (omega/Differential(tQtilde))(Qtilde))/tQtilde)(Qtilde) : omega in omegas]); 
		end if;
	end for;

	Atilde:=Matrix(matrixseq);

	if Rank(Atilde) eq d then
		return true;
	else
		return false;
	end if;
end function;
