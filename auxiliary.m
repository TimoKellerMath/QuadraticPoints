load "rank_0_auxiliary.m";

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
