X := X0NQuotient(74, [37]);
pts := PointSearch(X, 10);
r := 2;

for p in [p : p in PrimesUpTo(100) | p notin {2,37}] do
    Xp := ChangeRing(X, GF(p));
    ptsp := [Xp!ChangeUniverse(Eltseq(pt), GF(p)) : pt in pts]; // reductions of Q-points

    PicXp, phi, psi := ClassGroup(Xp);
    JFp := TorsionSubgroup(PicXp);
    goodells := PrimeDivisors(GCD(AbelianInvariants(JFp)));

    divsp := [psi(Place(ptsp[i]) - Place(ptsp[1])) : i in [2..#ptsp]];
    mat := Matrix(Integers(), #divsp, #AbelianInvariants(JFp), [Eltseq(JFp ! D) : D in divsp]);
    if exists(ell){ell : ell in goodells | Rank(ChangeRing(mat, GF(ell))) ge r} then
        printf "p = %o: J(F_p) = %o; ell = %o\n", p, JFp, ell;
        break;
    end if;
end for;