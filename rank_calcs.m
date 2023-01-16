///////////////////
/// simple_rank ///
///////////////////

// Input : A
// A is a simple modular abelian variety that appears as a factor of J_0(N)

// Ouput : Rank(A), tf
// Rank(A) and whether this is provably true.
// If the second output is false then Rank(A) will be -1000

simple_rank := function(A);
    tf := true;
    if Dimension(A) eq 0 or IsZeroAt(LSeries(A),1) eq false then
       rk := 0;
    else M := ModularSymbols(Newform(A));
         _,ord_vanishing := LSeriesLeadingCoefficient(M,1,100);
         if ord_vanishing eq 1 then
            rk := Degree(HeckeEigenvalueField(M));
         else if Dimension(A) eq 1 then   // we have an elliptic curve and we try to compute the rank directly
                 E := EllipticCurve(A);
                 rk,ell_tf := Rank(E);
                 assert ell_tf eq true;
              else rk := -1000;
                   tf := false;
              end if;
          end if;
    end if;
    return rk, tf;
end function;

////////////////////////////////////////////////////
////////////////////////////////////////////////////

////////////////
/// rank_quo ///
////////////////

// Input: N, sequence of AL indices which generates a group W
// Ouput: Rank(J_0(N)) / W, tf
// Rank and whether it is provably true
// If the second output is false then the rank will be -1000

// if you want to compute the rank of J_0(N) (without quotienting) then take empty sequence

rank_quo := function(N,seq_al);
    J := JZero(N);
    if #seq_al gt 0 then
        J_quo := Image(&*[1+AtkinLehnerOperator(J,i) : i in seq_al]);
    else J_quo := J;
    end if;
    dec := Decomposition(J_quo);
    rk := 0;
    tf := true;

    for A in dec do
        rkA, Atf := simple_rank(A);
        if Atf eq false then  // cannot compute rank with simple_rank
           rk := -1000;
           tf := false;
           break;
        else rk := rk + rkA;
        end if;
     end for;

     return rk, tf;
end function;


////////////////////////////////////////////////////
////////////////////////////////////////////////////
      
//////////////////
/// equal_rank ///
//////////////////

// Input: N, seq_al.
// N is the level
// seq_al is sequence of AL indices which generates a group W

// Output: true true, false true, or false, false

// true true if the ranks of J_0(N) and J_0(N) / W are equal and this is provably correct
// false true if the ranks of J_0(N) and J_0(N) / W are not equal and this is provably correct
// false false if we cannot verify whether or not the ranks of J_0(N) and J_0(N) / W are equal

// This code provides an alternative way of checking the equality of ranks. 
// It is of course possible to compute the rank of J0N and the quotient using the code above and checking whether they are equal.
// This code works with different simple abelian varieties, so may work even if computing the ranks separately fails 
// (but not vice-versa, if this code fails then computing the rank of J0N will also fail)

equal_rank := function(N,seq_al);
    J := JZero(N);  
    if seq_al eq [] then 
        return true, true;
    end if;
    J_min := ConnectedKernel(&*[1+AtkinLehnerOperator(J,i) : i in seq_al]);  
    dec := Decomposition(J_min);

    for A in dec do  // simple factors of minus part
        rkA, tfA := simple_rank(A);
        if rkA gt 0 and tfA eq true then // there is a positive rank factor in J_min
           return false, true;
        elif tfA eq false then 
           return false, false;
        end if;
    end for;
    return true, true;
end function;



/*
// A few examples

rank_quo(74, []); // 2 true. So the rank of J_0(74) is 2
rank_quo(74, [74]); // 1 true. So the rank of J_0+(74) is 1
rank_quo(74, [37]); // 2 true.
rank_quo(74, [2]); // 1 true.
// The following four lines all compute the rank of the quotient by the full AL group
rank_quo(74, [2,37]); // 1 true
rank_quo(74, [37,74]);
rank_quo(74, [2,74]);
rank_quo(74, [2,37,74]);

equal_rank(74,[74]); // false true
equal_rank(74,[37]); // true true
equal_rank(74,[2]); // false true
equal_rank(74,[2, 37]); // false true

//////// 

rank_quo(389,[]); // 13 true. So the rank of J_0(389) is 13.
rank_quo(389,[389]); // 11 true. So the rank of J_0+(389) is 11.
equal_rank(389,[389]); // false true

for A in Decomposition(JZero(389)) do
    simple_rank(A);   // ranks are 2,2,3,6,0. All true.
end for;

////////

rank_quo(13,[]); // 0 true  
rank_quo(1,[]); // 0 true  

*/
