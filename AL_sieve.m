// This will be the main file for the Atkin-Lehner sieve method
// Here is a rough start, probably does not run yet, will work on it.

load "AL_sieve_auxiliary.m";

for N in [74, 85, 86, 97, 103, 109, 121, 127] do
    // Choose appropriate AL index, d.
    if N eq 74 then 
        dd := 37;
    elif N eq 86 then 
        dd := 43;
    else 
        dd := N;
    end if;

    // Include any additional points.
    
    if N eq 74 then
        K7<r7> := QuadraticField(-7);
        P1 := <K7, [-1, 0, 0, 1/r7, 2/r7, -2/r7, 1/r7, 1]>;
        P2 := <K7, [-1, 0, 0, -1/r7, 2/r7, -2/r7, 1/r7, -1]>;
        nonpbs := [P1, P2];
    elif N eq 86 then    
        K7<r7> := QuadraticField(-7);
        P1 := <K7, [-1, (-1/7)*r7, 0, (1/7)*r7, (1/7)*r7, (1/7)*r7, (-1/7)*r7, (-1/7)*r7, 1, 1]>;
        P2 := <K7, [1, (1/7)*r7, 0, (-1/7)*r7, (-1/7)*r7, (1/7)*r7, (-1/7)*r7, (-1/7)*r7, 1, 1]>;
        nonpbs := [P1, P2];
    else 
        nonpbs := [];
    end if;
        
     AL_sieve(N : d:=dd, nonpullbacks := nonpbs);
end for;
