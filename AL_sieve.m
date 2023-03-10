// This is the main file for the Atkin-Lehner sieve method.
// The output for each level is contained in the corresponding .log file in the Output_files folder

load "AL_sieve_auxiliary.m";

for N in [74, 85, 97, 103, 107, 109, 113, 121, 127] do
    // Choose appropriate AL index, d. 
    // The main function will verify the equal rank criterion.
    if N eq 74 then 
        dd := 37;
    else 
        dd := N;
    end if;

    // Include any additional points. These additional points are computed using the pullbacks.m file. 
    // Here we input the points manually
    
    if N eq 74 then
        K7<r7> := QuadraticField(-7);
        P1 := <K7, [-1, 0, 0, 1/r7, 2/r7, -2/r7, 1/r7, 1]>;
        P2 := <K7, [-1, 0, 0, -1/r7, 2/r7, -2/r7, 1/r7, -1]>;
        nonpbs := [P1, P2];
    else 
        nonpbs := [];
    end if;       
     AL_sieve(N : d:=dd, nonpullbacks := nonpbs); // This carries out the Atkin-Lehner sieve
end for;


// Timing for X_0(53): 
// time AL_sieve(53: badPrimes := {3,5,7,11}); // 3.8 seconds
