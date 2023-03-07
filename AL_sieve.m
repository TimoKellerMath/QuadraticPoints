// This is the main file for the Atkin-Lehner sieve method.
// The output for each level is contained in the corresponding .log file in the Output_files folder

load "AL_sieve_auxiliary.m";

for N in [74, 85, 86, 97, 103, 109, 121, 127] do
    // Choose appropriate AL index, d. 
    // The main function will verify the equal rank criterion.
    if N eq 74 then 
        dd := 37;
    elif N eq 86 then 
        dd := 43;
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
    elif N eq 86 then    
        K7<r7> := QuadraticField(-7);
        P1 := <K7, [-1, (-1/7)*r7, 0, (1/7)*r7, (1/7)*r7, (1/7)*r7, (-1/7)*r7, (-1/7)*r7, 1, 1]>;
        P2 := <K7, [1, (1/7)*r7, 0, (-1/7)*r7, (-1/7)*r7, (1/7)*r7, (-1/7)*r7, (-1/7)*r7, 1, 1]>;
        nonpbs := [P1, P2];
        // can also include 7 as a 'bad prime' for N = 86 to speed up the sieving computation if desired.
    else 
        nonpbs := [];
    end if;       
     AL_sieve(N : d:=dd, nonpullbacks := nonpbs); // This carries out the Atkin-Lehner sieve
end for;


// Timing for X_0(53): 
// time AL_sieve(53: badPrimes := {5,7,11}); // 4.9 seconds
