//the following Magma code proves that there are only two (pairs of Galois conjugated)
//quadratic points on X0(86) that are not pullbacks
//of rational points on X0(86)/w43
//(nor fixed points of w43)


//we first create a list of points that are not pullbacks

K7<r7> := QuadraticField(-7);
P1 := <K7, [-1, (-1/7)*r7, 0, (1/7)*r7, (1/7)*r7, (1/7)*r7, (-1/7)*r7, (-1/7)*r7, 1, 1]>;
P2 := <K7, [1, (1/7)*r7, 0, (-1/7)*r7, (-1/7)*r7, (1/7)*r7, (-1/7)*r7, (-1/7)*r7, 1, 1]>;
nonpbs := [P1, P2];

 load "AL_sieve_auxiliary.m";
 AL_sieve(86 : d:=43, nonpullbacks:=nonpbs, badPrimes:={7});
//prime 7 does not contribute to the sieve

//log is available at X_0(86).log


// since X0(86)/w43 is genus 4 rank 2 curve,
// one can prove that it has exactly 7 rational points
// in the same manner as we did for X0(74)/w37
//  (look at 74_37.m in Classical Chabauty folder,
//    in this file, change 74 to 86, 37 to 43,
//    and  prime to 13 (p := 13;)
//  )

