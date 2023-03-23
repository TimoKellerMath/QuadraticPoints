# QuadraticPoints
Magma code to compute quadratic points on X_0(N). 

The code is associated to the following paper: http://arxiv.org/abs/2303.12566 "Computing quadratic points on modular curves X_0(N)" by Nikola Adzaga, Timo Keller, Philippe Michaud-Jacobs, Filip Najman, Ekin Ozman, and Borna Vukorepa.

The repository consists of the following files and folders:

- **Additional_examples** (folder). This folder contains additional example computations that do not form part of the paper.
- **Classical_Chabauty** (folder). This folder contains code for perfoming classical Chabauty computations.
- **Output_files** (folder). Contains all output files for tha 'rank 0' and 'Atkin-Lehner sieve' levels as well as the output of the verifications file.
- `AL_sieve.m` Main file for the 'Atkin-Lehner sieve' method. Performs the computations.
- `AL_sieve_auxiliary.m`.  Contains functions for the 'Atkin-Lehner sieve' method.
- `going_down.m`. Main file for the 'going-down' method. Performs the computations.
- `models_and_maps.m`.  This file contains code to compute models for X_0(N), quotient curves, quotient maps, j-maps and more.
- `pullbacks.m`.   This file contains a function to search for quadratic points on a model of X_0(N) which arise as pullbacks of rational points on AL quotients. Also provides code to compute j-invariants and CM discriminants. 
- `rank_0.m`. Main file for the 'rank 0' method. Performs the computations.
- `rank_0_auxiliary.m`. Contains functions for the 'rank 0' method. This code is taken from the paper: Ozman-Siksek, Quadratic Points on Modular curves.
- `rank_calcs.m`.  This file contains functions for computing the ranks over Q of J_0(N) and its quotients.
- `symm_chab.m`. This file contains functions for verifying the symmetric Chabauty criterion we use in the Atkin-Lehner sieve.
- `verifications.m`. This file checks (and prints most of) the data presented in the tables of the paper, it also provides coordinates for each quadratic point we consider.
