load "finiteindexsubgroupofJ.m";
SetDebugOnError(true);
X := X0NQuotient(74, [37]);
r := rank_quo(74,[37]);
Xpts := PointSearch(X,100);
IsFiniteIndexSubgroupOfJacobian(X, false, r, Xpts);