// This file contains all computations used in the 'going-down method'
load  "new_models.m";


// We will need this function

coords_jK := function(X,j,jinv,K);
    PP := Codomain(j);
    pt := PP ! [jinv];
    base_scheme := BaseScheme(j);
    pullback_scheme := Pullback(j,pt);
    difference := Difference(pullback_scheme, base_scheme);
    differenceK := BaseChange(difference,K);
    points := Points(differenceK);
    return points;
end function;


%%%%%%%%%%%%%%%%%%%%%%%% N=58 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
// We first deal with the case N=58. The first thing we do is that the exceptional quadratic points on $X_0(29)$ do not pull back to quadratic points on X_0(58). We do this by checking that none of them have a 2-isogeny, which is quivalent to having a 2-torsion points.  

C:=SmallModularCurve(29);
d:=-1;
K<w>:=QuadraticField(d);
C1:=ChangeRing(C,K);
P:=C1![w-1,2*w+4];
j:=jInvariant(P,29);
E:=EllipticCurveFromjInvariant(j);
TwoTorsionSubgroup(E);
P:=C1![w-1,-1];
j:=jInvariant(P,29);
E:=EllipticCurveFromjInvariant(j);
TwoTorsionSubgroup(E);
d:=-7;
K<w>:=QuadraticField(d);
C1:=ChangeRing(C,K);
P:=C1![(w+1)/4,(-11*w-7)/16];
j:=jInvariant(P,29);
E:=EllipticCurveFromjInvariant(j);
TwoTorsionSubgroup(E);
P:=C1![(w+1)/4,(5*w+9)/8];
j:=jInvariant(P,29);
E:=EllipticCurveFromjInvariant(j);
TwoTorsionSubgroup(E);

//checked, none of them, moving on. 





X,w,quot:= eqs_quos(58,[[29]]);
"Nice model for X0(58) is:";
X;
Xw:=quot[1,1];
quotMap:=quot[1,2];


RankBounds(Jacobian(Xw));

//The rank is 1, so we can use classical Chabauty over Q. 
J:=Jacobian(Xw);
pts:=RationalPoints(Xw:Bound:=200);
P:=pts[1]-pts[2];
P:=J!P;
assert Order(P) eq 0;
pts2:=Chabauty(P);
f3:=Inverse(f2);
assert #pts2 eq #pts;
// so we have found all the points. It remains to find the j-invariants. 
j:=jmap(X,58);
deg2pb:=[Pullback(quotMap,Place(Xw!p)):p in pts];
g:=Genus(X);
for i in [1..#deg2pb] do
	if Degree(ResidueClassField(Decomposition(deg2pb[i])[1,1])) gt 1 then
		K1<z>:=ResidueClassField(Decomposition(deg2pb[i])[1,1]);
		d:=SquarefreeFactorization(Discriminant(K1));
		K<w>:=QuadraticField(d);
		tr,f:=IsIsomorphic(K1,K);
		assert tr;
		P:=RepresentativePoint(Decomposition(deg2pb[i])[1,1]);
		w^2,P,j(P)[1],HasComplexMultiplication(EllipticCurveFromjInvariant(j(P)[1]));
	end if;
end for;

/* This completes the case N=58 */

/* The list of CM points below has been provided by P. L. Clark, T. Genao, P. Pollack, and F. Saia 

The N'th element in this list has the form [* N, d_{CM}(X_0(N)), [ orders ] *], where [ orders ] is the complete sequence of imaginary quadratic orders O such that O minimizes d_{CM}(X_0(N)), i.e., d_{O,CM}(X_0(N)) = d_{CM}(X_0(N)). 

The orders O are given in the form [f, d_K, h(O)] := [conductor, fundamental discriminant, class number of O] -- the class number is only included for convenience. */




t68:=[* 68, 2,
    [   [ 1, -4, 1 ],
        [ 2, -4, 1 ]
    ]
*];


t76:=[* 76, 2,
    [
        [ 2, -3, 1 ]
    ]
*];



t108:=[* 108, 4,
    [
        [ 1, -8, 1 ],
        [ 2, -8, 2 ]
    ]
*];

// there are no degree 2 CM points on X0(108)

ComputejInvs:= function(A);
n:=#A[3];
ret:=[];
for i:=1 to n do 
	B:=A[3,i];
	D:=B[2]*B[1]^2;
	j:=Round(jInvariant(BinaryQuadraticForms(D)!1));
	ret:= Append(ret, [j, D]);
end for;
return ret;
end function;

//this gives us the CM j-invariants such that correspond to quadratic points on X_0(68)
j68:=ComputejInvs(t68); 
*/ returns
[
    [ 1728, -4 ],
    [ 287496, -16 ]
]
*/
// now we want to determine a model for X_0(68) and the coordinates of corresponding points
X:=eqs_quos(68,[]);
"Nice model for X0(68) is:";
X;
j:=jmap(X,68);
for i:= 1 to #j68 do
d:=SquareFreeFactorization(Integers()!j68[i,2]);
K<w>:=QuadraticField(d);
K, coords_jK(X,j,K!(j68[i,1]),K);
end for;
*/ this takes a while and returns:
Quadratic Field with defining polynomial $.1^2 + 1 over the Rational Field
{@ (-w : -1 : 0 : 0 : 0 : -1/2*w : 1), (w : -1 : 0 : 0 : 0 : 1/2*w : 1) @}
Quadratic Field with defining polynomial $.1^2 + 1 over the Rational Field
{@ (0 : 0 : 0 : 0 : -1/2*w : -1/4*w : 1), (0 : 0 : 0 : 0 : 1/2*w : 1/4*w : 1),
(-w : 1 : 0 : 0 : 0 : 1/2*w : 1), (w : 1 : 0 : 0 : 0 : -1/2*w : 1) @}

*/

*/ The case N=76 remains. We now deal with it */

X:=eqs_quos(76,[]);
"Nice model for X0(76) is:";
X;
j:=jmap(X,76);
j76:=ComputejInvs(t76); 
/* returns:

[
    [ 54000, -12 ]
]

*/
for i:= 1 to #j76 do
d:=SquareFreeFactorization(Integers()!j76[i,2]);
K<w>:=QuadraticField(d);
K, coords_jK(X,j,K!j76[i,1],K);
end for;

*/

/* this returns


Quadratic Field with defining polynomial $.1^2 + 3 over the Rational Field
{@ (-1 : 0 : 0 : -1/3*w : 0 : 1/3*w : 2 : 1), (-1 : 0 : 0 : 1/3*w : 0 : -1/3*w :
2 : 1), (1 : 0 : 0 : -1/3*w : 0 : -1/3*w : 2 : 1), (1 : 0 : 0 : 1/3*w : 0 :
    1/3*w : 2 : 1) @}
*/








