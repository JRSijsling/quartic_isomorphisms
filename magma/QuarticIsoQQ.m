/***
 *  Quartic isomorphisms over the rationals
 *
 *  Written by Jeroen Sijsling (jeroen.sijsling@uni-ulm.de)
 *
 *  See LICENSE.txt for license details.
 */


import "Ingredients.m": DifferentialOperation, EffSPProduct, SmallSplittingFieldOverRationals, TrivializeAlgebra, TransformTernaryForm, Normalize33, BinQuadInvs, IsMultiple, AssertTs;
import "IsoZ3.m": IsoZ3;
import "IsoG16.m": IsoG16;
import "Sutherland.m": SPQIsIsomorphic;


function QuarticIsoQQInvTest(f1,f2);

I1,W := DixmierOhnoInvariants(f1);
I2,W := DixmierOhnoInvariants(f2);

if WPSNormalize(W,I1) eq WPSNormalize(W,I2) then
    return true;
else
    return false;
end if;

end function;


/* C3 stratum (dim 2) */
function IsInStratumC3(DO)

    I03,I06,I09,J09,I12,J12,I15,J15,I18,J18,I21,J21,I27 := Explode(DO);

    if
	I03 eq 0
	and
	I06 eq 0
	and
	I12 eq 0
	and
	J12 eq 0
	and
	I15 eq 0
	and
	J15 eq 0
	and
	I21 eq 0
	and
	J21 eq 0
	then
	return true;
    end if;

    return false;
end function;


/* G16 stratum (dim 1) */
function IsInStratumG16(DO)

    I03,I06,I09,J09,I12,J12,I15,J15,I18,J18,I21,J21,I27 := Explode(DO);

    if
	I06 eq 0
	and
	-3*J09 + I09 eq 0
	and
	I12 eq 0
	and
	3*J12 - I09*I03 eq 0
	and
	I15 eq 0
	and
	J15 eq 0
	and
	J18 eq 0
	and
	I18 eq 0
	and
	I21 eq 0
	and
	J21 eq 0
	and
	I27 - 27*I09^3 + 27*I09^2*I03^3 - 9*I09*I03^6 + I03^9 eq 0
	then
	return true;
    end if;

    return false;
end function;


function QuarticIsomorphismsQQ(f1, f2 : geometric := false);

//This algorithm determines whether the quartic curves in  P2  determined by two homogeneous polynomials  f1 and f2  with a common ground field are isomorphic.
//If so, it returns all isomorphisms between these curves.

//It is based on part of the Ph.D. thesis of Sander van Rijnswou.
//We improved his implementation by taking an at worst
//quadratic extension of the base field.

P2 := ProjectiveSpace(Parent(f1));
F := BaseRing(P2);
S<t> := PolynomialRing(F);
R<x1,x2,x3> := CoordinateRing(P2);
Transfs := [];

if not QuarticIsoQQInvTest(f1,f2) then
    return false,[* *],false;
else

I1 := DixmierOhnoInvariants(f1);
if IsInStratumC3(I1) then
    vprint QuarticIso : "In stratum C3";
    try
        test,Ts,StF := IsoZ3(f1,f2 : geometric := geometric);
        return test,Ts,true;
    catch e
        test, Mss := SPQIsIsomorphic(f1, f2 : geometric := geometric);
        return test, &cat(Mss), true;
    end try;
end if;
if IsInStratumG16(I1) then
    vprint QuarticIso : "In stratum G16";
    try
        test,Ts := IsoG16(f1,f2 : geometric := geometric);
        return test,Ts,true;
    catch e
        test, Mss := SPQIsIsomorphic(f1, f2 : geometric := geometric);
        return test, &cat(Mss), true;
    end try;
end if;

//try
//Finding a suitable quadratic contravariant
stop := false;
teller := 0;

while not stop do
teller := teller + 1;

if teller eq 2 then
    stop := true;
else

if teller eq 1 then
    Phi1 := f1;
    Sigma1, Psi1 := ContravariantSigmaAndPsi(Phi1);
    Rho1 := (1/144)*DifferentialOperation(Phi1,Psi1);
    Phi2 := f2;
    Sigma2, Psi2 := ContravariantSigmaAndPsi(Phi2);
    Rho2 := (1/144)*DifferentialOperation(Phi2,Psi2);
    C1 := Rho1;
    C2 := Rho2;
    cov := false;
elif teller eq 2 then
    He1 := (1/1728)*CovariantHessian(Phi1);
    He2 := (1/1728)*CovariantHessian(Phi2);
    Tau1 := (1/12)*DifferentialOperation(Rho1,Phi1);
    Tau2 := (1/12)*DifferentialOperation(Rho2,Phi2);
    C1 := Tau1;
    C2 := Tau2;
    cov := true;
elif teller eq 3 then
    Xi1 := (1/72)*DifferentialOperation(Sigma1,He1);
    Xi2 := (1/72)*DifferentialOperation(Sigma2,He2);
    C1 := Xi1;
    C2 := Xi2;
    cov := true;
elif teller eq 4 then
    Eta1 := (1/12)*DifferentialOperation(Xi1,Sigma1);
    Eta2 := (1/12)*DifferentialOperation(Xi2,Sigma2);
    C1 := Eta1;
    C2 := Eta2;
    cov := false;
elif teller eq 5 then
    Chi1 := (1/8)*DifferentialOperation(Tau1,DifferentialOperation(Tau1,Psi1));
    Chi2 := (1/8)*DifferentialOperation(Tau2,DifferentialOperation(Tau2,Psi2));
    C1 := Chi1;
    C2 := Chi2;
    cov := false;
elif teller eq 6 then
    Nu1 := (1/8)*DifferentialOperation(Eta1,DifferentialOperation(Rho1,He1));
    Nu2 := (1/8)*DifferentialOperation(Eta2,DifferentialOperation(Rho2,He2));
    C1 := Nu1;
    C2 := Nu2;
    cov := true;
end if;

//Standard form of covariant
CS := x2^2 - x1*x3;

//We transform into standard diagonal form.
//At the same time, this is a further isomorphism test over the ground field.

MC1 := Matrix(F,3,3,[MonomialCoefficient(C1,x1^2),MonomialCoefficient(C1,x1*x2)/2,MonomialCoefficient(C1,x1*x3)/2,
                       MonomialCoefficient(C1,x2*x1)/2,MonomialCoefficient(C1,x2*x2),MonomialCoefficient(C1,x2*x3)/2,
                       MonomialCoefficient(C1,x3*x1)/2,MonomialCoefficient(C1,x3*x2)/2,MonomialCoefficient(C1,x3^2)]);
MC2 := Matrix(F,3,3,[MonomialCoefficient(C2,x1^2),MonomialCoefficient(C2,x1*x2)/2,MonomialCoefficient(C2,x1*x3)/2,
                       MonomialCoefficient(C2,x2*x1)/2,MonomialCoefficient(C2,x2*x2),MonomialCoefficient(C2,x2*x3)/2,
                       MonomialCoefficient(C2,x3*x1)/2,MonomialCoefficient(C2,x3*x2)/2,MonomialCoefficient(C2,x3^2)]);
MCS := Matrix(F,3,3,[MonomialCoefficient(CS,x1^2),MonomialCoefficient(CS,x1*x2)/2,MonomialCoefficient(CS,x1*x3)/2,
                       MonomialCoefficient(CS,x2*x1)/2,MonomialCoefficient(CS,x2*x2),MonomialCoefficient(CS,x2*x3)/2,
                       MonomialCoefficient(CS,x3*x1)/2,MonomialCoefficient(CS,x3*x2)/2,MonomialCoefficient(CS,x3^2)]);

if Determinant(MC1) ne 0 then
//"still suitable";

Min1,ST1 := MinimalModel(Conic(P2,C1));
Min2,ST2 := MinimalModel(Conic(P2,C2));
MinS,STS := MinimalModel(Conic(P2,CS));

DE1 := DefiningEquation(Min1);
DP1 := DefiningPolynomials(ST1);
MT1 := Matrix(F,3,3,[MonomialCoefficient(DP1[1],x1),MonomialCoefficient(DP1[1],x2),MonomialCoefficient(DP1[1],x3),
                     MonomialCoefficient(DP1[2],x1),MonomialCoefficient(DP1[2],x2),MonomialCoefficient(DP1[2],x3),
                     MonomialCoefficient(DP1[3],x1),MonomialCoefficient(DP1[3],x2),MonomialCoefficient(DP1[3],x3)]);
MT1 := Transpose(MT1);

DE2 := DefiningEquation(Min2);
DP2 := DefiningPolynomials(ST2);
MT2 := Matrix(F,3,3,[MonomialCoefficient(DP2[1],x1),MonomialCoefficient(DP2[1],x2),MonomialCoefficient(DP2[1],x3),
                     MonomialCoefficient(DP2[2],x1),MonomialCoefficient(DP2[2],x2),MonomialCoefficient(DP2[2],x3),
                     MonomialCoefficient(DP2[3],x1),MonomialCoefficient(DP2[3],x2),MonomialCoefficient(DP2[3],x3)]);
MT2 := Transpose(MT2);

DES := DefiningEquation(MinS);
DPS := DefiningPolynomials(STS);
MTS := Matrix(F,3,3,[MonomialCoefficient(DPS[1],x1),MonomialCoefficient(DPS[1],x2),MonomialCoefficient(DPS[1],x3),
                     MonomialCoefficient(DPS[2],x1),MonomialCoefficient(DPS[2],x2),MonomialCoefficient(DPS[2],x3),
                     MonomialCoefficient(DPS[3],x1),MonomialCoefficient(DPS[3],x2),MonomialCoefficient(DPS[3],x3)]);
MTS := Transpose(MTS);

DF1,T1 := DiagonalForm(DE1);
DF2,T2 := DiagonalForm(DE2);
DFS,TS := DiagonalForm(DES);

DF1 := DiagonalMatrix(F,3,[MonomialCoefficient(DF1,x1^2),MonomialCoefficient(DF1,x2^2),MonomialCoefficient(DF1,x3^2)]);
DF2 := DiagonalMatrix(F,3,[MonomialCoefficient(DF2,x1^2),MonomialCoefficient(DF2,x2^2),MonomialCoefficient(DF2,x3^2)]);
DFS := DiagonalMatrix(F,3,[MonomialCoefficient(DFS,x1^2),MonomialCoefficient(DFS,x2^2),MonomialCoefficient(DFS,x3^2)]);
T1 := MatrixRing(F,3)!T1;
T2 := MatrixRing(F,3)!T2;
TS := MatrixRing(F,3)!TS;

a1 := DF1[1,1];
b1 := DF1[2,2];
c1 := DF1[3,3];
a2 := DF2[1,1];
b2 := DF2[2,2];
c2 := DF2[3,3];
aS := DFS[1,1];
bS := DFS[2,2];
cS := DFS[3,3];

//Let's make the entries a bit smaller.
scx1 := EffSPProduct(b1,c1);
scy1 := EffSPProduct(a1,c1);
scx2 := EffSPProduct(b2,c2);
scy2 := EffSPProduct(a2,c2);
scxS := EffSPProduct(bS,cS);
scyS := EffSPProduct(aS,cS);

SF1 := DiagonalMatrix(F,3,[1/scx1,1/scy1,1/(scx1*scy1)]);
SF2 := DiagonalMatrix(F,3,[1/scx2,1/scy2,1/(scx2*scy2)]);
SFS := DiagonalMatrix(F,3,[1/scxS,1/scyS,1/(scxS*scyS)]);

Q1 := QuaternionAlgebra<F | -b1*c1*(1/scx1)^2 , -a1*c1*(1/scy1)^2 >;
Q2 := QuaternionAlgebra<F | -b2*c2*(1/scx2)^2 , -a2*c2*(1/scy2)^2 >;
QS := QuaternionAlgebra<F | -bS*cS*(1/scxS)^2 , -aS*cS*(1/scyS)^2 >;

Disc1 := Discriminant(Q1);
Disc2 := Discriminant(Q2);
DiscS := Discriminant(QS);

if not (Disc1 eq Disc2) then
    return false,[* *],false;
else

//Now we take a common extension for all three algebras such that all split.
//(The final one splits over  Q  itself already, so that is easy.)
//We can then map the forms associated to the first two to (still different) multiples of the last.

d := SmallSplittingFieldOverRationals(Disc1);

R<t> := PolynomialRing(F);
L := SplittingField(t^2 - d);
P2L<x1,x2,x3> := ProjectiveSpace(L,2);
RL<x1,x2,x3> := CoordinateRing(P2L);

Con1 := Conic(P2L,a1*x1^2 + b1*x2^2 + c1*x3^2);
Con2 := Conic(P2L,a2*x1^2 + b2*x2^2 + c2*x3^2);
ConS := Conic(P2L,aS*x1^2 + bS*x2^2 + cS*x3^2);

test1,pt1 := HasRationalPoint(Con1);
test2,pt2 := HasRationalPoint(Con2);
testS,ptS := HasRationalPoint(ConS);

Q1L<i1,j1,k1> := QuaternionAlgebra<L | -b1*c1*(1/scx1)^2 , -a1*c1*(1/scy1)^2 >;
Q2L<i2,j2,k2> := QuaternionAlgebra<L | -b2*c2*(1/scx2)^2 , -a2*c2*(1/scy2)^2 >;
QSL<iS,jS,kS> := QuaternionAlgebra<L | -bS*cS*(1/scxS)^2 , -aS*cS*(1/scyS)^2 >;

pt1 := [scx1*pt1[1]/(b1*c1),scy1*pt1[2]/(a1*c1),scx1*scy1*pt1[3]/(a1*b1*c1)];
pt2 := [scx2*pt2[1]/(b2*c2),scy2*pt2[2]/(a2*c2),scx2*scy2*pt2[3]/(a2*b2*c2)];
ptS := [scxS*ptS[1]/(bS*cS),scyS*ptS[2]/(aS*cS),scxS*scyS*ptS[3]/(aS*bS*cS)];

ip1,jp1 := TrivializeAlgebra(Q1L,pt1);
ip2,jp2 := TrivializeAlgebra(Q2L,pt2);
ipS,jpS := TrivializeAlgebra(QSL,ptS);

kp1 := ip1*jp1;
kp2 := ip2*jp2;
kpS := ipS*jpS;

U1 := DiagonalMatrix(F,[b1*c1,a1*c1,a1*b1*c1]);
U2 := DiagonalMatrix(F,[b2*c2,a2*c2,a2*b2*c2]);
US := DiagonalMatrix(F,[bS*cS,aS*cS,aS*bS*cS]);

V1 := Matrix(L,3,3,[Eltseq(ip1)[2],Eltseq(ip1)[3],Eltseq(ip1)[4],Eltseq(jp1)[2],Eltseq(jp1)[3],Eltseq(jp1)[4],Eltseq(kp1)[2],Eltseq(kp1)[3],Eltseq(kp1)[4]]);
V2 := Matrix(L,3,3,[Eltseq(ip2)[2],Eltseq(ip2)[3],Eltseq(ip2)[4],Eltseq(jp2)[2],Eltseq(jp2)[3],Eltseq(jp2)[4],Eltseq(kp2)[2],Eltseq(kp2)[3],Eltseq(kp2)[4]]);
VS := Matrix(L,3,3,[Eltseq(ipS)[2],Eltseq(ipS)[3],Eltseq(ipS)[4],Eltseq(jpS)[2],Eltseq(jpS)[3],Eltseq(jpS)[4],Eltseq(kpS)[2],Eltseq(kpS)[3],Eltseq(kpS)[4]]);

W1 := V1*SF1*U1*T1*MT1;
W2 := V2*SF2*U2*T2*MT2;
WS := VS*SFS*US*TS*MTS;

D1 := W1*MC1*Transpose(W1);
D2 := W2*MC2*Transpose(W2);
DS := WS*MCS*Transpose(WS);

T1 := WS^(-1)*W1;
T2 := WS^(-1)*W2;

//We transform the forms such that the covariants are (a multiple of)  RhoS  :
if not cov then
    TT1 := T1^(-1);
    TT2 := T2^(-1);
    f1new := TransformTernaryForm(RL!f1,TT1);
    f2new := TransformTernaryForm(RL!f2,TT2);
else
    TT1 := Transpose(T1);
    TT2 := Transpose(T2);
    f1new := TransformTernaryForm(RL!f1,TT1);
    f2new := TransformTernaryForm(RL!f2,TT2);
//    Testing covariance
//    Phi1 := f1new;
//    Sigma1, Psi1 := ContravariantSigmaAndPsi(Phi1);
//    Rho1 := (1/144)*DifferentialOperation(Phi1,Psi1);
//    He1 := (1/1728)*CovariantHessian(Phi1);
//    Tau1 := (1/12)*DifferentialOperation(Rho1,Phi1);
//    Phi2 := f2new;
//    Sigma2, Psi2 := ContravariantSigmaAndPsi(Phi2);
//    Rho2 := (1/144)*DifferentialOperation(Phi2,Psi2);
//    He2 := (1/1728)*CovariantHessian(Phi2);
//    Tau2 := (1/12)*DifferentialOperation(Rho2,Phi2);
//    Tau1;
//    Tau2;
end if;

//C1new := TransformTernaryForm(RL!C1,Transpose(T1));
//C2new := TransformTernaryForm(RL!C2,Transpose(T2));
//C1new;
//C2new;

//Finally, we apply the decomposition by Cohen et al.
//described computationally by Van Rijnswou.
if not cov then

T := Matrix(L,15,15,[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
                     0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,
                     0,0,8,12,0,0,0,0,0,0,0,0,0,0,0,
                     0,0,0,0,72,0,24,0,0,0,0,0,0,0,0,
                     0,0,0,0,0,144,0,288,0,0,24,0,0,0,0,
                     0,0,0,0,0,0,0,0,1440,0,0,480,0,0,0,
                     0,0,0,0,0,0,0,0,0,2880,0,0,4320,0,0,
                     0,0,0,0,0,0,0,0,0,0,0,0,0,20160,0,
                     0,0,0,0,0,0,0,0,0,0,0,0,0,0,40320,
                     0,0,-4,1,0,0,0,0,0,0,0,0,0,0,0,
                     0,0,0,0,-8,0,2,0,0,0,0,0,0,0,0,
                     0,0,0,0,0,-16,0,-4,0,0,2,0,0,0,0,
                     0,0,0,0,0,0,0,0,-48,0,0,12,0,0,0,
                     0,0,0,0,0,0,0,0,0,-96,0,0,24,0,0,
                     0,0,0,0,0,16,0,-8,0,0,1,0,0,0,0]);
T := Transpose(T);

M8 := Matrix(L,15,9,[1,0,0,0,0,0,0,0,0,
                     0,8,0,0,0,0,0,0,0,
                     0,0,8*7,0,0,0,0,0,0,
                     0,0,0,8*7*6,0,0,0,0,0,
                     0,0,0,0,8*7*6*5,0,0,0,0,
                     0,0,0,0,0,8*7*6*5*4,0,0,0,
                     0,0,0,0,0,0,8*7*6*5*4*3,0,0,
                     0,0,0,0,0,0,0,8*7*6*5*4*3*2,0,
                     0,0,0,0,0,0,0,0,8*7*6*5*4*3*2*1,
                     0,0,0,0,0,0,0,0,0,
                     0,0,0,0,0,0,0,0,0,
                     0,0,0,0,0,0,0,0,0,
                     0,0,0,0,0,0,0,0,0,
                     0,0,0,0,0,0,0,0,0,
                     0,0,0,0,0,0,0,0,0]);
M8 := Transpose(M8);

M4 := Matrix(L,15,5,[0,0,0,0,0,
                     0,0,0,0,0,
                     0,0,0,0,0,
                     0,0,0,0,0,
                     0,0,0,0,0,
                     0,0,0,0,0,
                     0,0,0,0,0,
                     0,0,0,0,0,
                     0,0,0,0,0,
                     1,0,0,0,0,
                     0,4,0,0,0,
                     0,0,4*3,0,0,
                     0,0,0,4*3*2,0,
                     0,0,0,0,4*3*2*1,
                     0,0,0,0,0]);
M4 := Transpose(M4);

//M4 := Matrix(L,15,5,[0,0,0,0,0,
//                     0,0,0,0,0,
//                     0,0,0,0,0,
//                     0,0,0,0,0,
//                     0,0,0,0,0,
//                     0,0,0,0,0,
//                     0,0,0,0,0,
//                     0,0,0,0,0,
//                     0,0,0,0,0,
//                     0,0,0,0,1,
//                     0,0,0,-4,0,
//                     0,0,12,0,0,
//                     0,-24,0,0,0,
//                     24,0,0,0,0,
//                     0,0,0,0,0]);
//M4 := Transpose(M4);

a400 := MonomialCoefficient(f1new,x1^4);
a310 := MonomialCoefficient(f1new,x1^3*x2);
a301 := MonomialCoefficient(f1new,x1^3*x3);
a220 := MonomialCoefficient(f1new,x1^2*x2^2);
a211 := MonomialCoefficient(f1new,x1^2*x2*x3);
a202 := MonomialCoefficient(f1new,x1^2*x3^2);
a130 := MonomialCoefficient(f1new,x1*x2^3);
a121 := MonomialCoefficient(f1new,x1*x2^2*x3);
a112 := MonomialCoefficient(f1new,x1*x2*x3^2);
a103 := MonomialCoefficient(f1new,x1*x3^3);
a040 := MonomialCoefficient(f1new,x2^4);
a031 := MonomialCoefficient(f1new,x2^3*x3);
a022 := MonomialCoefficient(f1new,x2^2*x3^2);
a013 := MonomialCoefficient(f1new,x2*x3^3);
a004 := MonomialCoefficient(f1new,x3^4);

b400 := MonomialCoefficient(f2new,x1^4);
b310 := MonomialCoefficient(f2new,x1^3*x2);
b301 := MonomialCoefficient(f2new,x1^3*x3);
b220 := MonomialCoefficient(f2new,x1^2*x2^2);
b211 := MonomialCoefficient(f2new,x1^2*x2*x3);
b202 := MonomialCoefficient(f2new,x1^2*x3^2);
b130 := MonomialCoefficient(f2new,x1*x2^3);
b121 := MonomialCoefficient(f2new,x1*x2^2*x3);
b112 := MonomialCoefficient(f2new,x1*x2*x3^2);
b103 := MonomialCoefficient(f2new,x1*x3^3);
b040 := MonomialCoefficient(f2new,x2^4);
b031 := MonomialCoefficient(f2new,x2^3*x3);
b022 := MonomialCoefficient(f2new,x2^2*x3^2);
b013 := MonomialCoefficient(f2new,x2*x3^3);
b004 := MonomialCoefficient(f2new,x3^4);

v1 := Matrix(L,15,1,[a400,a310,a301,a220,a211,a202,a130,a121,a112,a103,a040,a031,a022,a013,a004]);
v2 := Matrix(L,15,1,[b400,b310,b301,b220,b211,b202,b130,b121,b112,b103,b040,b031,b022,b013,b004]);

Ti := T^(-1);

w41 := M4*Ti*v1;
w42 := M4*Ti*v2;

w81 := M8*Ti*v1;
w82 := M8*Ti*v2;

else

T := Matrix(L,15,15,[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
                     0,-8,0,0,0,0,0,0,0,0,0,0,0,0,0,
                     0,0,8,48,0,0,0,0,0,0,0,0,0,0,0,
                     0,0,0,0,-144,0,-192,0,0,0,0,0,0,0,0,
                     0,0,0,0,0,144,0,1152,0,0,384,0,0,0,0,
                     0,0,0,0,0,0,0,0,-2880,0,0,-3840,0,0,0,
                     0,0,0,0,0,0,0,0,0,2880,0,0,17280,0,0,
                     0,0,0,0,0,0,0,0,0,0,0,0,0,-40320,0,
                     0,0,0,0,0,0,0,0,0,0,0,0,0,0,40320,
                     0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,
                     0,0,0,0,4,0,-4,0,0,0,0,0,0,0,0,
                     0,0,0,0,0,-4,0,-4,0,0,8,0,0,0,0,
                     0,0,0,0,0,0,0,0,24,0,0,-24,0,0,0,
                     0,0,0,0,0,0,0,0,0,-24,0,0,24,0,0,
                     0,0,0,0,0,1,0,-2,0,0,1,0,0,0,0]);
T := Transpose(T);

M8 := Matrix(L,15,9,[1,0,0,0,0,0,0,0,0,
                     0,8,0,0,0,0,0,0,0,
                     0,0,8*7,0,0,0,0,0,0,
                     0,0,0,8*7*6,0,0,0,0,0,
                     0,0,0,0,8*7*6*5,0,0,0,0,
                     0,0,0,0,0,8*7*6*5*4,0,0,0,
                     0,0,0,0,0,0,8*7*6*5*4*3,0,0,
                     0,0,0,0,0,0,0,8*7*6*5*4*3*2,0,
                     0,0,0,0,0,0,0,0,8*7*6*5*4*3*2*1,
                     0,0,0,0,0,0,0,0,0,
                     0,0,0,0,0,0,0,0,0,
                     0,0,0,0,0,0,0,0,0,
                     0,0,0,0,0,0,0,0,0,
                     0,0,0,0,0,0,0,0,0,
                     0,0,0,0,0,0,0,0,0]);
M8 := Transpose(M8);

M4 := Matrix(L,15,5,[0,0,0,0,0,
                     0,0,0,0,0,
                     0,0,0,0,0,
                     0,0,0,0,0,
                     0,0,0,0,0,
                     0,0,0,0,0,
                     0,0,0,0,0,
                     0,0,0,0,0,
                     0,0,0,0,0,
                     1,0,0,0,0,
                     0,4,0,0,0,
                     0,0,4*3,0,0,
                     0,0,0,4*3*2,0,
                     0,0,0,0,4*3*2*1,
                     0,0,0,0,0]);
M4 := Transpose(M4);

a400 := MonomialCoefficient(f1new,x3^4);
a310 := MonomialCoefficient(f1new,x3^3*x2);
a301 := MonomialCoefficient(f1new,x3^3*x1);
a220 := MonomialCoefficient(f1new,x3^2*x2^2);
a211 := MonomialCoefficient(f1new,x3^2*x2*x1);
a202 := MonomialCoefficient(f1new,x3^2*x1^2);
a130 := MonomialCoefficient(f1new,x3*x2^3);
a121 := MonomialCoefficient(f1new,x3*x2^2*x1);
a112 := MonomialCoefficient(f1new,x3*x2*x1^2);
a103 := MonomialCoefficient(f1new,x3*x1^3);
a040 := MonomialCoefficient(f1new,x2^4);
a031 := MonomialCoefficient(f1new,x2^3*x1);
a022 := MonomialCoefficient(f1new,x2^2*x1^2);
a013 := MonomialCoefficient(f1new,x2*x1^3);
a004 := MonomialCoefficient(f1new,x1^4);

b400 := MonomialCoefficient(f2new,x3^4);
b310 := MonomialCoefficient(f2new,x3^3*x2);
b301 := MonomialCoefficient(f2new,x3^3*x1);
b220 := MonomialCoefficient(f2new,x3^2*x2^2);
b211 := MonomialCoefficient(f2new,x3^2*x2*x1);
b202 := MonomialCoefficient(f2new,x3^2*x1^2);
b130 := MonomialCoefficient(f2new,x3*x2^3);
b121 := MonomialCoefficient(f2new,x3*x2^2*x1);
b112 := MonomialCoefficient(f2new,x3*x2*x1^2);
b103 := MonomialCoefficient(f2new,x3*x1^3);
b040 := MonomialCoefficient(f2new,x2^4);
b031 := MonomialCoefficient(f2new,x2^3*x1);
b022 := MonomialCoefficient(f2new,x2^2*x1^2);
b013 := MonomialCoefficient(f2new,x2*x1^3);
b004 := MonomialCoefficient(f2new,x1^4);

v1 := Matrix(L,15,1,[a400,a310,a301,a220,a211,a202,a130,a121,a112,a103,a040,a031,a022,a013,a004]);
v2 := Matrix(L,15,1,[b400,b310,b301,b220,b211,b202,b130,b121,b112,b103,b040,b031,b022,b013,b004]);

Ti := T^(-1);

w41 := M4*Ti*v1;
w42 := M4*Ti*v2;

w81 := M8*Ti*v1;
w82 := M8*Ti*v2;

end if;

R<x,y> := PolynomialRing(L,2);
S<t> := PolynomialRing(L);
h := hom<R -> S | [t,1]>;

bq1 := w41[1,1]*x^4 + w41[2,1]*x^3*y + w41[3,1]*x^2*y^2 + w41[4,1]*x*y^3 + w41[5,1]*y^4;
bq2 := w42[1,1]*x^4 + w42[2,1]*x^3*y + w42[3,1]*x^2*y^2 + w42[4,1]*x*y^3 + w42[5,1]*y^4;
hbq1 := h(bq1);
hbq2 := h(bq2);

I1,J1,Delta1 := BinQuadInvs(bq1);
I2,J2,Delta2 := BinQuadInvs(bq2);
//Delta1;
//Delta2;
//"WPSTest:";
//WPSEqual([2,3],[I1,J1],[I2,J2]);
//Delta1;
//Delta2;

if Delta1 ne 0 then

test5,List := IsGL2GeometricEquivalent(hbq1,hbq2,4 : geometric := geometric);
//test5,List := IsGL2Equivalent(bq1,bq2);
//"test5:",test5;

if test5 then

Ts := [* *];
for l in List do
    FF := L;
    P2FF := ProjectiveSpace(FF,2);
    RFF<x1,x2,x3> := CoordinateRing(P2FF);
    f1newFF := f1new;
    f2newFF := f2new;
    TT1FF := Matrix(FF,3,3,ElementToSequence(TT1));
    TT2FF := Matrix(FF,3,3,ElementToSequence(TT2));
//    FF := Parent(l[1]);
//    P2FF := ProjectiveSpace(FF,2);
//    RFF<x1,x2,x3> := CoordinateRing(P2FF);
//    f1newFF := RFF ! f1new;
//    f2newFF := RFF ! f2new;
//    TT1FF := Matrix(FF,3,3,ElementToSequence(TT1));
//    TT2FF := Matrix(FF,3,3,ElementToSequence(TT2));

    a := l[1];
    b := l[3];
    c := l[2];
    d := l[4];

    T := Matrix(FF,3,3,[a^2,2*a*b,b^2,a*c,a*d+b*c,b*d,c^2,2*c*d,d^2]);
    if not cov then
        T := Transpose(T);
    else
        T := T^(-1);
    end if;

    test,factor := IsMultiple(TransformTernaryForm(f1newFF,T),f2newFF);
    if test then
        N := Normalize33(TT1FF*T*TT2FF^(-1));
        C := ElementToSequence(N);
        test := true;
        for i:=1 to #C do
            test := test and (C[i] in F);
        end for;
        if test then
            C0 := [ ];
            for c in C do
                Append(~C0,F!c);
            end for;
            Append(~Ts,Matrix(F,3,3,C0));
        end if;
    end if;
end for;
//Ts;
AssertTs(f1, f2, Ts);
return (#Ts ne 0),Ts,false;

else
    return false,[* *],false;
end if;

else

bo1 := w81[1,1]*x^8 + w81[2,1]*x^7*y + w81[3,1]*x^6*y^2 + w81[4,1]*x^5*y^3 + w81[5,1]*x^4*y^4
     + w81[6,1]*x^3*y^5 + w81[7,1]*x^2*y^6 + w81[8,1]*x*y^7 + w81[9,1]*y^8;
bo2 := w82[1,1]*x^8 + w82[2,1]*x^7*y + w82[3,1]*x^6*y^2 + w82[4,1]*x^5*y^3 + w82[5,1]*x^4*y^4
     + w82[6,1]*x^3*y^5 + w82[7,1]*x^2*y^6 + w82[8,1]*x*y^7 + w82[9,1]*y^8;

bq1T := Transvectant(bo1,bo1,6);
bq2T := Transvectant(bo2,bo2,6);
I1,J1,Delta1 := BinQuadInvs(bq1T);
I2,J2,Delta2 := BinQuadInvs(bq2T);
//WPSEqual([2,3],[I1,J1],[I2,J2]);
//Delta1;
//Delta2;

if Delta1 ne 0 then

test6,List := IsGL2GeometricEquivalent(h(bq1T),h(bq2T),4 : geometric := geometric);
//"test6:",test6;

if test6 then

Ts := [* *];
for l in List do
    FF := L;
    P2FF := ProjectiveSpace(FF,2);
    RFF<x1,x2,x3> := CoordinateRing(P2FF);
    f1newFF := f1new;
    f2newFF := f2new;
    TT1FF := Matrix(FF,3,3,ElementToSequence(TT1));
    TT2FF := Matrix(FF,3,3,ElementToSequence(TT2));
//    FF := Parent(l[1]);
//    P2FF := ProjectiveSpace(FF,2);
//    RFF<x1,x2,x3> := CoordinateRing(P2FF);
//    f1newFF := RFF ! f1new;
//    f2newFF := RFF ! f2new;
//    TT1FF := Matrix(FF,3,3,ElementToSequence(TT1));
//    TT2FF := Matrix(FF,3,3,ElementToSequence(TT2));

    a := l[1];
    b := l[3];
    c := l[2];
    d := l[4];

    T := Matrix(FF,3,3,[a^2,2*a*b,b^2,a*c,a*d+b*c,b*d,c^2,2*c*d,d^2]);
    if not cov then
        T := Transpose(T);
    else
        T := T^(-1);
    end if;

    test,factor := IsMultiple(TransformTernaryForm(f1newFF,T),f2newFF);
    if test then
        N := Normalize33(TT1FF*T*TT2FF^(-1));
        C := ElementToSequence(N);
        test := true;
        for i:=1 to #C do
            test := test and (C[i] in F);
        end for;
        if test then
            C0 := [* *];
            for c in C do
                Append(~C0,F!c);
            end for;
            Append(~Ts,Matrix(F,3,3,C0));
        end if;
    end if;
end for;
//Ts;
AssertTs(f1, f2, Ts);
return (#Ts ne 0),Ts,false;

else
    return false,[* *],false;
end if;
end if;

//We have a robust IsGL2 for octics!
hbo1 := h(bo1);
hbo2 := h(bo2);
if (Degree(hbo1) gt 6) and (Discriminant(hbo1) ne 0) then
test7,List := IsGL2GeometricEquivalent(hbo1,hbo2,8 : geometric := geometric);
//"test7:",test7;

if test7 then

Ts := [* *];
for l in List do
    FF := L;
    P2FF := ProjectiveSpace(FF,2);
    RFF<x1,x2,x3> := CoordinateRing(P2FF);
    f1newFF := f1new;
    f2newFF := f2new;
    TT1FF := Matrix(FF,3,3,ElementToSequence(TT1));
    TT2FF := Matrix(FF,3,3,ElementToSequence(TT2));
//    FF := Parent(l[1]);
//    P2FF := ProjectiveSpace(FF,2);
//    RFF<x1,x2,x3> := CoordinateRing(P2FF);
//    f1newFF := RFF ! f1new;
//    f2newFF := RFF ! f2new;
//    TT1FF := Matrix(FF,3,3,ElementToSequence(TT1));
//    TT2FF := Matrix(FF,3,3,ElementToSequence(TT2));

    a := l[1];
    b := l[3];
    c := l[2];
    d := l[4];

    T := Matrix(FF,3,3,[a^2,2*a*b,b^2,a*c,a*d+b*c,b*d,c^2,2*c*d,d^2]);
    if not cov then
        T := Transpose(T);
    else
        T := T^(-1);
    end if;

    test,factor := IsMultiple(TransformTernaryForm(f1newFF,T),f2newFF);
    if test then
        N := Normalize33(TT1FF*T*TT2FF^(-1));
        C := ElementToSequence(N);
        test := true;
        for i:=1 to #C do
            test := test and (C[i] in F);
        end for;
        if test then
            C0 := [* *];
            for c in C do
                Append(~C0,F!c);
            end for;
            Append(~Ts,Matrix(F,3,3,C0));
        end if;
    end if;
end for;
//Ts;
AssertTs(f1, f2, Ts);
return (#Ts ne 0),Ts,false;

else
    return false,[* *],false;
end if;

else

hbf1 := hbq1*hbo1;
hbf2 := hbq2*hbo2;
D1 := Derivative(hbf1);
D2 := Derivative(hbf2);
hbf1red := S! (hbf1 / GCD(hbf1,D1));
hbf2red := S! (hbf2 / GCD(hbf2,D2));
deg1 := Degree(hbf1red);
deg2 := Degree(hbf2red);
m := Max(deg1,deg2);
if (deg1 eq deg2) and (Degree(hbf1) lt 12) and (Degree(hbf2) lt 12) then
    m := m + 1;
end if;

test8,List := IsGL2GeometricEquivalent(hbf1red,hbf2red,m : geometric := geometric);
//"test8:",test8;

if test8 then

Ts := [* *];
for l in List do
    FF := L;
    P2FF := ProjectiveSpace(FF,2);
    RFF<x1,x2,x3> := CoordinateRing(P2FF);
    f1newFF := f1new;
    f2newFF := f2new;
    TT1FF := Matrix(FF,3,3,ElementToSequence(TT1));
    TT2FF := Matrix(FF,3,3,ElementToSequence(TT2));
//    FF := Parent(l[1]);
//    P2FF := ProjectiveSpace(FF,2);
//    RFF<x1,x2,x3> := CoordinateRing(P2FF);
//    f1newFF := RFF ! f1new;
//    f2newFF := RFF ! f2new;
//    TT1FF := Matrix(FF,3,3,ElementToSequence(TT1));
//    TT2FF := Matrix(FF,3,3,ElementToSequence(TT2));

    a := l[1];
    b := l[3];
    c := l[2];
    d := l[4];

    T := Matrix(FF,3,3,[a^2,2*a*b,b^2,a*c,a*d+b*c,b*d,c^2,2*c*d,d^2]);
    if not cov then
        T := Transpose(T);
    else
        T := T^(-1);
    end if;

    test,factor := IsMultiple(TransformTernaryForm(f1newFF,T),f2newFF);
    if test then
        N := Normalize33(TT1FF*T*TT2FF^(-1));
        C := ElementToSequence(N);
        test := true;
        for i:=1 to #C do
            test := test and (C[i] in F);
        end for;
        if test then
            C0 := [* *];
            for c in C do
                Append(~C0,F!c);
            end for;
            Append(~Ts,Matrix(F,3,3,C0));
        end if;
    end if;
end for;
//Ts;
AssertTs(f1, f2, Ts);
return (#Ts ne 0),Ts,false;

else
    return false,[* *],false;
end if;
end if;
end if;
end if;
end if;
end if;

end while;
/*
catch e
    test, Mss := SPQIsIsomorphic(f1, f2 : geometric := geometric);
    return test, &cat(Mss), true;
end try;
*/

test, Mss := SPQIsIsomorphic(f1, f2 : geometric := geometric);
return test, &cat(Mss), true;

end if;

end function;

