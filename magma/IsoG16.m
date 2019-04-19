/***
 *  Quartic isomorphisms for automorphism group G16
 *
 *  Written by Jeroen Sijsling (jeroen.sijsling@uni-ulm.de)
 *
 *  See LICENSE.txt for license details.
 */


import "Ingredients.m": TransformBinaryForm;


function IsoG16(f01,f02 : geometric := false);

Ts := [];

F := BaseRing(Parent(f01));
P2<x,y,z> := ProjectiveSpace(F,2);
R2<x,y,z> := CoordinateRing(P2);
R<s,t> := PolynomialRing(F,2);
S<u> := PolynomialRing(F);
h := hom<R -> S | [u,1]>;

f1 := R2!f01;
f2 := R2!f02;

C1 := Curve(P2,f1);
C2 := Curve(P2,f2);

F1 := Flexes(C1);
F2 := Flexes(C2);

HF1 := SingularSubscheme(F1);
HF2 := SingularSubscheme(F2);

HFPts1,FF1 := PointsOverSplittingField(HF1);
HFPts2,FF2 := PointsOverSplittingField(HF2);

C1ext := BaseExtend(C1,FF1);
C2ext := BaseExtend(C2,FF2);

//x1-coordinate determined by vanishing on four hyperflexes
pt1 := HFPts1[1];
pt2 := HFPts1[2];
M := Matrix(FF1,2,3,[pt1[1],pt1[2],pt1[3],pt2[1],pt2[2],pt2[3]]);
N := NullSpace(Transpose(M));
nx1 := N.1;
nx1 := [F!nx1[1],F!nx1[2],F!nx1[3]];
x1 := nx1[1]*x + nx1[2]*y + nx1[3]*z;

//Determining intersection of the four hyperflexes
L1 := TangentLine(C1ext,C1ext![pt1[1],pt1[2],pt1[3]]);
L2 := TangentLine(C1ext,C1ext![pt2[1],pt2[2],pt2[3]]);

LInt := L1 meet L2;
LIntPts := PointsOverSplittingField(LInt);
LIntPt := [F!LIntPts[1][1],F!LIntPts[1][2],F!LIntPts[1][3]];

//Choosing  y1 and z1  accordingly
M := Matrix(FF1,1,3,[LIntPt[1],LIntPt[2],LIntPt[3]]);
N := NullSpace(Transpose(M));
n1 := N.1;
n2 := N.2;

ny1 := [F!n1[1],F!n1[2],F!n1[3]];
y1 := ny1[1]*x + ny1[2]*y + ny1[3]*z;
nz1 := [F!n2[1],F!n2[2],F!n2[3]];
z1 := nz1[1]*x + nz1[2]*y + nz1[3]*z;

//x2-coordinate determined by vanishing on four hyperflexes
pt1 := HFPts2[1];
pt2 := HFPts2[2];
M := Matrix(FF2,2,3,[pt1[1],pt1[2],pt1[3],pt2[1],pt2[2],pt2[3]]);
N := NullSpace(Transpose(M));
nx2 := N.1;
nx2 := [F!nx2[1],F!nx2[2],F!nx2[3]];
x2 := nx2[1]*x + nx2[2]*y + nx2[3]*z;

//Determining intersection of the four hyperflexes
L1 := TangentLine(C2ext,C2ext![pt1[1],pt1[2],pt1[3]]);
L2 := TangentLine(C2ext,C2ext![pt2[1],pt2[2],pt2[3]]);

LInt := L1 meet L2;
LIntPts := PointsOverSplittingField(LInt);
LIntPt := [F!LIntPts[1][1],F!LIntPts[1][2],F!LIntPts[1][3]];

//Choosing  y2 and z2  accordingly
M := Matrix(FF2,1,3,[LIntPt[1],LIntPt[2],LIntPt[3]]);
N := NullSpace(Transpose(M));
n1 := N.1;
n2 := N.2;

ny2 := [F!n1[1],F!n1[2],F!n1[3]];
y2 := ny2[1]*x + ny2[2]*y + ny2[3]*z;
nz2 := [F!n2[1],F!n2[2],F!n2[3]];
z2 := nz2[1]*x + nz2[2]*y + nz2[3]*z;

//Transforming to standard form:
U1 := Matrix(F,3,3,[nx1[1],nx1[2],nx1[3],ny1[1],ny1[2],ny1[3],nz1[1],nz1[2],nz1[3]]);
g1 := TransformForm(f1,U1^(-1));
g1 := g1/MonomialCoefficient(g1,x^4);

U2 := Matrix(F,3,3,[nx2[1],nx2[2],nx2[3],ny2[1],ny2[2],ny2[3],nz2[1],nz2[2],nz2[3]]);
g2 := TransformForm(f2,U2^(-1));
g2 := g2/MonomialCoefficient(g2,x^4);

//Finding isomorphisms between binary forms
a1 := MonomialCoefficient(g1,y^4);
b1 := MonomialCoefficient(g1,y^3*z);
c1 := MonomialCoefficient(g1,y^2*z^2);
d1 := MonomialCoefficient(g1,y*z^3);
e1 := MonomialCoefficient(g1,z^4);
bq1 := a1*s^4 + b1*s^3*t + c1*s^2*t^2 + d1*s*t^3 + e1*t^4;

a2 := MonomialCoefficient(g2,y^4);
b2 := MonomialCoefficient(g2,y^3*z);
c2 := MonomialCoefficient(g2,y^2*z^2);
d2 := MonomialCoefficient(g2,y*z^3);
e2 := MonomialCoefficient(g2,z^4);
bq2 := a2*s^4 + b2*s^3*t + c2*s^2*t^2 + d2*s*t^3 + e2*t^4;

test1,L := IsGL2GeometricEquivalent(h(bq1),h(bq2),4 : geometric := geometric);

if test1 then
for C in L do
    FF := Parent(C[1]);
    RFF := PolynomialRing(FF,2);
    U1FF := Matrix(FF,3,3,ElementToSequence(U1));
    U2FF := Matrix(FF,3,3,ElementToSequence(U2));
    bq1FF := RFF ! bq1;
    bq2FF := RFF ! bq2;

    M := Matrix(FF,2,2,C);
    bla,lambda := IsMultiplePolynomial(TransformBinaryForm(bq1FF,M),bq2FF);
    lambda := lambda[1,1];
    lambda := 1/lambda;
    FFF := FF;
    S<t> := PolynomialRing(FF);
    if geometric then
        FFF := SplittingField(t^4 - lambda);
    end if;

    RFFF := PolynomialRing(FFF,2);
    U1FFF := Matrix(FFF,3,3,ElementToSequence(U1));
    U2FFF := Matrix(FFF,3,3,ElementToSequence(U2));

    Rs := Roots(t^4 - lambda,FFF);
    for R in Rs do
        r := R[1];
        N := Matrix(FFF,3,3,[r,0,0,0,M[1,1],M[1,2],0,M[2,1],M[2,2]]);
        T := U2FFF^(-1)*N^(-1)*U1FFF;
        T := T^(-1);
        Append(~Ts, T);
    end for;
end for;
end if;

return (#Ts ne 0),Ts;

end function;
