/***
 *  Quartic isomorphisms for automorphism group C3
 *
 *  Written by Jeroen Sijsling (jeroen.sijsling@uni-ulm.de)
 *
 *  See LICENSE.txt for license details.
 */


import "Ingredients.m": FlexesThroughPoint, AssertTs;


function IsoC3(f01,f02 : geometric := false);

Ts := [* *];

F := BaseRing(Parent(f01));
P2<x,y,z> := ProjectiveSpace(F,2);
R2<x,y,z> := CoordinateRing(P2);
S<t> := PolynomialRing(F);

f1 := R2!f01;
f2 := R2!f02;

C1 := Curve(P2,f1);
C2 := Curve(P2,f2);

F1 := Flexes(C1);
F2 := Flexes(C2);

HF1 := SingularSubscheme(F1);
HF2 := SingularSubscheme(F2);

Deg1 := Degree(HF1);
Deg2 := Degree(HF2);

HFPts1 := Points(HF1);
HFPts2 := Points(HF2);

if (Deg1 ne Deg2) or (#HFPts1 ne #HFPts2) then
     return false,[* *],f01;
else
for i := 1 to #Points(HF1) do

//z1-coordinate determined by vanishing on a tangent line.
HF1 := [HFPts1[i][1],HFPts1[i][2],HFPts1[i][3]];
C1HF1 := C1!HF1;
TL1 := DefiningEquation(TangentLine(C1,C1HF1));
nz1 := [MonomialCoefficient(TL1,x),MonomialCoefficient(TL1,y),MonomialCoefficient(TL1,z)];

//y1  complement to  z1  vanishing in  (1,0,0)  .
M := Matrix(F,1,3,HF1);
N := NullSpace(Transpose(M));
ny1 := N.1;
if ny1 in sub<N | N!nz1> then
    ny1 := N.1 + N.2;
end if;

//x1-coordinate determined by containing 4 flexes whose flexlines intersect in the hyperflex.
Pts1,FF1 := FlexesThroughPoint(f1,HF1);
if #Pts1 eq 4 then
pt1 := Pts1[1];
pt2 := Pts1[2];
M := Matrix(FF1,2,3,[pt1[1],pt1[2],pt1[3],pt2[1],pt2[2],pt2[3]]);
N := NullSpace(Transpose(M));
nx1 := N.1;
nx1 := [F!nx1[1],F!nx1[2],F!nx1[3]];

U1 := Matrix(F,3,3,[nx1[1],nx1[2],nx1[3],ny1[1],ny1[2],ny1[3],nz1[1],nz1[2],nz1[3]]);
g1 := TransformForm(f1,U1^(-1));

for j := 1 to #Points(HF2) do

//z2-coordinate determined by vanishing on a tangent line.
HF2 := [HFPts2[j][1],HFPts2[j][2],HFPts2[j][3]];
C2HF2 := C2!HF2;
TL2 := DefiningEquation(TangentLine(C2,C2HF2));
nz2 := [MonomialCoefficient(TL2,x),MonomialCoefficient(TL2,y),MonomialCoefficient(TL2,z)];

//y2  complement to  z2  vanishing in  (1,0,0)  .
M := Matrix(F,1,3,HF2);
N := NullSpace(Transpose(M));
ny2 := N.1;
if ny2 in sub<N | N!nz2> then
    ny2 := N.1 + N.2;
end if;

//x2-coordinate determined by containing 4 flexes whose flexlines intersect in the hyperflex.
Pts2,FF2 := FlexesThroughPoint(f2,HF2);
if #Pts2 eq 4 then
pt1 := Pts2[1];
pt2 := Pts2[2];
M := Matrix(FF2,2,3,[pt1[1],pt1[2],pt1[3],pt2[1],pt2[2],pt2[3]]);
N := NullSpace(Transpose(M));
nx2 := N.1;
nx2 := [F!nx2[1],F!nx2[2],F!nx2[3]];

U2 := Matrix(F,3,3,[nx2[1],nx2[2],nx2[3],ny2[1],ny2[2],ny2[3],nz2[1],nz2[2],nz2[3]]);
g2 := TransformForm(f2,U2^(-1));

//We have two standard equations. Now we put their traces equal to zero.
V1 := Matrix(F,3,3,[1,0,0,0,1,MonomialCoefficient(g1,y^3*z)/(4*MonomialCoefficient(g1,y^4)),0,0,1]);
h1 := TransformForm(g1,V1^(-1));
h1 := h1 / MonomialCoefficient(h1,x^3*z);
V2 := Matrix(F,3,3,[1,0,0,0,1,MonomialCoefficient(g2,y^3*z)/(4*MonomialCoefficient(g2,y^4)),0,0,1]);
h2 := TransformForm(g2,V2^(-1));
h2 := h2 / MonomialCoefficient(h2,x^3*z);

//Now to start  x^3 z + y^4 + ...
W1 := Matrix(F,3,3,[1,0,0,0,1,0,0,0,(MonomialCoefficient(h1,y^4))^(-1)]);
i1 := TransformForm(h1,W1^(-1));
i1 := i1 / MonomialCoefficient(i1,x^3*z);
W2 := Matrix(F,3,3,[1,0,0,0,1,0,0,0,(MonomialCoefficient(h2,y^4))^(-1)]);
i2 := TransformForm(h2,W2^(-1));
i2 := i2 / MonomialCoefficient(i2,x^3*z);

//Isomorphisms between standard forms:
a1 := MonomialCoefficient(i1,y^2*z^2);
b1 := MonomialCoefficient(i1,y*z^3);
c1 := MonomialCoefficient(i1,z^4);
a2 := MonomialCoefficient(i2,y^2*z^2);
b2 := MonomialCoefficient(i2,y*z^3);
c2 := MonomialCoefficient(i2,z^4);

if not WPSEqual([2,3,4],[a1,b1,c1],[a2,b2,c2]) then
    return false,[* *],f01;
else
//The  bi  are non-zero in this stratum.
if a1 ne 0 then
    lambda3 := (b1/a1)/(b2/a2);
    K := F;
    if geometric then
        K := SplittingField(t^3 - lambda3);
    end if;
    rs := Roots(t^3 - lambda3,K);
    for r in rs do
        lambda := r[1];
        X := Matrix(K,3,3,[1,0,0,0,lambda,0,0,0,lambda^4]);
        T := (W2*V2*U2)^(-1) * X * W1*V1*U1;
        Append(~Ts,T^(-1));
        StF := i1;
    end for;
else
    lambda3 := (c1/b1)/(c2/b2);
    K := F;
    if geometric then
        K := SplittingField(t^3 - lambda3);
    end if;
    rs := Roots(t^3 - lambda3,K);
    for r in rs do
        lambda := r[1];
        X := Matrix(K,3,3,[1,0,0,0,lambda,0,0,0,lambda^4]);
        T := (W2*V2*U2)^(-1) * X * W1*V1*U1;
        Append(~Ts,T^(-1));
        StF := i1;
    end for;
end if;
end if;

end if;
end for;
end if;
end for;

if #Ts eq 0 then
    return false,[* *],0;
else
    AssertTs(f1, f2, Ts : geometric := geometric);
    return (#Ts ne 0),Ts,StF;
end if;

end if;

end function;

