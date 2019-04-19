/***
 *  Proper equivalence of binary forms after Cremona-Fischer
 *
 *  Written by Jeroen Sijsling (jeroen.sijsling@uni-ulm.de)
 *
 *  See LICENSE.txt for license details.
 */


function IsCFProperlyEquivalent(q1,q2)
//After Cremona-Fisher.

R1<x,y> := Parent(q1);
S1<t> := PolynomialRing(BaseRing(R1));
h1 := hom<R1 -> S1 | [t,1]>;

F := BaseRing(R1);
R3<x1,y1,x2,y2> := PolynomialRing(F,4);

//Coefficients in standard notation
a1 := MonomialCoefficient(q1,x^4);
b1 := MonomialCoefficient(q1,x^3*y);
c1 := MonomialCoefficient(q1,x^2*y^2);
d1 := MonomialCoefficient(q1,x*y^3);
e1 := MonomialCoefficient(q1,y^4);

a2 := MonomialCoefficient(q2,x^4);
b2 := MonomialCoefficient(q2,x^3*y);
c2 := MonomialCoefficient(q2,x^2*y^2);
d2 := MonomialCoefficient(q2,x*y^3);
e2 := MonomialCoefficient(q2,y^4);

//Associated Hessians and sextics
H1 := (3*b1^2 - 8*a1*c1)*x^4 + 4*(b1*c1 - 6*a1*d1)*x^3*y + 2*(2*c1^2 - 24*a1*e1 - 3*b1*d1)*x^2*y^2 + 4*(c1*d1 - 6*b1*e1)*x*y^3 + (3*d1^2 - 8*c1*e1)*y^4;
H2 := (3*b2^2 - 8*a2*c2)*x^4 + 4*(b2*c2 - 6*a2*d2)*x^3*y + 2*(2*c2^2 - 24*a2*e2 - 3*b2*d2)*x^2*y^2 + 4*(c2*d2 - 6*b2*e2)*x*y^3 + (3*d2^2 - 8*c2*e2)*y^4;

//Some inclusion and projection morphisms of rings
f1 := hom<R1 -> R3 | [x1,y1]>;
f2 := hom<R1 -> R3 | [x2,y2]>;
p1 := hom<R3 -> R1 | [1,0,x,y]>;
p2 := hom<R3 -> R1 | [0,1,x,y]>;
p3 := hom<R3 -> R1 | [1,1,x,y]>;

//CF's  F
CFF := f1(q1)*f2(H2) - f2(q2)*f1(H1);

//Interpolate and find factorization.
CFFev1 := p1(CFF);
CFFev2 := p2(CFF);
CFFev3 := p3(CFF);

Fac1 := Factorization(CFFev1);
Fac2 := Factorization(CFFev2);
Fac3 := Factorization(CFFev3);

FacL1 := [];
for fac1 in Fac1 do
if Degree(fac1[1]) eq 1 then
    Append(~FacL1,fac1[1]);
end if;
end for;

FacL2 := [];
for fac2 in Fac2 do
if Degree(fac2[1]) eq 1 then
    Append(~FacL2,fac2[1]);
end if;
end for;

FacL3 := [];
for fac3 in Fac3 do
if Degree(fac3[1]) eq 1 then
    Append(~FacL3,fac3[1]);
end if;
end for;

Rats1 := [];
for fac1 in FacL1 do
    Append(~Rats1,[MonomialCoefficient(fac1,x),MonomialCoefficient(fac1,y)]);
end for;

Rats2 := [];
for fac2 in FacL2 do
    Append(~Rats2,[MonomialCoefficient(fac2,x),MonomialCoefficient(fac2,y)]);
end for;

Rats3 := [];
for fac3 in FacL3 do
    Append(~Rats3,[MonomialCoefficient(fac3,x),MonomialCoefficient(fac3,y)]);
end for;

TentFacts := [];
for r1 in Rats1 do
for r2 in Rats2 do
for r3 in Rats3 do
lambda1 := r1[1];
mu1 := r1[2];
lambda2 := r2[1];
mu2 := r2[2];
lambda3 := r3[1];
mu3 := r3[2];
M := Matrix(F,3,4,[-mu1,lambda1,0,0,
                   0,0,-mu2,lambda2,
                   -mu3,lambda3,-mu3,lambda3]);
N := NullSpace(Transpose(M));
d := Dimension(N);
if d eq 1 then
    v := N.1;
    tf := v[1]*x1*x2 + v[2]*x1*y2 + v[3]*y1*x2 + v[4]*y1*y2;
    Append(~TentFacts,tf);
end if;
end for;
end for;
end for;

Facts := [];
for tf in TentFacts do
    if IsDivisibleBy(CFF,tf) then
        Append(~Facts,tf);
    end if;
end for;

L := [];
for Fac in Facts do
    m := Matrix(F,2,2,[MonomialCoefficient(Fac,x1*x2),MonomialCoefficient(Fac,y1*x2),
                       MonomialCoefficient(Fac,x1*y2),MonomialCoefficient(Fac,y1*y2)])
         *Matrix(F,2,2,[0,1,-1,0]);
//    sqtest,r := IsSquare(Determinant(m));
//    if sqtest then
//        m0 := m/r;
        m0 := m;
        m0 := Transpose(m0^(-1));
//        trtest := IsMultiple(q1,TransformBinaryForm(q2,m0));
        trtest := true;
        if trtest then
            Append(~L,Normalize22(m0));
        end if;
//    end if;
end for;

test := (#L ne 0);
return test,L;

end function;

