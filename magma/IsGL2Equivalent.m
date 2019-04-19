/***
 *  Equivalence of binary forms after Cremona-Fischer
 *
 *  Written by Jeroen Sijsling (jeroen.sijsling@uni-ulm.de)
 *
 *  See LICENSE.txt for license details.
 */


function IsGL2Equivalent(q1,q2)
//Exploits Cremona-Fisher for a general iso test.

R1<x,y> := Parent(q1);
S1<t> := PolynomialRing(BaseRing(R1));
h1 := hom<R1 -> S1 | [t,1]>;

F := BaseRing(R1);
R0<t> := PolynomialRing(F);

I1,J1,Delta1 := BinQuadInvs(q1);
I2,J2,Delta2 := BinQuadInvs(q2);
IJ1 := [I1,J1];
IJ2 := [I2,J2];

if not WPSEqual([2,3],IJ1,IJ2) then
    return false,[];
else
if I1*J1 ne 0 then
    //In this case, if there exists a relation  g2 = l g1^m  at all,
    //then  l  equals  (J2/I2)/(J1/I1)  up to squares.
    //After multiplying by it, we will have a proper equivalence
    q := (J2/I2)/(J1/I1);
    return IsCFProperlyEquivalent(q*q1,q2);
elif I1 ne 0 then
    //In this case, if there exists a relation  g2 = l g1^m  at all,
    //then we know  l^2  up to fourth powers; it equals  I2 / I1  .
    //We try proper equivalence for the two corresponding possibilities
    //for the rest class; if a relation exists, then one of these will
    //give a proper equivalence, and conversely such proper equivalences
    //yield  g2 = l g1^m  .

    //More detail: we see that  q = I2 / I1  is a square, say  mu^2  .
    //Replace  g1  by  mu g1  .
    //Then  g1 and g2  have the same invariants  I  . So suppose this from now on.
    //If  g2 = l g1^m  , then  l^2 det(M)^4 = 1  .
    //If  l det(M)^2 = 1  , then we have a proper equivalence by  (1/det(M), M)  between  g1 and g2.
    //If  l det(M)^2 = -1  , then we have a proper equivalence by  (1/det(M), M)  between  g1 and g2.
    //Conversely, in the case of a proper equivalence, we certainly have a GL_2-equivalence,
    //and we simply compose this with the old one.
    q := I2/I1;
    test,mu := IsSquare(q);
    if not test then
        return false,[];
    else
        test1,Ts1 := IsCFProperlyEquivalent(mu*q1,q2);
        test2,Ts2 := IsCFProperlyEquivalent(-mu*q1,q2);
        Ts := Ts1 cat Ts2;
        return (#Ts ne 0),Ts;
    end if;
elif J1 ne 0 then
    //Similar to the previous case.
    q := J2/J1;
    test,mu := IsPower(q,3);
    if not test then
        return false,[];
    else
        zs := Roots(t^3 - 1,F);
        Ts := [];
        for rs in zs do
            zeta3 := rs[1];
            test,Tsz := IsCFProperlyEquivalent(zeta3*mu*q1,q2);
            Ts := Ts cat Tsz;
        end for;
        return (#Ts ne 0),Ts;
    end if;
end if;
end if;

end function;

