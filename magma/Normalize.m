/***
 *  Normalize automorphisms of order 2
 *
 *  Written by Jeroen Sijsling (jeroen.sijsling@uni-ulm.de)
 *
 *  See LICENSE.txt for license details.
 */


intrinsic MinimizeC2Quartic(f::RngMPolElt : minimize := true) -> .
{Normalizes a ternary quartic form with few automorphisms.}

R := Parent(f);
x := R.1; y := R.2; z := R.3;
F := BaseRing(R);
if not Type(F) eq FldRat then
    minimize := false;
end if;

f0 := f; counter := 0;
while true do
    counter +:= 1;
    f := f0;
    test, Ts := QuarticIsomorphisms(f, f);
    Ts := [ T : T in Ts | IsScalar(T^2) and not IsScalar(T) ];
    if #Ts ne 1 then
        return R ! f, CyclicGroup(1);
    end if;
    T := Ts[1];
    D, U := JordanForm(T);

    f := TransformForm(f, U^(-1));
    if D[1,1] eq D[2,2] then
        f := Evaluate(f, [z,y,x]);
    end if;
    cs := Coefficients(f);
    f *:= LCM([ Denominator(c) : c in cs ]);
    f /:= GCD([ Numerator(c) : c in cs ]);

    mons4 := [ x^4 ];
    mons2 := [ x^2*y^2, x^2*y*z, x^2*z^2 ];
    mons0 := [ y^4, y^3*z, y^2*z^2, y*z^3, z^4 ];

    gcd4 := GCD([ Numerator(MonomialCoefficient(f, mon)) : mon in mons4 ]);
    gcd2 := GCD([ Numerator(MonomialCoefficient(f, mon)) : mon in mons2 ]);
    gcd0 := GCD([ Numerator(MonomialCoefficient(f, mon)) : mon in mons0 ]);
    gcd := GCD(gcd2, gcd4);
    ps := [ tup[1] : tup in Factorization(gcd) ];
    for p in ps do
        e := Minimum([ Valuation(gcd2, p), Valuation(gcd4, p) div 2 ]);
        q := p^e;
        f := &+[ (MonomialCoefficient(f, mon) / q^2)*mon : mon in mons4 ] + &+[ (MonomialCoefficient(f, mon) / q^1)*mon : mon in mons2 ] + &+[ (MonomialCoefficient(f, mon) / q^0)*mon : mon in mons0 ];
    end for;

    gcd4 := GCD([ Numerator(MonomialCoefficient(f, mon)) : mon in mons4 ]);
    gcd2 := GCD([ Numerator(MonomialCoefficient(f, mon)) : mon in mons2 ]);
    gcd0 := GCD([ Numerator(MonomialCoefficient(f, mon)) : mon in mons0 ]);
    gcd := GCD(gcd2, gcd0);
    ps := [ tup[1] : tup in Factorization(gcd) ];
    for p in ps do
        e := Minimum([ Valuation(gcd2, p), Valuation(gcd0, p) div 2 ]);
        q := p^e;
        f := &+[ (MonomialCoefficient(f, mon) / q^0)*mon : mon in mons4 ] + &+[ (MonomialCoefficient(f, mon) / q^1)*mon : mon in mons2 ] + &+[ (MonomialCoefficient(f, mon) / q^2)*mon : mon in mons0 ];
    end for;

    cs := Coefficients(f);
    f *:= LCM([ Denominator(c) : c in cs ]);
    f /:= GCD([ Numerator(c) : c in cs ]);
    vprint QuarticIso : "";
    vprint QuarticIso : "Normalized curve:";
    vprint QuarticIso : f;

    f := MinimizeReducePlaneQuartic(f);
    vprint QuarticIso : "";
    vprint QuarticIso : "Reduced normalized curve:";
    vprint QuarticIso : f;

    if f eq f0 or counter eq 12 then
        break;
    end if;
    f0 := f;
end while;

return R ! f, CyclicGroup(2);

end intrinsic;


intrinsic MinimizeC2Quartic(X::CrvPln : minimize := true) -> .
{Normalizes a plane quartic curve with few automorphisms.}

f := DefiningPolynomial(X);
assert Degree(f) eq 4;
return PlaneCurve(MinimizeC2Quartic(f : minimize := minimize));

end intrinsic;
