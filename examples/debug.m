/* Examples over finite fields */
SetVerbose("QuarticIso", 1);

N := 50;
F := FiniteField(NextPrime(10^N));
F := FiniteField(19);
F := Rationals();
P2<x,y,z> := ProjectiveSpace(F,2);

fs := [ ];
f := x^3*y+y^3*z+z^3*x; Append(~fs, f);
f := x^3*y+y^3*z+z^4; Append(~fs, f);
f := x^4+y^4+z^4+3*(x^2*y^2+y^2*z^2); Append(~fs, f);
f := x^4 + y^4 + z^4; Append(~fs, f);

for f in fs do
    test, isos := QuarticIsomorphisms(f, f : geometric := true);
    print BaseRing(isos[1]);
end for;

