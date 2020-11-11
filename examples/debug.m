/* Examples over finite fields */
SetVerbose("QuarticIso", 1);

N := 50;
F := FiniteField(NextPrime(10^N));
F := FiniteField(19);
//F := Rationals();
P2<x,y,z> := ProjectiveSpace(F,2);

f := x^3*y+y^3*z+z^3*x;
f := x^3*y+y^3*z+z^4;
f := x^4+y^4+z^4+3*(x^2*y^2+y^2*z^2);
//f := x^4 + y^4 + z^4;

test, isos := QuarticIsomorphisms(f, f : geometric := true);
print [ BaseRing(iso) : iso in isos ];

