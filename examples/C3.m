/* Examples with group C3 */

N := 10^100;
F := FiniteField(NextPrime(N));
//F := FiniteField(5);
//F := Rationals();
P2<x,y,z> := ProjectiveSpace(F,2);

f1 := x^3*z + y^4 + y^2*z^2 + 2*y*z^3 - 3*z^4;
f2 := 7*x^3*z + y^4 + y^2*z^2 + 2*y*z^3 - 3*z^4;
f2 := f1;
//f := x^3*z + y^4 + z*(3*y + z)^3;

for i:=1 to 2^5 do
    repeat
        T1 := Matrix(F,3,3,[Random([-N..N]),Random([-N..N]),Random([-N..N]),Random([-N..N]),Random([-N..N]),Random([-N..N]),Random([-N..N]),Random([-N..N]),Random([-N..N])]);
        T2 := Matrix(F,3,3,[Random([-N..N]),Random([-N..N]),Random([-N..N]),Random([-N..N]),Random([-N..N]),Random([-N..N]),Random([-N..N]),Random([-N..N]),Random([-N..N])]);
    until (Determinant(T1) ne 0) and (Determinant(T2) ne 0);

    g1 := map<P2 -> P2 | [T1[1,1]*x+T1[1,2]*y+T1[1,3]*z,T1[2,1]*x+T1[2,2]*y+T1[2,3]*z,T1[3,1]*x+T1[3,2]*y+T1[3,3]*z]>;
    g1 := AlgebraMap(g1);
    stopa1 := false;
    while not stopa1 do
        a1 := Random([-N..N]);
        stopa1 := a1 ne 0;
    end while;
    f1 := a1*g1(f1);

    g2 := map<P2 -> P2 | [T2[1,1]*x+T2[1,2]*y+T2[1,3]*z,T2[2,1]*x+T2[2,2]*y+T2[2,3]*z,T2[3,1]*x+T2[3,2]*y+T2[3,3]*z]>;
    g2 := AlgebraMap(g2);
    stopa2 := false;
    while not stopa2 do
        a2 := Random([-N..N]);
        stopa2 := a2 ne 0;
    end while;
    f2 := a2*g2(f2);

    time test,Ts,StF := QuarticIsomorphisms(f1,f2);
    //test;
    //"Memory used:";
    //Memory();

    //"Standard form of the curves used:";
    //StF;

    //"Transformation tests:";
    FF := Parent(Ts[1][1,1]);
    P2FF<x,y,z> := ProjectiveSpace(FF,2);
    R2FF<x,y,z> := CoordinateRing(P2FF);
    f1FF := R2FF ! f1;
    f2FF := R2FF ! f2;
    for T in Ts do
        if not IsMultiplePolynomial(TransformForm(f1FF,T),f2FF) then
            error "SOMETHING WENT WRONG, PLEASE TELL ME!";
        end if;
    end for;
end for;
