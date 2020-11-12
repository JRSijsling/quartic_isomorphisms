/* Examples with group C3 */
SetVerbose("QuarticIso", 1);

N := 10^100;
F := FiniteField(NextPrime(N));
//F := FiniteField(5);
F := Rationals(); N := 10;
P2<x,y,z> := ProjectiveSpace(F,2);

f1 := x^3*z + y^4 + y^2*z^2 + 2*y*z^3 - 3*z^4;
f2 := 7*x^3*z + y^4 + y^2*z^2 + 2*y*z^3 - 3*z^4;
f2 := f1;
//f := x^3*z + y^4 + z*(3*y + z)^3;

/* Note that coefficient size keeps increasing */
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

    time test,Ts,IINeeded := QuarticIsomorphisms(f1,f2);
    time test,Ts,IINeeded := QuarticIsomorphisms(f1,f2 : geometric := true);

    if (not test) and (not IINeeded) then
        //stop := true;
        print f1;
        print f2;
        error "SOMETHING WENT WRONG, PLEASE TELL ME!";
    end if;

    //"Transformation tests:";
    for T in Ts do
        FF := Parent(T[1,1]);
        P2FF<x,y,z> := ProjectiveSpace(FF,2);
        R2FF<x,y,z> := CoordinateRing(P2FF);
        f1FF := R2FF ! f1;
        f2FF := R2FF ! f2;
        if not IsMultiplePolynomial(TransformForm(f1FF,T), f2FF) then
            print #Ts;
            print T;
            print Determinant(T);
            I1, W1 := DixmierOhnoInvariants(f1);
            I2, W2 := DixmierOhnoInvariants(f2);
            print WPSNormalize(W1, I1);
            print WPSNormalize(W2, I2);
            error "SOMETHING WENT WRONG, PLEASE TELL ME!";
        end if;
    end for;

    if IINeeded then
        if test then
            print "Usual isomorphism test needed";
        else
            print "Usual isomorphism test needed, BUT FAILS";
        end if;
    end if;
end for;
