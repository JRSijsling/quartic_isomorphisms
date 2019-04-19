/* Examples over the rationals */

N := 250;
M := 50;

P2<x,y,z> := ProjectiveSpace(Rationals(),2);
F := Rationals();

stop := false;
while not stop do

    repeat
        f  := Random([-N..N])*x^4 + Random([-N..N])*x^3*y + Random([-N..N])*x^2*y^2 + Random([-N..N])*x*y^3 + Random([-N..N])*y^4 + Random([-N..N])*x^3*z + Random([-N..N])*x^2*y*z + Random([-N..N])*x*y^2*z + Random([-N..N])*y^3*z + Random([-N..N])*x^2*z^2 + Random([-N..N])*x*y*z^2 + Random([-N..N])*y^2*z^2 + Random([-N..N])*x*z^3 + Random([-N..N])*y*z^3 + Random([-N..N])*z^4;
        T1 := Matrix(F,3,3,[Random([-M..M]),Random([-M..M]),Random([-M..M]),Random([-M..M]),Random([-M..M]),Random([-M..M]),Random([-M..M]),Random([-M..M]),Random([-M..M])]);
        T2 := Matrix(F,3,3,[Random([-M..M]),Random([-M..M]),Random([-M..M]),Random([-M..M]),Random([-M..M]),Random([-M..M]),Random([-M..M]),Random([-M..M]),Random([-M..M])]);
    until f ne 0 and (Determinant(T1) ne 0) and (Determinant(T2) ne 0);
    I := DixmierOhnoInvariants(f);

    if I[13] ne 0 then

        g1 := map<P2 -> P2 | [T1[1,1]*x+T1[1,2]*y+T1[1,3]*z,T1[2,1]*x+T1[2,2]*y+T1[2,3]*z,T1[3,1]*x+T1[3,2]*y+T1[3,3]*z]>;
        g1 := AlgebraMap(g1);
        stopa1 := false;
        while not stopa1 do
            a1 := Random([-N..N]);
            stopa1 := a1 ne 0;
        end while;
        f1 := a1*g1(f);

        g2 := map<P2 -> P2 | [T2[1,1]*x+T2[1,2]*y+T2[1,3]*z,T2[2,1]*x+T2[2,2]*y+T2[2,3]*z,T2[3,1]*x+T2[3,2]*y+T2[3,3]*z]>;
        g2 := AlgebraMap(g2);
        stopa2 := false;
        while not stopa2 do
            a2 := Random([-N..N]);
            stopa2 := a2 ne 0;
        end while;
        f2 := a2*g2(f);

        time test,Ts,IINeeded := QuarticIsomorphisms(f1,f2);
        //test,Ts,IINeeded := QuarticIsoQQ(f1,f2,P2);
        //Ts;

        if (not test) and (not IINeeded) then
            //stop := true;
            print f;
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
            if not IsMultiplePolynomial(TransformForm(f1FF,T),f2FF) then
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
    end if;
end while;


