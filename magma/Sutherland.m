/***
 *  Generic functionality by Drew Sutherland
 *
 *  See LICENSE.txt for license details.
 */


function DemPoints(S : geometric := false)

if not geometric then
    pts := Points(S);
else
    pts := PointsOverSplittingField(S);
end if;
return pts;

end function;


function SPQIsIsomorphic(f1, f2 : geometric := false)
// Tests isomorphism of smooth plane curves f(x,y,z)=0 by computing a matrix M in GL(3,F) such that f1^M is a scalar multiple of f2. 
    //require VariableWeights(Parent(f1)) eq [1,1,1]: "Inputs must be trivariate polynomials.";
    //require IsHomogeneous(f1) and Degree(f1) eq 4 and IsHomogeneous(f2) and Degree(f2) eq 4: "Input polynomials must be ternary quartic forms.";

    R := Parent(f1);
    if not IsField(BaseRing(R)) then R:=PolynomialRing(FieldOfFractions(BaseRing(R)),3); f1:=R!f1; f2:=R!f2; end if;
    f2 := R!f2; // make sure both f1 and f2 live in the same structure
    F := BaseRing(R);
    /*
     We need to determine whether there exists an invertible matrix M such that f1^M is a scalar multiple of f2.
     The matrix is determined only up to scaling; to reduce to a finite set, we set one of the entries equal to 1.
     This leads to three different cases, depending on which entry in the first row of M is the first nonzero entry.
    */

    // We begin with the most overdetermined case, with first row (0 0 1).
    Mss := [ ];
    A<[a]> := AffineSpace(F, 7);
    mat := Matrix(CoordinateRing(A), 3,3, [0,0,1] cat a[1..6]);
    PA := PolynomialRing(CoordinateRing(A), 3);
    h := hom< R -> PA | [ PA.1, PA.2, PA.3 ] >;
    fPA := h(f1);
    f1PA := h(f2);
    f2PA := fPA^mat;
    mons := MonomialsOfDegree(PA, 4);
    tworows := Matrix([[MonomialCoefficient(f1PA, m) : m in mons],
                       [MonomialCoefficient(f2PA, m) : m in mons]]);
    S := Scheme(A, Minors(tworows, 2) cat [Determinant(mat)*a[7]-1]);
    pts := DemPoints(S : geometric := geometric);
    Append(~Mss, [* Matrix(3,3, [0,0,1] cat Eltseq(pt)[1..6]) : pt in pts *]);

    // Now we look at first row (0 1 *).
    A<[a]> := AffineSpace(F, 8);
    mat := Matrix(CoordinateRing(A), 3,3, [0,1] cat a[1..7]);
    PA := PolynomialRing(CoordinateRing(A), 3);
    h := hom< R -> PA | [ PA.1, PA.2, PA.3 ] >;
    fPA := h(f1);
    f1PA := h(f2);
    f2PA := fPA^mat;
    mons := MonomialsOfDegree(PA, 4);
    tworows := Matrix([[MonomialCoefficient(f1PA, m) : m in mons],
                       [MonomialCoefficient(f2PA, m) : m in mons]]);
    S := Scheme(A, Minors(tworows, 2) cat [Determinant(mat)*a[8]-1]);
    pts := DemPoints(S : geometric := geometric);
    Append(~Mss, [* Matrix(3,3, [0,1] cat Eltseq(pt)[1..7]) : pt in pts *]);

    // Finally, the generic case, first row is (1 * *)
    A<[a]> := AffineSpace(F, 9);
    mat := Matrix(CoordinateRing(A), 3,3, [1] cat a[1..8]);
    PA := PolynomialRing(CoordinateRing(A), 3);
    h := hom< R -> PA | [ PA.1, PA.2, PA.3 ] >;
    fPA := h(f1);
    f1PA := h(f2);
    f2PA := fPA^mat;
    mons := MonomialsOfDegree(PA, 4);
    tworows := Matrix([[MonomialCoefficient(f1PA, m) : m in mons],
                       [MonomialCoefficient(f2PA, m) : m in mons]]);
    S := Scheme(A, Minors(tworows, 2) cat [Determinant(mat)*a[9]-1]);
    pts := DemPoints(S : geometric := geometric);
    Append(~Mss, [* Matrix(3,3, [1] cat Eltseq(pt)[1..8]) : pt in pts *]);

    // All together now
    for Ms in Mss do
        for M in Ms do
            Rcl := PolynomialRing(BaseRing(M), 3);
            h := hom< Parent(f1) -> Rcl | [ Rcl.1, Rcl.2, Rcl.3 ] >;
            g1 := h(f1); g2 := h(f2); g1M := g1^M;
            assert LeadingCoefficient(g2)*g1M eq LeadingCoefficient(g1M)*g2;
        end for;
    end for;
    return &or[ #Ms ne 0 : Ms in Mss ], Mss;
end function;
