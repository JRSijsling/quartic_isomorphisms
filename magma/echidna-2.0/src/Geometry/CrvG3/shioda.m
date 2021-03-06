//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//         Copyright (C) 2007 David Kohel <kohel@iml.univ-mrs.fr>           //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic ShiodaInvariants(C::CrvHyp) -> SeqEnum
    {}
    K := BaseRing(C);
    require Characteristic(K) notin {2,3,5,7} :
	"Argument must be defined over a field of characteristic not in {2,3,5,7}.";
    f, h := HyperellipticPolynomials(C);
    require h eq 0 and Degree(f) in [7,8] :
	"Argument must be a simplified model of genus 3.";
    P := PolynomialRing(K,2); X := P.1; Y := P.2;
    F := Numerator(Evaluate(f,X/Y));
    if TotalDegree(F) eq 7 then F *:= Y; end if;
    return ShiodaInvariants(F);
end intrinsic;

intrinsic ShiodaInvariants(F::RngMPolElt) -> SeqEnum
    {Given a homogeneous binary octavic over K, return the invariants
    J2, J3, ..., J10 of Shioda, such that J2, J3, ..., J7 are algebraically
    independent and K[J2,...,J10] is a free K[J2,...,J7]-module of rank 5,
    generated by 1, J8, J9, J10, J9^2.} 
    P := Parent(F);
    K := BaseRing(P);
    require Characteristic(K) notin {2,3,5,7} :
	"Argument must be defined over a field of characteristic not in {2,3,5,7}.";
    require Rank(P) eq 2 and IsHomogeneous(F) and TotalDegree(F) eq 8 :
	"Argument must be a homogeneous bivariate octavic.";
    H := Transvectant(F,F,2); // 
    g := Transvectant(F,F,4);
    k := Transvectant(F,F,6);
    h := Transvectant(k,k,2);
    m := Transvectant(F,k,4);
    n := Transvectant(F,h,4);
    p := Transvectant(g,k,4);
    q := Transvectant(g,h,4);
    // Invariants:
    J2 := K!Transvectant(F,F,8);
    J3 := K!Transvectant(F,g,8);
    J4 := K!Transvectant(k,k,4);
    J5 := K!Transvectant(m,k,4);
    J6 := K!Transvectant(k,h,4);
    J7 := K!Transvectant(m,h,4);
    J8 := K!Transvectant(p,h,4);
    J9 := K!Transvectant(n,h,4);
    JX := K!Transvectant(q,h,4);
    return [J2,J3,J4,J5,J6,J7,J8,J9,JX], [2,3,4,5,6,7,8,9,10];
end intrinsic;
