/***
 *  Final wrapping intrinsic
 *
 *  Written by Jeroen Sijsling (jeroen.sijsling@uni-ulm.de)
 *
 *  See LICENSE.txt for license details.
 */


import "QuarticIsoFF.m": QuarticIsomorphismsFF;
import "QuarticIsoQQ.m": QuarticIsomorphismsQQ;

intrinsic QuarticIsomorphisms(f1::RngMPolElt, f2::RngMPolElt : geometric := false) -> .
{Finds the isomorphisms between the ternary quartic forms f1 and f2. Matrices T returned as a second value satisfy f2 = f1 T up to scalar.}

K := BaseRing(Parent(f1));
if Type(K) eq FldFin then
    return QuarticIsomorphismsFF(f1, f2 : geometric := geometric);
elif Type(K) eq FldRat then
    return QuarticIsomorphismsQQ(f1, f2 : geometric := geometric);
else
    error "Base field currently not handled";
end if;

end intrinsic;


intrinsic QuarticAutomorphisms(f::RngMPolElt : geometric := false) -> .
{Finds the automorphisms of ternary quartic form f. Matrices T returned as a second value satisfy f = f T up to scalar.}

return QuarticIsomorphisms(f, f : geometric := geometric);

end intrinsic;


intrinsic QuarticIsomorphisms(X1::CrvPln, X2::CrvPln : geometric := false) -> .
{Finds the isomorphisms between the plane quartic curves X1 and X2. Matrices T returned as a second value map X1 onto X2.}

f1 := DefiningPolynomial(X1);
f2 := DefiningPolynomial(X2);
assert Degree(f1) eq 4;
assert Degree(f2) eq 4;

test, Ts := QuarticIsomorphisms(f1, f2 : geometric := geometric);
return test, [ T^(-1) : T in Ts ];

end intrinsic;


intrinsic QuarticAutomorphisms(X::CrvPln : geometric := false) -> .
{Finds the automorphisms of plane quartic curve X. Matrices T returned as a second value map X1 onto X.}

return QuarticIsomorphisms(X, X : geometric := geometric);

end intrinsic;
