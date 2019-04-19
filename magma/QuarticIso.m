/***
 *  Final wrapping intrinsic
 *
 *  Written by Jeroen Sijsling (jeroen.sijsling@uni-ulm.de)
 *
 *  See LICENSE.txt for license details.
 */


import "QuarticIsoFF.m": QuarticIsomorphismsFF;
import "QuarticIsoQQ.m": QuarticIsomorphismsQQ;

intrinsic QuarticIsomorphisms(f1::., f2::.) -> .
{Finds the isomorphisms between the quartics f1 and f2.}

K := BaseRing(Parent(f1));
if Type(K) eq FldFin then
    return QuarticIsomorphismsFF(f1, f2);
elif Type(K) eq FldRat then
    return QuarticIsomorphismsQQ(f1, f2);
else
    error "Base field currently not handled";
end if;

end intrinsic;
