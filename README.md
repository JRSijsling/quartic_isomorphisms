Description
--

This repository contains Magma code for calculating isomorphisms between plane quartic curves. The code in it is written in terrible style for now, and it only works over the rationals and finite fields. A number field version exists, but does not have acceptable speed. To be improved.

Prerequisites
--

You need to have Magma installed on your machine to use this code.

Installation
--

You can enable the functionality of this package in Magma by attaching the `quartic_isomorphisms/magma/spec` file with `AttachSpec`. To make this independent of the directory in which you find yourself, and to active this on startup by default, you may want to indicate the relative path in your `~/.magmarc` file, by adding the line
```
AttachSpec("~/Programs/quartic_isomorphisms/magma/spec");
```

Usage
--

Examples are given in the directory `examples/`.

Verbose comments are enabled by
```
SetVerbose("QuarticIso", n);
```
where `n` is either `1` or `2`. A higher value gives more comments.

Credits
--

This package uses code from the Magma package [`echidna`](http://iml.univ-mrs.fr/~kohel/alg/index.html) by David Kohel for an implementation of the Dixmier--Ohno invariants.
