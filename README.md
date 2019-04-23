Description
--

This repository contains Magma code for calculating isomorphisms between plane quartic curves. The code in it is written in excruciatingly terrible style for now, and it only works over the rationals and finite fields. To be improved.

Prerequisites
--

An installation of Magma.

Magma installation 
--

The subdirectory `quartic_isomorphisms/magma/` includes code that can be run purely within Magma. You can load all the Magma specific files by attaching the ``quartic_isomorphisms/magma/spec`` file with ``AttachSpec``. For example, if you start your session of Magma inside the git directory, you can do this by typing
```
AttachSpec("magma/spec");
```
To make this independent of the directory in which you find yourself, you may prefer to indicate the relative path, like
```
AttachSpec("~/Programs/quartic_isomorphisms/magma/spec");
```

Usage
--

Examples are given in the directory `examples/`.

Credits
--

The algorithms use functionality for invariant theory as first developed in David Kohel's [`echidna`](https://www.i2m.univ-amu.fr/perso/david.kohel/alg/index.html) package.
