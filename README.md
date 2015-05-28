# haskhol-math
HaskHOL libraries for mathematical and structural reasoning.  See haskhol.org for more details.
As a fair warning, these libraries are currently very unstable and very undocumented.

~~See the readme from the `haskhol-deductive` repo for why this package needs to be built with `cabal build -j1`.~~

The above has been fixed.  The standard process of `cabal build`, `cabal install` should work fine now.

You should also be sure you have something else to do while you wait for it to build, because it takes a decent amount of time.
Depending on if you're doing a full reconstruction of the theory contexts and proof cache, or just a simple rebuild, it takes in the neighborhood of 10-20 minutes to build on an average laptop.

Some of this is due to the large number of Text literals that are packed at compiled time, but mainly it's because of a handful of proofs that rely on parts of HaskHOL that haven't been tuned for performance yet.
Unfortunately, these proofs happen to lie in the critical path of theory construction, so they can't be avoided.

I'll improve things when I have the time, but for now you have my apologies.


