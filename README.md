polynomial-algebra Haskell library
==================================

This is a Haskell library to compute with multivariate polynomials.

Polynomials are implemented as free modules (with a coefficient ring)
over the monoid of monomials. The free module implementation is basically
a map from monomials to coefficients, with the invariant that zero 
coefficients should be never present. Different implementations of monomials
are available with different speed and usability tradeoffs:

* generic monomial over a variable set given by inhabitants of a type
* monomials over x1, x2 ... xn (two different in-memory representations)
* monomials over an infinite number of variables x1, x2, ...
* univariate monomial (basically, an integer exponent)
* exterior monomial (for exterior algebra)

Type level parameters are used for the variable names (used for pretty-printing)
and number of variables where possible.

A type class interface allows the user to work uniformly over different
implementations.