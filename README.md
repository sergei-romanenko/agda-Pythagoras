# Sqrt 2 is not rational

**Written by:** Ikegami Daisuke <ikegami.da@gmail.com>  
**Revised by:** Sergei Romanenko <sergei.romanenko@supercompilers.ru>

**The original proof** (in Agda1/Alfa) is due to Thierry Coquand.

This version tries to exploit the the Agda standard library.

## Links

* Agda  
  <http://wiki.portal.chalmers.se/agda/pmwiki.php>
* Agda standard library  
  <http://wiki.portal.chalmers.se/agda/agda.php?n=Libraries.StandardLibrary>
* The original proof on Agda1/Alfa  
  <http://www.cs.ru.nl/~freek/comparison/files/agda.alfa>
* The paper  
  <http://www.cs.ru.nl/~freek/comparison/comparison.pdf>
* Other proofs by another different proof assistants  
  <http://www.cs.ru.nl/~freek/comparison/>

## Files

* `Cancellative.agda`  
  The definition of cancellative abelian monoid.

* `Theorem.agda`  
  The main theorem which is originally proved by Thierry Coquand:
  any prime cannot be a square of rational in cancellative
  abelian monoid.

---

* `2Divides`  
  Some properties of natural numbers (with zero).

* `NatPlus.agda`  
  A set of natural numbers without zero.

---

* `Corollary.agda`  
  The set of the natural numbers without zero and  multiplication
  forms a cancellative abelian monoid.  
  Thus, the square root of two is irrational.

---

## Miscellanea

* `Corbineau.Sqrt2`

  There is no m and n such that

    > `n ≢ 0` and `m * m ≡ 2 * (n * n)`

  Hence, sqrt 2 is irrational.

  The proof in Coq has been originally written by Pierre Corbineau  
  <http://www-verimag.imag.fr/~corbinea/ftp/programs/sqrt2.v>

---

* `Danielsson.2IsPrime`

  2 is prime.

  Originally written by Nils Anders Danielsson  
  <https://lists.chalmers.se/pipermail/agda/2011/003464.html>

---
