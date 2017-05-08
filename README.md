# Sqrt 2 is not rational

**Author:** Ikegami Daisuke <ikegami.da@gmail.com>

**An example:** Translate Agda1/Alfa (written by Thierry Coquand) to Agda2

Works with the Agda standard library.

### Links:

* Agda
> <http://wiki.portal.chalmers.se/agda/pmwiki.php>
* Agda standard library
>  <http://wiki.portal.chalmers.se/agda/agda.php?n=Libraries.StandardLibrary>
* The original proof on Agda1/Alfa
> <http://www.cs.ru.nl/~freek/comparison/files/agda.alfa>
* The paper
> <http://www.cs.ru.nl/~freek/comparison/comparison.pdf>
* Other proofs by another different proof assistants
> <http://www.cs.ru.nl/~freek/comparison/>

### Files:

* `2IsPrime`
> 2 is prime: a short proof by Danielsson.

* `Noether.agda`
> The definitions of Noetherian and Fermat's infinite descent principle.

* `Cancel.agda`
> The definition of cancel.

* `CancellativeAbelianMonoid.agda`
> The definition of cancellative abelian monoid.

* `Property.agda`
> Helper functions of a cancellative abelian monoid.

* `Lemma.agda`
> A lemma for the proof of the main theorem in `Theorem.agda`.

* `Theorem.agda`
> The main theorem which is originally proved by Thierry Coquand:
> any prime cannot be a square of rational in cancellative
> abelian monoid.

* `NatStar.agda`
> A set of natural numbers without zero, and its multiplication.

* `NatStarProperties.agda`
> Properties of NatStar.

* `Corollary.agda`
> The set of the natural numbers without zero and  multiplication
> forms a cancellative abelian modoid.
> Thus, square root of two is irrational.