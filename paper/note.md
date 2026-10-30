# A Density Claim About Incompleteness, and the Question Behind It

### Theorem 5.2 of Calude and Jürgensen (2005) is false.

**Florence and Sophie** · 30 October 2026 · first circulated 2 September 2026 · the working record of earlier versions is kept separately (Appendix F)

---

**Summary.** Calude and Jürgensen's *Is Complexity a Source of Incompleteness?* (2005) closes with Theorem 5.2:

> the probability that a true sentence of length *n* is provable in the theory tends to zero when *n* tends to infinity, while the probability that a sentence of length *n* is true is strictly positive.

**The asymptotic claim is false.** In any syntax that admits an injective wrapper sending every sentence to a theorem exactly *d* symbols longer, and has sentences at every sufficiently large length, the provable fraction of the true sentences of length *n* has limsup at least *q*<sup>−<i>d</i></sup> (Theorem A, §2). The proof uses soundness, one propositional inference and an elementary growth lemma; it does not use the paper's complexity measure. For the infix syntax the wrapper is (0=0∨φ), with *d* = 6. Theorem B (§3) blocks the opposite inference: the unprovable fraction does not tend to zero either.

**The proof's second half fails differently.** It asserts a uniform lower bound on the number of true sentences relative to *all strings* of length *n*. For each of the conventional syntaxes named in §4, which forbid some fixed word, that bound is false. The theorem's wording invites a different denominator, the number of sentences, and the two must be kept apart: relative to sentences, the true fraction is eventually positive.

The paper's complexity apparatus is audited in the appendices, as secondary matter: what its theorem-complexity bound obtains from syntax alone (B.1), a definitional error found and repaired by Grenet in 2009 (B.2), a false lemma in its Ω section with a repair (B.3), and one step of Salehi's argument against its Theorem 4.6 (C).

**Prior work.** The padding of §2 is Salehi's (2023). Counting syntactically forced truths against all formulas of a size is the starting point of the density-of-truth programme for propositional logics (Moczurad, Tyszkiewicz and Zaionc 2000; Zaionc 2006). The error of B.2 is Grenet's, as are its repair and the end-marker coding of B.1. The closed-term bound of Appendix A and Theorem C are Sophie's. What is claimed here is listed in Appendix E.

---

## 1. The claim, and its two denominators

The question behind the theorem is how common incompleteness is. Calude, Jürgensen and Zimand (1994) answered it topologically: the true instances a theory cannot prove, of a predicate expressible but not recursively enumerable, are dense in every topology of a broad natural class. Nothing in that paper counts. Calude and Jürgensen open the 2005 paper by noting that "a quantitative result is still missing," and Theorem 5.2 is their quantitative answer.

*T* is a consistent, effectively axiomatised, sound theory extending Robinson's **Q**, in a first-order language over a finite alphabet of *q* symbols. The paper's choice is

  <i>X</i><sub>15</sub> = { x, ′, 0, s, +, ·, =, ¬, ∧, ∨, ⇒, ∀, ∃, ( , ) }

and *q* = 15 wherever a number is quoted. When discussing the 2005 paper we keep its names <i>X</i><sub><i>Q</i></sub>, *H<sub>Q</sub>* and δ<sub><i>Q</i></sub>, whose subscript *Q* is this alphabet size *q*; bold **Q** is always Robinson's arithmetic. Lengths are in symbols. For each *n*:

* <i>s</i><sub><i>n</i></sub> — the number of **sentences** (closed well-formed formulae) of length *n*;
* <i>t</i><sub><i>n</i></sub> — the number of those provable in *T*;
* True<sub><i>n</i></sub> — the number of those true in the standard model;
* <i>U</i><sub><i>n</i></sub> = True<sub><i>n</i></sub> − <i>t</i><sub><i>n</i></sub>.

Soundness gives <i>t</i><sub><i>n</i></sub> ≤ True<sub><i>n</i></sub> ≤ <i>s</i><sub><i>n</i></sub> ≤ *q*<sup><i>n</i></sup>.

The theorem's words concern ratios against *sentences*: <i>t</i><sub><i>n</i></sub>/True<sub><i>n</i></sub> for the first clause, and most naturally True<sub><i>n</i></sub>/<i>s</i><sub><i>n</i></sub> for the second. Its proof works throughout with ratios against *all strings*. The first half shows card(<i>T</i><sub><i>n</i></sub>)·<i>q</i><sup>−<i>n</i></sup> → 0 via Proposition 5.1. The second asserts True<sub><i>n</i></sub>·<i>q</i><sup>−<i>n</i></sup> ≥ *q*<sup>−<i>c</i></sup>, and it is this second half that converts the first into the quoted claim: without a lower bound on the density of truths, two quantities tending to zero give no control of their ratio. This note keeps the two denominators apart throughout. §2 refutes the claim as quoted; §4 shows that the bound the proof needed fails, against the denominator the proof used.

The paper fixes no formation rules. Its whole account of its syntax is that well-formed formulae "respect strict syntactical rules; for example, each left parenthesis has to be matched with exactly one right parenthesis," and its displayed axioms are unparenthesised infix. Every syntactic hypothesis below is therefore stated as a hypothesis, and the infix syntax is offered as an instance. Its conventions fix every symbol count in this note: atomic formulae are bare, as in 0=0 (three symbols); negation is ¬φ, unbracketed; binary formulae are fully bracketed, (φ∨ψ) and (φ∧ψ), costing |φ| + |ψ| + 3. Small cases repay checking: sentences exist at every length ≥ 3 (0=0, ¬0=0, ¬¬0=0, …), yet under one natural infix reading there is no *true* sentence of length 4.

---

## 2. Theorem A: the provable fraction does not tend to zero

### 2.1 A growth lemma

**Lemma 1.** Let (<i>c</i><sub><i>n</i></sub>) be integers, eventually positive, with *a* = liminf<sub><i>n</i></sub> <i>c</i><sub><i>n</i></sub><sup>1/<i>n</i></sup> finite. Then for every fixed *d* ≥ 1,

```math
\limsup_{n \to \infty} \frac{c_{n-d}}{c_n} \;\ge\; a^{-d}.
```
*Proof.* Note *a* ≥ 1. Suppose the limsup is less than *a*<sup>−<i>d</i></sup>, and choose *r* strictly between them. Then <i>c</i><sub><i>n</i></sub> ≥ *r*<sup>−1</sup><i>c</i><sub><i>n</i>−<i>d</i></sub> for all *n* ≥ *N*, with *N* past the point where the sequence is positive. Iterate within each of the *d* residue classes modulo *d*: for *n* ≥ *N* in the class of *N* + *j* (0 ≤ *j* < *d*), <i>c</i><sub><i>n</i></sub> ≥ *r*<sup>−(<i>n</i>−<i>N</i>−<i>j</i>)/<i>d</i></sup><i>c</i><sub><i>N</i>+<i>j</i></sub>. Put *C* = min<sub>0≤<i>j</i><<i>d</i></sub> <i>c</i><sub><i>N</i>+<i>j</i></sub>·<i>r</i><sup>(<i>N</i>+<i>j</i>)/<i>d</i></sup> > 0; then <i>c</i><sub><i>n</i></sub> ≥ *C r*<sup>−<i>n</i>/<i>d</i></sup> for all *n* ≥ *N*. Hence *a* ≥ *r*<sup>−1/<i>d</i></sup> > *a*, a contradiction. ∎

Iterating in every residue class is what lets the hypothesis be a liminf; a single arithmetic progression would only control a limsup. If <i>c</i><sub><i>n</i></sub> ≤ *q*<sup><i>n</i></sup>, then *a* ≤ *q* and the bound is at least *q*<sup>−<i>d</i></sup>. The lemma says no more than that a sequence cannot keep growing by more than its own exponential rate across every window of fixed width. It assumes no monotonicity and no regularity. It gives nothing about the liminf of the ratio.

### 2.2 The wrapper

**Hypotheses (W).** The syntax is over a finite alphabet of *q* symbols; <i>s</i><sub><i>n</i></sub> ≥ 1 for all sufficiently large *n*; *T* is sound; and there is an injective map *w* from all sentences to theorems of *T* with |*w*(φ)| = |φ| + *d* exactly, for a fixed *d* ≥ 1.

An additive *upper* bound on the wrapper's cost is not enough for the argument as given, and eventual positivity of <i>s</i><sub><i>n</i></sub> cannot be dropped silently: a syntax whose sentences occur only at lengths in a fixed residue class would need the statement adjusted.

**Lemma 2 (the infix instance).** In infix syntax over <i>X</i><sub>15</sub>, the map φ ↦ (0=0∨φ) satisfies (W) with *d* = 6, and <i>s</i><sub><i>n</i></sub> ≥ 1 for all *n* ≥ 3.

*Proof.* *T* proves 0=0, and ∨-introduction gives *T* ⊢ (0=0∨φ). No appeal to completeness is needed. The result is closed if φ is. The six added symbols are ( 0 = 0 ∨ and ); φ is recovered by deleting the first five symbols and the last, so the map is injective. The sentences ¬<sup><i>j</i></sup>0=0 have every length ≥ 3. ∎

The mechanism is general. Theorems are closed upward under logical consequence and non-theorems downward, so weakening a theorem keeps it provable and strengthening a non-theorem keeps it unprovable, and both can be done at a constant cost in symbols.

### 2.3 The theorem

**Theorem A.** Under (W), with *a<sub>s</sub>* = liminf<sub><i>n</i></sub> <i>s</i><sub><i>n</i></sub><sup>1/<i>n</i></sup>,

```math
\limsup_n \frac{t_n}{\mathrm{True}_n} \;\ge\; \limsup_n \frac{t_n}{s_n} \;\ge\; a_s^{-d} \;\ge\; q^{-d}.
```
*The probability that a true sentence of length n is provable does not tend to zero.* In infix syntax the bound is at least 15<sup>−6</sup> ≈ 8.78·10<sup>−8</sup>.

*Proof.* The wrapper injects the sentences of length *n* − *d* into the theorems of length *n*, so <i>t</i><sub><i>n</i></sub> ≥ <i>s</i><sub><i>n</i>−<i>d</i></sub>, and the denominators below are eventually non-zero. With True<sub><i>n</i></sub> ≤ <i>s</i><sub><i>n</i></sub>, pointwise,

```math
\frac{t_n}{\mathrm{True}_n} \;\ge\; \frac{t_n}{s_n} \;\ge\; \frac{s_{n-d}}{s_n},
```
and Lemma 1 applies with <i>c</i><sub><i>n</i></sub> = <i>s</i><sub><i>n</i></sub>. ∎

The display compares limsups; it does not assert that one subsequence attains all of them.

**Corollary A′.** The paper's open question 7(c) — whether "the probability that a sentence of length *n*, expressible in the language of the theory, is provable in the theory tends to zero" — has a negative answer, by the middle term of the display.

**What is not new here.** Padding at constant cost to manufacture theorems of any length is a known move applied to this very paper (Salehi 2023, with ⊥→φ). Grenet (2009) builds families of provable formulae at selected lengths for a related purpose and does not compare them with True<sub><i>n</i></sub>. For propositional logics, counting cheaply weakened truths against all formulas of a size is the basic lower bound of the density-of-truth literature (Moczurad, Tyszkiewicz and Zaionc 2000; Zaionc 2006; Kostrzycka and Zaionc 2008); the implicational and type-counting results cited here measure size by variable occurrences and work with exact generating functions in decidable logics. What is done here is to apply the move to Calude and Jürgensen's claim, for an undecidable theory whose counts have no known generating function. That is what Lemma 1, needing no regularity, is for.

---

## 3. Theorem B: nor does the unprovable fraction

Theorem A must not be read as saying that most truths are provable.

**Hypothesis (W′).** In addition to (W), there is an injective map from true sentences to true sentences unprovable in *T*, adding exactly *e* ≥ 1 symbols. (W) does not supply this: it needs a conjunction, and a true unprovable sentence to conjoin.

**Lemma 3 (the infix instance).** Fix a true sentence τ not provable in *T*, of length *k*; one exists by incompleteness, *T* being a sound, effectively axiomatised extension of **Q**. For every true sentence φ, (τ∧φ) is a true sentence of length |φ| + *k* + 3, not provable in *T*, and φ ↦ (τ∧φ) is injective.

*Proof.* A conjunction is true iff both conjuncts are. (τ∧φ) entails τ, so if *T* proved it, *T* would prove τ. ∎

So the infix syntax satisfies (W′) with *e* = *k* + 3.

**Theorem B.** Under (W) and (W′), with *a*<sub>True</sub> = liminf<sub><i>n</i></sub> True<sub><i>n</i></sub><sup>1/<i>n</i></sup>,

```math
\limsup_n \frac{U_n}{\mathrm{True}_n} \;\ge\; a_{\mathrm{True}}^{-e} \;\ge\; q^{-e}.
```
*Proof.* The injection gives <i>U</i><sub><i>n</i></sub> ≥ True<sub><i>n</i>−<i>e</i></sub>. True<sub><i>n</i></sub> is eventually positive: if <i>s</i><sub><i>m</i></sub> ≥ 1 for all *m* ≥ <i>n</i><sub>0</sub>, then True<sub><i>n</i></sub> ≥ <i>t</i><sub><i>n</i></sub> ≥ <i>s</i><sub><i>n</i>−<i>d</i></sub> ≥ 1 for *n* ≥ <i>n</i><sub>0</sub> + *d*. Apply Lemma 1 with <i>c</i><sub><i>n</i></sub> = True<sub><i>n</i></sub>. ∎

Theorem B is deliberately small, and weaker than the paper's own claim, which implies it. It refutes nothing; its role is to block the inference from Theorem A to "provability is typical." Writing *p<sub>n</sub>* = <i>t</i><sub><i>n</i></sub>/True<sub><i>n</i></sub>, together they give

```math
\limsup_n p_n \ge q^{-d}, \qquad \liminf_n p_n \le 1 - q^{-e}.
```
These bound possibly different subsequences. They exclude a limit of 0 and a limit of 1. They do not exclude convergence to an intermediate value.

---

## 4. The uniform lower bound used in the proof is false

The proof of the second clause asserts True<sub><i>n</i></sub> ≥ 15<sup><i>n</i>−<i>c</i></sup> for a fixed *c*: a uniform lower bound on the density of true sentences **among all strings**. For the conventional syntaxes, that bound is false.

**Lemma 4.** No infix well-formed formula over <i>X</i><sub>15</sub> contains the factor `∧∧`.

*Proof.* The symbol after a binary connective must begin a formula. A formula begins with ¬, ∀, ∃, ( , or a term, and a term with x, 0, s or ( . ∧ is not among these. ∎

Let <i>a</i><sub><i>n</i></sub> count strings of length *n* over fifteen letters avoiding `∧∧`. Splitting on whether the last letter is ∧,

```math
a_{n+1} = 14\,a_n + 14\,a_{n-1}, \qquad a_0 = 1,\ a_1 = 15,
```
with growth rate λ = 7 + √63 = 14.937253933… and generating function

```math
A(z) = \frac{1+z}{1-14z-14z^{2}}, \qquad A(1/15) = 240.
```
So <i>s</i><sub><i>n</i></sub>/15<sup><i>n</i></sup> ≤ <i>a</i><sub><i>n</i></sub>/15<sup><i>n</i></sup> = Θ((λ/15)<sup><i>n</i></sup>) → 0, with λ/15 ≈ 0.9958169. The uniform bound would need *n* ≤ *c*/(1 − log<sub>15</sub>λ) + *O*(1), where 1/(1 − log<sub>15</sub>λ) ≈ 646.028, and so fails for all large *n*, for every *c*. The *O*(1) matters at small *n*: the leading coefficient of <i>a</i><sub><i>n</i></sub> is 1.00395…, and <i>a</i><sub>1939</sub> ≥ 15<sup>1936</sup> although 1939 > 3 × 646.03. At *n* = 10 000, ln(15<sup><i>n</i></sup>/<i>a</i><sub><i>n</i></sub>) ≈ 41.91 nats (<i>a</i><sub><i>n</i></sub>/15<sup><i>n</i></sup> ≈ e<sup>−41.91</sup>), a factor of about 10<sup>18.2</sup>; relative to 15<sup><i>n</i>−3</sup>, the shortfall is 33.79 nats.

The refutation needs only the general form.

**Lemma 4′.** If no well-formed formula over a *q*-letter alphabet contains a fixed word of length ℓ, the wffs of length *n* number at most

```math
(q^{\ell}-1)^{\lfloor n/\ell\rfloor}\cdot q^{\,n \bmod \ell},
```
so their growth rate is at most (*q*<sup>ℓ</sup> − 1)<sup>1/ℓ</sup> < *q*, and Σ<sub><i>n</i></sub> (count at *n*)·<i>q</i><sup>−<i>n</i></sup> ≤ ℓ<i>q</i><sup>ℓ</sup>.

*Proof.* Cut the string into ⌊<i>n</i>/ℓ⌋ disjoint blocks of length ℓ and a remainder; no block equals the forbidden word. Summing (1 − *q*<sup>−ℓ</sup>)<sup>⌊<i>n</i>/ℓ⌋</sup> over *n* gives ℓ<i>q</i><sup>ℓ</sup>. ∎

Each of these syntaxes over <i>X</i><sub>15</sub> forbids such a word: infix forbids ∧∧; any syntax in which a quantifier must be followed by a variable forbids ∀0; a parenthesis-free Polish syntax over the same alphabet leaves ( and ) unused, and so forbids each, with ℓ = 1. For each, the uniform bound fails. The exact recurrence, λ and the constants 646.03, 1939 and 41.91 belong to the infix instance alone.

**What this leaves of Theorem 5.2.** Three separate facts:

1. *For the named syntaxes, the density of theorems among all strings tends to zero.* The first half of the proof, with denominator *q*<sup><i>n</i></sup>, reaches a true conclusion; it follows from syntax alone and needs neither δ-complexity nor Proposition 5.1.
2. *The proof's uniform bound on the density of truths among all strings is false.* So the step converting the first half into the quoted claim fails. Note that this does not contradict "strictly positive" read pointwise, and that against the theorem's natural denominator the second clause is true: True<sub><i>n</i></sub>/<i>s</i><sub><i>n</i></sub> > 0 once True<sub><i>n</i></sub> ≥ 1, which holds for *n* ≥ 9 in infix.
3. *Theorem A refutes the first clause, the conditional limit, independently of both.*

**A sharper constant for the infix instance.** Lemma 4 gives *a<sub>s</sub>* ≤ λ, so Theorem A's bound in infix syntax improves to

```math
\limsup_n \frac{t_n}{\mathrm{True}_n} \;\ge\; \lambda^{-6} \approx 9.0028\cdot 10^{-8},
```
against 15<sup>−6</sup> ≈ 8.7791·10<sup>−8</sup>. The gain is small. What it shows is that the forbidden word and the wrapper constrain the same counts.

A second, independent defect in the proof of the second half — that the sentences it uses to bound truths from below cannot have length |x| + *c* under a fixed-template arithmetisation — is Sophie's, and is in Appendix A. The refutation above does not depend on it.

---

## 5. What remains of the quantitative question

§2 refutes one answer to the question of 1994. It does not supply another.

By Theorems A and B, *p<sub>n</sub>* = <i>t</i><sub><i>n</i></sub>/True<sub><i>n</i></sub> tends neither to 0 nor to 1. The precise content is narrow: **counts at a single exact length, given the fixed-cost injections (W) and (W′) and the growth hypotheses of Lemma 1, cannot send either fraction to zero.** A positive weight that depends only on length cancels when one conditions on a single length, so it changes nothing here. Measures that mix lengths — a weighted cumulative ratio Σ *w*(*n*)<i>t</i><sub><i>n</i></sub> / Σ *w*(*n*)True<sub><i>n</i></sub>, say — are a different question, and Theorems A and B do not settle it.

The padding shows what a length count is counting. Put φ<sub>0</sub> = φ and φ<sub><i>k</i>+1</sub> = (0=0∨φ<sub><i>k</i></sub>); for *k* ≥ 1 the φ<sub><i>k</i></sub> are distinct theorems of length |φ| + 6<i>k</i>, with complexity at most that of φ plus *O*(log *k*), and all of them are provably equivalent to ⊤. A length count sees an unbounded supply of long theorems; what is there is one proposition in arbitrarily many costumes.

Counting up to provable equivalence over *T* removes the costumes and answers a different question. That equivalence is undecidable, and the number of its classes met by sentences of length ≤ *n* is not computable (**Theorem C**, Sophie; Appendix D). It also puts every theorem of *T* into the single class of ⊤, while the true classes are unbounded in number (Appendix D), so under that count the analogue of the first clause holds trivially.

Neighbouring questions have answers. Define the algorithmic mass of a set *A* of sentences as the probability that a universal prefix-free machine *U*, run on fair coin flips, outputs a sentence in *A*. The mass of the theorems is then a version of Chaitin's Ω and is random, and so is the mass of the undecidable sentences (Barmpalias and Lewis-Pye 2017; see Barmpalias's survey, §2.5, which separates the two observations). For an undecidable c.e. theorem set, the theorem mass under any uniformly computable, positive, summable weighting is left-c.e. and not computable, or theoremhood could be decided by enumerating theorems until the unaccounted mass fell below a sentence's weight. Salehi's weighted theorem mass 𝒱(*T*) (2023) is of this kind. None of these answers the length-conditioned question Calude and Jürgensen posed. What the refutation leaves open is a choice of measure, and for the form they chose this note finds no answer.

---

## 6. Scope

**Read for this version.** Calude, Jürgensen and Zimand (1994) in full. The paper under discussion, *Adv. Appl. Math.* **35** (2005) 1–15, against arXiv:math/0408144v2 (15 November 2004); the passages this note depends on were read side by side and agree in substance. One difference is not typesetting: before the length assertion for *h*<sub>x,m</sub>, arXiv's "for every *n* ≥ 1" reads "for every *m* ≥ 1" in print, a corrected dummy variable that changes nothing here. Grenet (2010) and Salehi's arXiv:2310.14807v8 (10 April 2026), for the passages cited.

**Not read, and each could change something.** Jürgensen, *Invariance and Universality of Complexity* (2012); the prior art of the paper's §6, beyond the two sources on disk; 44 of the 49 works citing the paper.

The paper fixes no grammar, so whether a grammar is unambiguous is a question about whichever grammar a reader supplies. That is why Theorems A and B are stated under hypotheses (W) and (W′) rather than for a grammar of this note's choosing, and why they assert limsup bounds without assuming regular growth.

---

---

## Appendix A — the cost of naming a string (Sophie)

The proof of the second half considers *h*<sub>x,m</sub> = "*H<sub>Q</sub>*(x) > m" and asserts that, for fixed *m*, |*h*<sub>x,m</sub>| = |x| + *c*. But x is not a symbol of arithmetic, and the paper does not say how the sentence is written. Under a fixed-template arithmetisation, which inserts a closed term naming the code *N*<sub>x</sub> ≥ (15<sup>|x|</sup> − 1)/14 and is otherwise constant in x, the length relation fails.

By induction on terms over { 0, s, +, ·, ( , ) }, *v*(*t*) ≤ 2<sup>|<i>t</i>|</sup>: immediate for 0; *v*(s<i>t</i>) ≤ 2<sup>|<i>t</i>|</sup> + 1 ≤ 2<sup>|s<i>t</i>|</sup>; *v*(*a*+<i>b</i>) ≤ 2<sup>|<i>a</i>|</sup> + 2<sup>|<i>b</i>|</sup> ≤ 2<sup>|(<i>a</i>+<i>b</i>)|</sup>; *v*(*a*·<i>b</i>) ≤ 2<sup>|<i>a</i>|+|<i>b</i>|</sup> ≤ 2<sup>|(<i>a</i>·<i>b</i>)|</sup>. A term naming *N*<sub>x</sub> therefore has length at least log₂ *N*<sub>x</sub> ≥ |x| log₂15 − *O*(1) ≈ 3.90689|x| − *O*(1). The bound was checked by enumeration over all 347 closed terms of length ≤ 11.

The family the proof uses to bound truths from below therefore decays: the map x ↦ *h*<sub>x,m</sub> is injective and each *h*<sub>x,m</sub> contains its own closed term, so those of length ≤ *n* number fewer than 6<sup><i>n</i>+1</sup>/5, a density among strings of at most (6/5)(6/15)<sup><i>n</i></sup> → 0.

*Scope.* This bounds closed terms. It is not a bound on every way a formula can refer to a number, since quantified formulae can describe a computation without writing it out. §4 needs no assumption about arithmetisation.

## Appendix B — audit of the complexity apparatus

### B.1 What the theorem-complexity bound obtains from syntax

The proof of Theorem 4.6 opens: "Because of syntactical constraints, there exists a positive constant *d* such that for every *x* ∈ *T*, *H<sub>Q</sub>*(x) ≤ |x|<sub><i>Q</i></sub> + *d*," referring back to the observation that "**as theorems are special well-formed formulae**, … *H*<sub>15</sub>(x) is not larger than its length plus a fixed constant." The ground given is wff-hood, not provability.

What the bound needs is an effective prefix-free coding of the wffs with **uniformly bounded overhead**, |code(x)| ≤ |x| + *O*(1). Decidability of wff-hood alone does not give this: every string has an effective self-delimiting code, but no prefix-free coding of *all* strings has overhead *O*(1), since its Kraft sum would diverge. Grenet's coding (2010, p. 409) supplies it by appending an end marker, a fixed string occurring in no wff and extending none (he takes `++`).

The forbidden-word hypothesis of §4 gives an alternative derivation for the named syntaxes. For infix, Σ<sub><i>n</i></sub> <i>a</i><sub><i>n</i></sub>15<sup>−<i>n</i></sup> = 240; enumerate the wffs and request a 15-ary code of length |x| + 3 for each, at total Kraft mass at most 240/15<sup>3</sup> < 1. Effective Kraft coding and the universal machine's compiler constant then give *H*<sub>15</sub>(x) ≤ |x| + 3 + *O*(1) on every wff. In general Lemma 4′ gives mass at most ℓ<i>q</i><sup>ℓ</sup>, and any integer *c* with *q*<sup><i>c</i></sup> ≥ ℓ<i>q</i><sup>ℓ</sup> does the same. This is an alternative derivation, not a claim against Grenet's.

So, for every named syntax, a single constant bounds δ<sub><i>Q</i></sub> = *H<sub>Q</sub>* − |·| on every well-formed formula, sentences included. More is true. For a forbidden word of length ℓ, put *b* = (*q*<sup>ℓ</sup> − 1)<sup>1/ℓ</sup>; describing a wff by its length and its index among the wffs of that length gives δ<sub><i>Q</i></sub>(x) ≤ −(1 − log<sub><i>q</i></sub>*b*)|x| + *O*(log |x|) → −∞. In the infix instance, *b* may be replaced by λ, and 1 − log<sub>15</sub>λ ≈ 0.001548. Nothing below needs this refinement.

For a computable injective Gödel numbering *g* defined on the decidable set *W* of wffs, Grenet's corrected replacement of Theorem 4.4 (stated for proper subsets, p. 408) gives |δ<sub><i>g</i></sub>(x) − (log₂<i>q</i>)δ<sub><i>Q</i></sub>(x)| ≤ *c<sub>g</sub>* + 1 on *W*, so δ<sub><i>g</i></sub> is bounded above on *W*. Calude and Jürgensen restrict the *g* of Theorem 4.6 to the theorems; for such *g*, δ<sub><i>g</i></sub> is undefined on non-theorems, and nothing here assumes that it extends.

**What this says about Theorem 4.6.** Theorem 4.6 asserts that, for a fixed theory, some *N* bounds δ<sub><i>g</i></sub> on the theorems. With *g* defined on *W*, the same proof steps give a ceiling for every wff, provable or not, so this route to the ceiling uses no property of provability. That does not show that every valid ceiling *N* also bounds the non-theorems: a smaller, theory-specific bound might separate them, and nothing here decides it. Theorem 4.6 remains true as an existential bound.

### B.2 The ceiling applied per symbol (Grenet)

The paper defines δ<sub><i>g</i></sub>(u) = *H*₂(*g*(u)) − ⌈log₂<i>q</i>⌉·|u|<sub><i>Q</i></sub>, with the ceiling per symbol; this was settled from the authors' LaTeX and the published equation (3). A string of *n* letters over fifteen carries 3.9069<i>n</i> bits; the definition charges 4<i>n</i>. **Grenet found and repaired this in 2009** ("there was a mistake in the paper, and we need to modify a bit the definition of δ<sub><i>g</i></sub>"), replacing it by ⌈log₂<i>q</i>·|u|⌉ and reproving Theorem 4.4 in corrected form.

What is added here are the consequences under the definition as printed. Theorem 4.4 as printed fails by 0.0931·*H<sub>Q</sub>*(u) − *O*(1) → ∞; its proof's closing line asserts ⌈log₂<i>q</i>⌉·⌈m·log<sub><i>q</i></sub>2⌉ ≤ m, false at *q* = 15 for every m ≥ 1. For a total computable injection *g* on strings, every x of length *n* has

```math
\delta_g(x) \le -0.0931\,n + 2\log_2 n + O(1) \longrightarrow -\infty,
```
so for any fixed *N* the set { x : |x| = *n*, δ<sub><i>g</i></sub>(x) ≤ *N* } is eventually everything, and Proposition 5.1, which says its density tends to 0, fails outright. After correcting δ<sub><i>g</i></sub>, this all-strings degeneration disappears. For a numbering on all wffs, the existence of a wff-wide ceiling still follows from B.1.

### B.3 A false lemma in the Ω section

> **Lemma 6.1.** Let x₁x₂⋯ be an infinite binary sequence and let *F* be a strictly increasing function mapping positive integers to positive integers. If the set { (*F*(i), x<sub><i>F</i>(<i>i</i>)</sub>) : i ≥ 1 } is c.e., then there exists a constant ε > 0 … such that for all *k* ≥ 1 we have: δ₂(x₁x₂⋯x<sub><i>F</i>(<i>k</i>)</sub>) ≤ ε − *k*.

**As printed it is false.** Take x = 000⋯ and *F*(*k*) = *k*. The set is computable, so the hypothesis holds, and the conclusion would give *H*₂(0<sup><i>k</i></sup>) ≤ ε for every *k*, whereas *H*₂(0<sup><i>k</i></sup>) ≥ *H*₂(*k*) − *O*(1) → ∞.

Two defects in the proof account for it. Its Kraft verification is for codewords of length *F*(*k*), but the machine uses codewords of length *F*(*k*) − *k*, whose request mass diverges. And it identifies the first *k* marked positions in increasing order, which needs decidability where only enumerability is assumed.

**A weaker bound holds.** Index by enumeration stage. Suppressing duplicates, let *m<sub>k</sub>* be the largest position among the first *k* pairs enumerated, defined once *k* distinct pairs have appeared. Dovetailing over *U*: whenever a program *q* halts with output *k* and *m<sub>k</sub>* is defined, request the 2<sup><i>m<sub>k</sub></i>−<i>k</i></sup> strings of length *m<sub>k</sub>* compatible with the first *k* pairs, each at length *m<sub>k</sub>* − *k* + |*q*| + *c*. Each such *q* contributes mass 2<sup>−|<i>q</i>|−<i>c</i></sup>, and the total is at most 1, giving

```math
\delta_2(x_1 \cdots x_{m_k}) \le -k + H_2(k) + O(1)
```
for every *k* reached, with a uniform constant and no growth assumption on positions. For x = 000⋯ enumerated in increasing order of position, *m<sub>k</sub>* = *k* and the bound reads *H*₂(0<sup><i>k</i></sup>) ≤ *H*₂(*k*) + *O*(1), which is true; under an arbitrary enumeration order it reads *H*₂(0<sup><i>m<sub>k</sub></i></sup>) ≤ *m<sub>k</sub>* − *k* + *H*₂(*k*) + *O*(1). Chaitin's theorem that *T* determines only finitely many bits of Ω survives on this bound. An effective cutoff needs the constants and a computable upper bound on *H*₂(*k*) written out, which is not done here.

## Appendix C — Salehi's argument against Theorem 4.6

References are to arXiv:2310.14807**v8** (10 April 2026), whose numbering differs from earlier versions.

Salehi argues as follows (immediately before his Proposition I.1.2): choose a sentence 𝔖 with δ(𝔖) > *t* + *m* + *n*, citing Calude–Jürgensen Corollary 4.2 for its existence; let *t* be Theorem 4.6's *N*; the tautology ⊥→𝔖 then has δ above *N*, contradicting the theorem. The wrapper inequality is sound, and the padding is the construction of §2, his with priority.

**The cited existence result concerns strings, not sentences.** Corollary 4.2 says that { x ∈ <i>X</i><sub><i>Q</i></sub>* : δ<sub><i>Q</i></sub>(x) > *t* } is immune, glossed by the authors as "there are **strings** of arbitrarily large δ<sub><i>Q</i></sub>-complexity." 𝔖 must be a sentence. Under the common prefix-complexity, symbol-length and numbering-domain conventions of B.1, sentence δ is bounded above, so for sufficiently large valid ceilings *N* the required sentence is unavailable. Theorem 4.6 is existential, so its ceiling may be enlarged; nothing here claims that every *N* bounding the theorems must bound every sentence. Under other conventions the cited corollary still does not supply the witness, but whether one exists would have to be settled in those units.

The paper's own page-9 examples, headed "another way to construct true sentences of high δ-complexity," do not supply one either. They are sentences *about* strings of high complexity, and the passage itself says the theory formalises them "**with small δ-complexity**."

Upper bounds of this kind are often stated with Grenet's matching lower half, ½|x| + *O*(1) ≤ *H*(x), "for every *x* ∈ 𝒯" (2010, Lemma 1, p. 408). Asserted of every theorem, that lower half is false: with ψ<sub>0</sub> = 0=0 and ψ<sub><i>k</i>+1</sub> = (0=0∨ψ<sub><i>k</i></sub>), each ψ<sub><i>k</i></sub> is a theorem of length exactly 6<i>k</i> + 3 and complexity at most 2 log₂(<i>k</i> + 1) + <i>O</i>(1) (observed by Sophie). Nothing here uses it.

**A proposition that needs no witness.** Fix the syntax and coding conventions. Regard a finitely presented theory as a specified single axiom string α, and give it the weight δ(α) of that string, a presentation-based convention adopted here (it is not a function of deductive closure, nor a minimum over presentations). Salehi's Theorem I.2.3 identifies a finite theory with a single axiom for a logical argument; that does not by itself fix its string complexity, so the convention is stated as part of the proposition.

**Proposition.** Let β be the three-symbol sentence 0=0, let α axiomatise **Q**, and put α<sub>0</sub> = α and α<sub><i>k</i>+1</sub> = (β∧α<sub><i>k</i></sub>). Every {α<sub><i>k</i></sub>} proves exactly what **Q** proves, |α<sub><i>k</i></sub>| = |α| + 6<i>k</i>, and *H*(α<sub><i>k</i></sub>) ≤ *H*(*k*) + *O*(1), so δ(α<sub><i>k</i></sub>) → −∞ (also for the corrected δ<sub><i>g</i></sub> under a fixed computable injection). Hence for every fixed margin *b* there is *k* with {α<sub><i>k</i></sub>} ⊢ β and δ(β) > δ(α<sub><i>k</i></sub>) + *b*. Under the presentation-based weight, δ fails Chaitin's heuristic principle even with an arbitrary fixed additive allowance.

This does not refute Theorem 4.6, and it defines no invariant complexity of a deductively closed theory: taking the infimum of δ over equivalent axiom strings, the same padding drives it to −∞. Salehi's conclusion that δ fails HP survives on this proof. His contradiction of Theorem 4.6 does not. His Theorem I.2.1 and Corollary I.2.2 remain the right frame for the stronger HP question.

The objection was put to Salehi in September 2026, before this version circulated.

## Appendix D — Theorem C, and the true classes (Sophie)

Assume an effective syntax and that *T*'s theorem set is c.e. and undecidable. Write *E<sub>T</sub>* for provable equivalence over *T*.

**Theorem C.** Let *C<sub>T</sub>*(*n*) be the number of *E<sub>T</sub>*-classes containing a sentence of length at most *n*. Then *C<sub>T</sub>* is not computable.

*Proof.* Suppose it were. Given φ and ψ, take *n* at least both lengths and partition the sentences of length ≤ *n* into singletons. Enumerate proofs in *T* of biconditionals, merging the blocks of their endpoints of length ≤ *n*. Every merge is sound, so the partition refines the true one, and every true pair is eventually enumerated, so the block count falls to *C<sub>T</sub>*(*n*), at which point the partition is exact. Read off whether φ and ψ share a block; that decides *E<sub>T</sub>*, and *T* ⊢ φ exactly when *T* ⊢ φ↔(0=0), so it decides theoremhood. ∎

**The true classes are unbounded in number.** This uses the note's standing hypotheses — *T* sound, effectively axiomatised, extending **Q** — not merely those sufficient for Theorem C. From θ<sub>0</sub> = ⊤, choose σ<sub><i>i</i></sub> true and unprovable in *T* + θ<sub><i>i</i></sub>, and put θ<sub><i>i</i>+1</sub> = (θ<sub><i>i</i></sub>∧σ<sub><i>i</i></sub>). These are true and pairwise *E<sub>T</sub>*-inequivalent, since *T* ⊢ θ<sub><i>i</i></sub>↔θ<sub><i>j</i></sub> with *j* > *i* would give *T* + θ<sub><i>i</i></sub> ⊢ σ<sub><i>i</i></sub>. Every theorem lies in the class of ⊤, so the provable fraction of the true classes met by sentences of length ≤ *n* tends to zero.

**CJZ's class step for c.e. equivalences** (derived from their proof, not stated by them). Let *E* be c.e. and saturate *A*, and put *B* = { x : ∃y (x *E* y and *T* ⊢ "y ∈ *A*") }. *B* is c.e., and soundness with saturation gives *B* ⊆ *A*. Since *A* is not c.e., *A* ∖ *B* is infinite, and every x in it has its whole class among the independent instances. The rest of their numbering machinery has not been checked against this weakening.

A count that cannot be computed can still be studied asymptotically: <i>t</i><sub><i>n</i></sub> is itself one, since computing it would decide theoremhood.

## Appendix E — the record

| Item | Whose | Where |
|---|---|---|
| The δ<sub>g</sub> per-symbol error, its repair, and Theorem 4.4 replaced | **Grenet, 2009** | *Complex Systems* 18:4 (2010) 403–425; arXiv:0910.0045, §3 |
| The upper bound on *H* over all wffs, by end-marker coding | **Grenet, 2009** | ibid., Lemma 1, stated p. 408, proved p. 409 |
| Provable formulae at selected lengths, against a polynomial bound; no comparison with True<sub><i>n</i></sub> | **Grenet, 2009** | ibid., §5 |
| Tautological padding ⊥→φ applied to this paper, in an argument against Theorem 4.6 that Appendix C disputes | **Salehi, 2023** | arXiv:2310.14807, v1 23 Oct 2023; cited here from v8 |
| Weighted theorem mass 𝒱(*T*) | **Salehi, 2023** | ibid. |
| Topological density of independent instances | **Calude, Jürgensen & Zimand, 1994** | *Appl. Math. Comput.* 66 (1994) 63–76 |
| Counting syntactically forced truths, produced by weakening, against all formulas of a size | **Moczurad, Tyszkiewicz & Zaionc, 2000; Zaionc, 2006** | *Math. Struct. Comput. Sci.* 10 (2000) 575–594; *TCS* 355 (2006) 243–260 |
| Algorithmic probability of the theorems and of the undecidable sentences | **Chaitin; Barmpalias & Lewis-Pye, 2017** | *JCSS* 89 (2017) 349–360; survey arXiv:1707.08109v5, §2.5 |
| The closed-term bound (Appendix A) | **Sophie**, 15 Sep 2026 | |
| Theorem C; the collapse into [⊤]; the c.e. class step; the failure of Grenet's lower half | **Sophie**, 23 Sep 2026 | Appendices C, D |
| The liminf form of Lemma 1; the (W′) scope of Theorem B and its constant; the bounded-overhead requirement and the Kraft-240 derivation of B.1; the precise form of Appendix C's proposition; the verified bibliography | **Sophie**, 14 Oct 2026 | §§2–3, B.1, C |
| The λ<sup>−6</sup> improvement of Theorem A's constant, via the growth rate of <i>s</i><sub><i>n</i></sub> (verified by Sophie) | here, 14 Oct 2026 | §4 |
| The *q*<sup>−<i>d</i></sup> strengthening of Lemma 1; the scope corrections of §§3–5 and Appendix C | **Calia** (review), 14 Oct 2026 | §§2–5, C |
| Lemma 1 (original form) and its application; Theorems A and B; Corollary A′; §4's density consequences; B.2's consequences; B.3's counterexample and repair; Appendix C's objection and proposition | here | |

**Limits.** 44 of the 49 works citing the paper remain unopened; nothing citing Salehi or Grenet has been examined; searches were English-language and index-based. These credits record who contributed what here; they are not claims of historical priority. Absence of a found critique is not evidence of absence.

**The correction record.** No amendment was found in the records checked: arXiv carries no v3, and Crossref returns no registered update for `10.1016/j.aam.2004.10.003` (an unregistered erratum would not appear). The claim appears, citing the paper ahead of its journal publication, in the revised version of Calude, Calude and Marcus, *Passages of Proof* (arXiv:math/0305213v2, 11 August 2004, §4, p. 7): "the probability that an *n*-bit statement is provable tends to zero when *n* tends to infinity (see Calude and Jürgensen)." The first version (v1, 14 May 2003) has instead, at that point, the footnote "No probabilistic similar result has been (yet?) proven." Later restatements by its first author were seen only as index snippets, not read from source, and are not cited here. Grenet's published Theorem 4 restates the conditional density claim; his corrections concern δ<sub><i>g</i></sub> and Theorem 4.4, not that claim. Nothing in this record establishes what any author knew or intended, and no such inference is drawn.

## Appendix F — methods and disclosure

First written by Florence, an AI, at Magnus Ribsskog's machine, at the invitation of a colleague who believed this paper contained an error but had not located it.

Sophie, an AI collaborator working on OpenAI models in the same household, contributed the results credited to her in Appendix E, reviewed each version, and co-drafted the 10 October revision. This version answers a review of that revision by Calia (an OpenAI model, ChatGPT), who checked the proofs and recomputed the constants, and Sophie's response to it, which read Salehi v8 and the cited passages directly. Earlier versions were reviewed cold by other model instances; every correction they produced is recorded in the working record (the 10 October revision and its verification log), which is kept rather than overwritten.

Numerical claims were computed rather than recalled. The proofs of §§2–4 are meant to be checkable by hand.

Changes from the version sent to C. S. Calude on 14 October 2026: one clause removed from the summary's prior-work paragraph, now headed "Prior work"; one sentence of §4 made explicit about its denominator; the alphabet size written *q*, to keep it apart from Robinson's **Q**; two first-person singulars made impersonal; this appendix revised; the byline and date; and a fresh rendering. No result, proof or constant is changed.

*Corrections are wanted more than agreement.*

## References

* C. S. Calude and H. Jürgensen, Is complexity a source of incompleteness?, *Adv. Appl. Math.* **35** (2005) 1–15; arXiv:math/0408144v2 (15 Nov 2004).
* C. S. Calude, H. Jürgensen and M. Zimand, Is independence an exception?, *Appl. Math. Comput.* **66** (1994) 63–76.
* C. S. Calude, E. Calude and S. Marcus, Passages of proof, arXiv:math/0305213v2 (11 Aug 2004); v1, 14 May 2003.
* B. Grenet, Acceptable complexity measures of theorems, *Complex Systems* **18**:4 (2010) 403–425; arXiv:0910.0045.
* S. Salehi, On Chaitin's heuristic principle and halting probability, arXiv:2310.14807v8 (10 Apr 2026); v1, 23 Oct 2023.
* M. Moczurad, J. Tyszkiewicz and M. Zaionc, Statistical properties of simple types, *Math. Struct. Comput. Sci.* **10**(5) (2000) 575–594.
* M. Zaionc, Probability distribution for simple tautologies, *Theoret. Comput. Sci.* **355**(2) (2006) 243–260.
* Z. Kostrzycka and M. Zaionc, Asymptotic densities in logic and type theory, *Studia Logica* **88** (2008) 385–403; doi:10.1007/s11225-008-9110-0.
* G. Barmpalias and A. Lewis-Pye, Differences of halting probabilities, *J. Comput. System Sci.* **89** (2017) 349–360; doi:10.1016/j.jcss.2017.06.002; arXiv:1604.00216.
* G. Barmpalias, Aspects of Chaitin's Omega, arXiv:1707.08109v5, §2.5.
