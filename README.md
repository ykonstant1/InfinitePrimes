### Infinite Primes from scratch

This is a Lean 4 proof of the decidability of primality and the
infinitude of prime numbers using only Nat lemmas from core, the
propext axiom and elementary tactics up to 'simp only'.

Definitions of divisibility, primality, etc. are based on Nat
arithmetic operations and all decidability instances proved from
scratch.

This project was meant to familiarize me with Lean's syntax and
term-based proofs; as such, I avoided tactics as much as
possible, writing terms by hand instead, and developed all the
necessary notions of divisibility and relevant theorems from
scratch.  I also wanted to depend on minimal axioms and managed
to rely only on propositional extensionality.

### Main results

There are two takeaway results in this codebase : the decidability
of primality, and the infinitude of primes in the form of an
unboundedness statement:

```lean
instance : Decidable (Prime n) := sorry

theorem unbounded_primes :
    ∀ n, ∃ p, Prime p ∧ p > n := sorry
```

The definition of primality is given by

```lean
def Prime (k : Nat) :=
  2 ≤ k ∧ ∀ n m : Nat, (k ∣ n * m) → (k ∣ n) ∨ (k ∣ m)
```

which we prove equivalent to the "internal" definition

```lean
def NatPrime (k : Nat) :=
  2 ≤ k ∧ ∀ m, 2 ≤ m ∧ m < k → (m ∤ k)
```

### Proof structure

The theorems are proven using the following auxiliary results:

1. Every natural at least $2$ has a minimal divisor apart from $1$.

2. The minimal divisor is a `NatPrime`.

3. `NatPrime` and `Prime` are equivalent predicates.

4. Every decidable predicate `p` that is satisfied by some $n$ is
   satisfied by a minimal $n₀$ (this statement is used in several
   places, including 1 and 2).

5. The existence of a number in a bounded interval satisfying a
   decidable predicate is a decidable proposition; so is the
   corresponding universal quantification.

6. A collection of lemmata linking divisibility and the `mod`
   operation, including a convenient restatement of the Euclidean
   algorithm.

7. A definition and elementary properties of the factorial and
   other auxiliary functions.

These are all supported by various lemmata that provide natural
number identities and inequalities.
