import LinearAssemblies.Probability.DiscreteLaw

set_option autoImplicit false

namespace LinearAssemblies.Probability

/-- An arbitrary discrete summand, with an asserted mean and scale. -/
structure BernsteinInput where
  mass : ℕ → ℝ
  mean : ℝ
  scale : ℝ

def BernsteinInput.Valid (b : BernsteinInput) : Prop :=
  (∀ n, 0 ≤ b.mass n) ∧ HasSum b.mass 1 ∧
  HasSum (fun n : ℕ => (n : ℝ) * b.mass n) b.mean ∧ 0 < b.scale ∧
  Summable (fun n => b.mass n * Real.exp (|(n : ℝ) - b.mean| / b.scale)) ∧
  (∑' n, b.mass n * Real.exp (|(n : ℝ) - b.mean| / b.scale)) ≤ 2

/-- E03a: the tail-to-exponential-moment implication in Vershynin,
High-Dimensional Probability, first edition, Proposition 2.7.1 (a) => (d).
This is a generic theorem about arbitrary discrete laws and arbitrary observables.
The universal constant has been harmlessly enlarged to at least one. -/
def SubexponentialEquivalence : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ (p X : ℕ → ℝ) (K : ℝ),
    (∀ n, 0 ≤ p n) → HasSum p 1 → 0 < K →
    (∀ u : ℝ, 0 ≤ u → magnitudeTail p X u ≤ 2 * Real.exp (-u / K)) →
    Summable (fun n => p n * Real.exp (|X n| / (C * K))) ∧
    (∑' n, p n * Real.exp (|X n| / (C * K))) ≤ 2

/-- E03b: Vershynin, Theorem 2.8.1, in discrete convolution form.
Every normalization, mean, exponential integrability, and scale bound is explicit.
The convolution is the independent product law pushed forward by addition.
V and B are upper bounds on the sum of squared scales and largest scale. -/
def BernsteinLaw : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (bs : List BernsteinInput) (V B t : ℝ),
    (∀ b ∈ bs, b.Valid) → 0 < V → 0 < B → 0 < t →
    (bs.map fun b => b.scale ^ 2).sum ≤ V →
    (∀ b ∈ bs, b.scale ≤ B) →
    deviation (independentSum (bs.map BernsteinInput.mass))
        (bs.map BernsteinInput.mean).sum t ≤
      2 * Real.exp (-c * min (t ^ 2 / V) (t / B))

end LinearAssemblies.Probability
