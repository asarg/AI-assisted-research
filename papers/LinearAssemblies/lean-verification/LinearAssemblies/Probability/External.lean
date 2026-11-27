import LinearAssemblies.Probability.UniformChain
import LinearAssemblies.Probability.Reachable

set_option autoImplicit false

namespace LinearAssemblies.Probability

/-- E01: standard finite absorbing-chain results, supplied as a theorem hypothesis.
Source: Grinstead--Snell, Introduction to Probability, Section 11.2,
Theorems 11.3--11.5 (normalization, finite mean, invertible first-step equations).
The contract concerns arbitrary finite uniform graphs, with no tile or cost claim.
-/
structure FiniteAbsorptionLaw : Prop where
  normalized : ∀ {S : Type} [Fintype S] (g : UniformGraph S), g.Haltable →
    ∀ x, HasSum (fun k => g.stoppingMass k x) 1
  finite_mean : ∀ {S : Type} [Fintype S] (g : UniformGraph S), g.Haltable →
    ∀ x, Summable (fun k : ℕ => (k : ℝ) * g.stoppingMass k x)
  first_step : ∀ {S : Type} [Fintype S] (g : UniformGraph S), g.Haltable →
    g.Potential g.expected
  unique : ∀ {S : Type} [Fintype S] (g : UniformGraph S) (h : S → ℝ),
    g.Haltable → g.Potential h → ∀ x, g.expected x = h x

end LinearAssemblies.Probability
