import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LiftSystemComplexConjugation
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SameOrbitRefl
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_system_complex_conjugation : ∀ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] {A : FinHolAtlas e X} {P : Ideal (MRing ι)} {U : X → Set X} {lift : X → X → (Σ k, ι k) → ℂ}, IsLiftSys A P U lift → ∃ c : X → X, (∀ x, SameOrbit (lift (c x) (c x)) (cj (lift x x))) ∧ Continuous c ∧ ∀ x, c (c x) = x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Cj.exists_conj_of_isLiftSys | exact GlobalTheory.CompanionTheory.Ar.PB.Cj.exists_conj_of_isLiftSys | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Cj.exists_conj_of_isLiftSys <;> assumption)
