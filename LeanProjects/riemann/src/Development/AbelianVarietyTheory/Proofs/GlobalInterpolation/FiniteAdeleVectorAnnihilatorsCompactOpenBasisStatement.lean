import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteAdeleVectorAnnihilatorsCompactOpenBasis
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdeleVector_annihilators_compact_open_basis : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a → (∀ L : AddSubgroup (Fin N → Af F), IsOpen (L : Set (Fin N → Af F)) → IsCompact {u : Fin N → Af F | ∀ y ∈ L, ψ (pairA F 0 (Bd (Af F) a u y)) = 1}) ∧ (∀ K : Set (Fin N → Af F), IsCompact K → {y : Fin N → Af F | ∀ u ∈ K, ψ (pairA F 0 (Bd (Af F) a u y)) = 1} ∈ 𝓝 0) ∧ ∀ U ∈ 𝓝 (0 : Fin N → Af F), ∃ L : AddSubgroup (Af F), IsOpen (L : Set (Af F)) ∧ IsCompact (L : Set (Af F)) ∧ ∀ u : Fin N → Af F, (∀ l, u l ∈ L) → u ∈ U := by
  first | exact @GlobalTheory.SWQ.finite_annihilators | exact GlobalTheory.SWQ.finite_annihilators | (intros; apply GlobalTheory.SWQ.finite_annihilators <;> assumption)
