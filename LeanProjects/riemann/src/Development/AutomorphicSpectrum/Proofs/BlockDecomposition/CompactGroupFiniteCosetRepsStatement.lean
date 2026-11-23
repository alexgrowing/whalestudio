import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactGroupFiniteCosetReps
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_group_finite_coset_reps : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J H A : Subgroup G), IsCompact (J : Set G) → IsOpen (H : Set G) → H ≤ J → A ≤ J → (∀ y ∈ J, ∃ a ∈ A, a⁻¹ * y ∈ H) → ∃ r : ℕ, 0 < r ∧ ∃ x : Fin r → G, (∀ i, x i ∈ A) ∧ ∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈ H := by
  first | exact @GlobalTheory.CompanionTheory.CosetReps.exists_fin_coset_reps | exact GlobalTheory.CompanionTheory.CosetReps.exists_fin_coset_reps | (intros; apply GlobalTheory.CompanionTheory.CosetReps.exists_fin_coset_reps <;> assumption)
