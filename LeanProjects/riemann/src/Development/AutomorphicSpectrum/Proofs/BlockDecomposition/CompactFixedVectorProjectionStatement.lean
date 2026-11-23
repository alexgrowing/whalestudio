import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactFixedVectorProjection
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_fixed_vector_projection : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G), IsCompact (J : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∃ E : V →ₗ[ℂ] V, (∀ v, E v ∈ fixed π J) ∧ (∀ v ∈ fixed π J, E v = v) ∧ (∀ l : Module.Dual ℂ V, (∀ x ∈ J, l ∘ₗ π x = l) → l ∘ₗ E = l) ∧ (∀ x ∈ J, E ∘ₗ π x = E) ∧ ∀ (u : V) (H : Subgroup G), H ≤ J → (∀ h ∈ H, π h u = u) → ∀ (r : ℕ) (x : Fin r → G), 0 < r → (∀ i, x i ∈ J) → (∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈ H) → E u = ((r : ℂ)⁻¹) • ∑ i, π (x i) u := by
  first | exact @GlobalTheory.CompanionTheory.CompactAvg.exists_average | exact GlobalTheory.CompanionTheory.CompactAvg.exists_average | (intros; apply GlobalTheory.CompanionTheory.CompactAvg.exists_average <;> assumption)
