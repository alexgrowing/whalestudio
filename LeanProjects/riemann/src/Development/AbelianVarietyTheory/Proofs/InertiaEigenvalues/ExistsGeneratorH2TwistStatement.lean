import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGeneratorH2Twist
import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_H2_twist : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] {G : Type} [Group G] [TopologicalSpace G], Formalism.GaloisCohomology.LocalTateDualityK → FiniteDimensional ℚ_[p] K → PadicCoeff p O → ∀ (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}, IsCyc p K (carry i ε) → ∃ z : H2 (twist ε O), Function.Bijective (fun a : O => a • z) := by
  first | exact @GlobalTheory.FreeTwistH2.exists_free_H2_twist | exact GlobalTheory.FreeTwistH2.exists_free_H2_twist | (intros; apply GlobalTheory.FreeTwistH2.exists_free_H2_twist <;> assumption)
