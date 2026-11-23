import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsBorelSectionUnitaryOrbitQuadric
import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
open MeasureTheory Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_borelSection_unitary_orbit_quadric : ∀ (P Q : ℕ) (β : ℝ) (x₀ : GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q), β ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.qf x₀ = β → ∃ s : GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q → UpqT P Q, GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.IsSection β x₀ s := by
  first | exact @GlobalTheory.QuadricSection.exists_isSection | exact GlobalTheory.QuadricSection.exists_isSection | (intros; apply GlobalTheory.QuadricSection.exists_isSection <;> assumption)
