import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAdeleCoverModFieldShrunkCompact
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValHalfInf
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.Eis.Conv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adele_cover_mod_field_shrunk_compact : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∃ (Ω : Set (AF F)) (C : ℝ), IsCompact Ω ∧ ∀ m : ℕ, ∃ Y : Finset (AF F), (Y.card : ℝ) ≤ C * ((2 : ℝ) ^ Fintype.card (InfinitePlace F)) ^ m ∧ ∀ a : AF F, ∃ x : F, ∃ y ∈ Y, ∃ ω ∈ Ω, a = algebraMap F (AF F) x + y + (halfInf F).1 ^ m * ω := by
  first | exact @GlobalTheory.Eis.ConvCover.exists_cover | exact GlobalTheory.Eis.ConvCover.exists_cover | (intros; apply GlobalTheory.Eis.ConvCover.exists_cover <;> assumption)
