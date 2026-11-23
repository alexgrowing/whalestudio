import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGroupMatGroupUnimodular
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LintegralInvEqOfBiInvariantMatGroup

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem isUnimod_GG : ∀ (k r : ℕ) (μ : Measure (Mt k r)), IsHaarOn (GG k r) μ → IsUnimod (GG k r) μ := by
  intro k r μ hμ
  obtain ⟨hG, h⟩ := GlobalTheory.unitaryGroup_matGroup_unimodular k r
  obtain ⟨hM, hR⟩ := h μ hμ
  refine ⟨fun s hs => hR s hs, ?_⟩
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf measurable_invM]
  exact GlobalTheory.HaarInversion.lintegral_inv_eq _ (GG k r) μ hG hM hR f hf

end GlobalTheory.SgInf

example : ∀ (k r : ℕ) (μ : Measure (Mt k r)), IsHaarOn (GG k r) μ → IsUnimod (GG k r) μ := GlobalTheory.SgInf.isUnimod_GG
