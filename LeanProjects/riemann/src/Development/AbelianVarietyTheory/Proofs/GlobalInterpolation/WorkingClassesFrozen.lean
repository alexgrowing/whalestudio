import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.SharpRestriction.DesignExistsOfChoices
import Formalism.SharpRestriction.SmoothDesignExistence.DesignExistsDes
import Formalism.SharpRestriction.PageFix
import Formalism.SharpRestriction.Divisibility.SmallFirstModulusBelowScale
import Formalism.SharpRestriction.GlobalSchurBounds.WeightVectorSmallSharesEight
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PageDutiesOfClassSeven
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk GlobalTheory.EX GlobalTheory.Fc

namespace GlobalTheory.Fc

theorem tameDistinctF_iff {eps : ℝ} (Fm : FamP eps) : DC.TameDistinctF Fm ↔ Formalism.MainNotions.TameDistinctF Fm := by
  unfold DC.TameDistinctF Formalism.MainNotions.TameDistinctF
  simp only [DQ.tameDistinct_iff]

theorem dGamDvdF_iff {eps : ℝ} (Fm : FamP eps) : DC.DGamDvdF Fm ↔ Formalism.MainNotions.DGamDvdF Fm := Iff.rfl

theorem codeUpF_iff {eps : ℝ} (Fm : FamP eps) (C0 CH : ℝ) : DC.CodeUpF Fm C0 CH ↔ Formalism.MainNotions.CodeUpF Fm C0 CH := Iff.rfl

theorem working_classes_frozen : (∀ (𝒜 : FamClass) (eps : ℝ) (Fm : FamP eps), (Formalism.MainNotions.WithTw (Formalism.MainNotions.WithSm (fun Fm => 𝒜 Fm ∧ Formalism.MainNotions.DGamDvdF Fm ∧ Formalism.MainNotions.TameDistinctF Fm ∧ Formalism.MainNotions.BoxesF Fm ∧ Formalism.MainNotions.QDRowsF Fm ∧ Fm.CYL ≤ 9)) Fm ↔ W1 𝒜 Fm) ∧ (Formalism.MainNotions.Des (fun Fm => 𝒜 Fm ∧ Formalism.MainNotions.DGamDvdF Fm ∧ Formalism.MainNotions.TameDistinctF Fm ∧ Formalism.MainNotions.BoxesF Fm ∧ Formalism.MainNotions.QDRowsF Fm ∧ Fm.CYL ≤ 9) 3 Fm ↔ W3 𝒜 Fm)) ∧ (∀ (𝒜 : FamClass) (cT : ℝ → ℝ → ℝ), (DC.MinkDiv → DC.DesignChoices (DC.WithTw 𝒜) 3 cT) → Formalism.MainNotions.MinkDiv → Formalism.MainNotions.DesignChoices (Formalism.MainNotions.WithTw 𝒜) 3 cT) := by
  refine ⟨fun 𝒜 eps Fm => ?_, fun 𝒜 cT h hM => ?_⟩
  · have e1 : Formalism.MainNotions.WithTw (Formalism.MainNotions.WithSm (fun Fm => 𝒜 Fm ∧ Formalism.MainNotions.DGamDvdF Fm ∧ Formalism.MainNotions.TameDistinctF Fm ∧ Formalism.MainNotions.BoxesF Fm ∧
        Formalism.MainNotions.QDRowsF Fm ∧ Fm.CYL ≤ 9)) Fm ↔ W1 𝒜 Fm := by
      simp only [Formalism.MainNotions.WithTw, Formalism.MainNotions.WithSm, W1, tameDistinctF_iff, dGamDvdF_iff]
    refine ⟨e1, ?_⟩
    simp only [Formalism.MainNotions.Des, W3, ← e1]
  · obtain ⟨ε0, h0, h⟩ := h hM
    refine ⟨ε0, h0, fun eps he hle K => ?_⟩
    obtain ⟨Fm, CH, C5, Cb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h eps he hle K
    exact ⟨Fm, CH, C5, Cb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, (tameDistinctF_iff Fm).1 h15, h16,
      (codeUpF_iff Fm 3 CH).1 h17, h18⟩

end GlobalTheory.Fc
