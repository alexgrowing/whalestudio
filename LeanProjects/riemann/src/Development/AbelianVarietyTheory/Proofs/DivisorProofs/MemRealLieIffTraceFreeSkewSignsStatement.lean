import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRealLieIffTraceFreeSkewSigns
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfIsIdent
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CovTop.VolUp GlobalTheory.CovTop.VolUp.FrameBox

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_realLie_iff_traceFree_skew_signs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r), IsIdent p q Ψ G x σ A e → ∀ Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r), Y ∈ (realLie Ψ G).comap (fromFrame x) ↔ SkewCond (sgnR σ e) Y := by
  first | exact @GlobalTheory.CovTop.VolUp.FrameBox.mem_comap_realLie_iff_skewCond | exact GlobalTheory.CovTop.VolUp.FrameBox.mem_comap_realLie_iff_skewCond | (intros; apply GlobalTheory.CovTop.VolUp.FrameBox.mem_comap_realLie_iff_skewCond <;> assumption)
