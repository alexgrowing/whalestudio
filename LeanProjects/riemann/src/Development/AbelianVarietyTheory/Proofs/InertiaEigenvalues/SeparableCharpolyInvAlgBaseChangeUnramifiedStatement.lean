import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeparableCharpolyInvAlgBaseChangeUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separable_charpoly_invAlgBaseChangeUnramified : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)), B.P.Separable → (overExt φ B ψ hψ hσ).P.Separable := by
  first | exact @GlobalTheory.UnitLemma.Unr.charpoly_overExt_separable | exact GlobalTheory.UnitLemma.Unr.charpoly_overExt_separable | (intros; apply GlobalTheory.UnitLemma.Unr.charpoly_overExt_separable <;> assumption)
