import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValResultantEqDegreeMulUnramifiedExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.val_resultant_eq_degree_mul_unramifiedExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → Odd d → ∀ (B₁ B₂ : InvAlg K) (ψ₁ : K'.E →+* B₁.A) (ψ₂ : K'.E →+* B₂.A) (h₁ : ∀ e, ψ₁ (φ e) = algebraMap K.E B₁.A e) (h₁' : ∀ e, B₁.σ (ψ₁ e) = ψ₁ (K'.c e)) (h₂ : ∀ e, ψ₂ (φ e) = algebraMap K.E B₂.A e) (h₂' : ∀ e, B₂.σ (ψ₂ e) = ψ₂ (K'.c e)), (∀ y : K'.O, (ψ₁.prod ψ₂) (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) → (B₁.P * B₂.P).Separable → ∀ s : K'.O, (∃ Q : K'.O[X], Q.map (algebraMap K'.O K'.E) = (overExt φ B₁ ψ₁ h₁ h₁').P * (overExt φ B₂ ψ₂ h₂ h₂').P ∧ Q.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O s)) ^ Q.natDegree) → val K.O (resultant B₁.P B₂.P) = d * val K'.O (resultant (overExt φ B₁ ψ₁ h₁ h₁').P (overExt φ B₂ ψ₂ h₂ h₂').P) := by
  first | exact @GlobalTheory.UnitLemma.Unr.ResVal.val_resultant_unr | exact GlobalTheory.UnitLemma.Unr.ResVal.val_resultant_unr | (intros; apply GlobalTheory.UnitLemma.Unr.ResVal.val_resultant_unr <;> assumption)
