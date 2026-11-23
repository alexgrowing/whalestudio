import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalFunctionDualLabel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfRegularForms
open IsDedekindDomain NumberField Formalism.UG Formalism.IndefR.Mult GlobalTheory.SphPar Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_function_dual_label : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (α : Fin n → ℂ) (φ : GL (Fin n) (P.adicCompletion E) → ℂ), (∀ i, α i ≠ 0) → IsSpherical E P α φ → ∃ φ' : GL (Fin n) (P.adicCompletion E) → ℂ, IsSpherical E P (fun i => (α i.rev)⁻¹) φ' ∧ φ' 1 = φ 1 ∧ ∀ d : List ℤ, d.length = n → hAct (GLint (Fin n) (Ov E P)) (divInd (Ov E P) (dualLab d)) φ' 1 = hAct (GLint (Fin n) (Ov E P)) (divInd (Ov E P) d) φ 1 := by
  first | exact @GlobalTheory.InvTranspose.exists_spherical_dual | exact GlobalTheory.InvTranspose.exists_spherical_dual | (intros; apply GlobalTheory.InvTranspose.exists_spherical_dual <;> assumption)
