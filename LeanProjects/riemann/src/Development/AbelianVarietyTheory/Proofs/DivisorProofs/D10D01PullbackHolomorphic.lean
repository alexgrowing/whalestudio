import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
open Matrix Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Pullback
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionForm.Pullback

theorem fderiv_baseChange_apply {E E' W : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] [NormedAddCommGroup W] [NormedSpace ℝ W] {g : ℕ}
    (φ : E' → E) (F : Pt E g → W) (P w : Pt E' g) (hφ : DifferentiableAt ℂ φ P.1)
    (hF : DifferentiableAt ℝ F (φ P.1, P.2)) :
    fderiv ℝ (fun Q : Pt E' g => F (φ Q.1, Q.2)) P w =
      fderiv ℝ F (φ P.1, P.2) (fderiv ℂ φ P.1 w.1, w.2) := by
  have hψ : HasFDerivAt (fun Q : Pt E' g => (φ Q.1, Q.2))
      ((((fderiv ℂ φ P.1).restrictScalars ℝ).comp (ContinuousLinearMap.fst ℝ E' (Fin g → ℂ))).prod
        (ContinuousLinearMap.snd ℝ E' (Fin g → ℂ))) P := by
    refine HasFDerivAt.prodMk ?_ hasFDerivAt_snd
    exact (hφ.hasFDerivAt.restrictScalars ℝ).comp P hasFDerivAt_fst
  have h := (hF.hasFDerivAt.comp P hψ).fderiv
  rw [show (fun Q : Pt E' g => F (φ Q.1, Q.2)) = F ∘ (fun Q : Pt E' g => (φ Q.1, Q.2)) from rfl, h]
  rfl

theorem d10_d01_comp_fst_eq_fderiv_of_baseChange : ∀ {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E'] {g m : ℕ} (φ : E' → E) (F : Pt E g → Ext m) (G : Pt E g → ℂ) (P w : Pt E' g), DifferentiableAt ℂ φ P.1 → DifferentiableAt ℝ F (φ P.1, P.2) → DifferentiableAt ℝ G (φ P.1, P.2) → d10 (fun Q : Pt E' g => F (φ Q.1, Q.2)) P w = d10 F (φ P.1, P.2) (fderiv ℂ φ P.1 w.1, w.2) ∧ d01 (fun Q : Pt E' g => F (φ Q.1, Q.2)) P w = d01 F (φ P.1, P.2) (fderiv ℂ φ P.1 w.1, w.2) ∧ d10 (fun Q : Pt E' g => G (φ Q.1, Q.2)) P w = d10 G (φ P.1, P.2) (fderiv ℂ φ P.1 w.1, w.2) := by
  intro E E' _ _ _ _ g m φ F G P w hφ hF hG
  have hI : (Complex.I • w).1 = Complex.I • w.1 := rfl
  have key : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (H : Pt E g → W),
      DifferentiableAt ℝ H (φ P.1, P.2) → ∀ v : Pt E' g,
      fderiv ℝ (fun Q : Pt E' g => H (φ Q.1, Q.2)) P v = fderiv ℝ H (φ P.1, P.2) (fderiv ℂ φ P.1 v.1, v.2) :=
    fun H hH v => fderiv_baseChange_apply φ H P v hφ hH
  have hw : ((fderiv ℂ φ P.1 (Complex.I • w).1, (Complex.I • w).2) : Pt E g) =
      Complex.I • ((fderiv ℂ φ P.1 w.1, w.2) : Pt E g) := by
    simp [Prod.smul_mk, map_smul]
  refine ⟨?_, ?_, ?_⟩
  · simp only [d10, key F hF, hw]
  · simp only [d01, key F hF, hw]
  · simp only [d10, key G hG, hw]

end GlobalTheory.TorsionForm.Pullback
