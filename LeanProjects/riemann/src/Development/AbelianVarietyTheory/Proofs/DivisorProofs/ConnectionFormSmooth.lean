import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFormSmoothOnCover
open Matrix Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Pullback
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionForm.ConnSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}

theorem contDiffOn_det {B : Set E} {A : E → Matrix (Fin g) (Fin g) ℂ}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun b => A b i j) B) : ContDiffOn ℝ ∞ (fun b => (A b).det) B := by
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => hA _ _)

theorem contDiffOn_inv_apply {B : Set E} {A : E → Matrix (Fin g) (Fin g) ℂ}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun b => A b i j) B) (hd : ∀ b ∈ B, (A b).det ≠ 0) (i j : Fin g) :
    ContDiffOn ℝ ∞ (fun b => (A b)⁻¹ i j) B := by
  have e : ∀ b, (A b)⁻¹ i j = ((A b).det)⁻¹ * (A b).adjugate i j := by
    intro b; rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  simp only [e]
  refine ((contDiffOn_det hA).inv hd).mul ?_
  simp only [Matrix.adjugate_apply]
  refine contDiffOn_det fun k l => ?_
  by_cases hk : k = j
  · simp only [Matrix.updateRow_apply, hk, if_true]; exact contDiffOn_const
  · simp only [Matrix.updateRow_apply, hk, if_false]; exact hA k l

end GlobalTheory.TorsionForm.ConnSmooth

open GlobalTheory.TorsionForm.ConnSmooth in

theorem GlobalTheory.TorsionForm.ConnSmooth.connForm_contDiffOn : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g n : ℕ} (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (s : Pt E g → Ext (n + n + g)), IsPeriodMap B τ → ContDiffOn ℝ ∞ s (cov B g) → ∀ v : E, ContDiffOn ℝ ∞ (fun Q : Pt E g => connForm τ Q.1 v (s Q)) (cov B g) := by
  intro E _ _ _ g n B τ s hτ hs v
  obtain ⟨hB, hhol, hsieg⟩ := hτ
  have him : ∀ a e, ContDiffOn ℝ ∞ (fun b => imPart τ b a e) B := by
    intro a e
    have h0 : ContDiffOn ℂ ∞ (fun b => τ b a e) B :=
      (GlobalTheory.FlatSmooth.analyticOnNhd_of_differentiableOn hB (hhol a e)).contDiffOn hB.uniqueDiffOn
    have h1 : ContDiffOn ℝ ∞ (fun b => τ b a e) B := h0.restrict_scalars ℝ
    have h2 : ContDiffOn ℝ ∞ (fun b => ((τ b a e).im : ℂ)) B :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (Complex.imCLM.contDiff.comp_contDiffOn h1)
    simpa [imPart] using h2
  have hd01 : ∀ a e, ContDiffOn ℝ ∞ (fun b => d01 (fun b' => imPart τ b' a e) b v) B := by
    intro a e
    have hf := (him a e).fderiv_of_isOpen (m := ∞) hB (by simp)
    have hA := hf.clm_apply (contDiffOn_const (c := v))
    have hB := hf.clm_apply (contDiffOn_const (c := Complex.I • v))
    unfold d01
    exact (contDiffOn_const (c := (1 / 2 : ℂ))).smul (hA.add ((contDiffOn_const (c := Complex.I)).smul hB))
  have hdet : ∀ b ∈ B, (imPart τ b).det ≠ 0 := by
    intro b hb
    have hp : ((τ b).map Complex.im).PosDef := (hsieg b hb).2
    rw [show imPart τ b = Complex.ofRealHom.mapMatrix ((τ b).map Complex.im) from by
      ext; simp [imPart], ← RingHom.map_det]
    exact Complex.ofReal_ne_zero.2 hp.det_pos.ne'
  have hinv := contDiffOn_inv_apply him hdet
  have hcoef : ∀ a c, ContDiffOn ℝ ∞ (fun b => ((Matrix.of fun a e =>
      d01 (fun b' => imPart τ b' a e) b v) * (imPart τ b)⁻¹) a c) B := by
    intro a c
    simp only [Matrix.mul_apply, Matrix.of_apply]
    exact ContDiffOn.sum fun k _ => (hd01 a k).mul (hinv k c)
  have hfst : MapsTo Prod.fst (cov B g) B := fun Q hQ => hQ.1
  have hc : ∀ T, ContDiffOn ℝ ∞ (fun Q => s Q T) (cov B g) := fun T => contDiffOn_pi.1 hs T
  have hwc : ∀ a c, ContDiffOn ℝ ∞ (fun Q => wedge (dzb n c) (contr (dzb n a) (s Q))) (cov B g) := by
    intro a c
    refine contDiffOn_pi.2 fun S => ?_
    unfold wedge contr
    by_cases h1 : dzb n c ∈ S <;> by_cases h2 : dzb n a ∈ S.erase (dzb n c) <;>
      simp only [h1, h2, if_true, if_false] <;>
      first | exact contDiffOn_const | exact contDiffOn_const.mul (contDiffOn_const.mul (hc _))
  unfold connForm
  exact ContDiffOn.sum fun a _ => ContDiffOn.sum fun c _ =>
    ((hcoef a c).comp contDiffOn_fst hfst).smul (hwc a c)
