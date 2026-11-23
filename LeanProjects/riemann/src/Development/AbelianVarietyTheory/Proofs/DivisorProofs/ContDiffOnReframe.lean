import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapMoebiusDenomUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFormSmoothOnCover
open Matrix MeasureTheory Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ReframeSmooth

theorem contDiffOn_det_cplx {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ}
    {M : X → Matrix (Fin n) (Fin n) ℂ} {s : Set X}
    (h : ∀ a b, ContDiffOn ℝ ∞ (fun v => M v a b) s) : ContDiffOn ℝ ∞ (fun v => (M v).det) s := by
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => h _ _)

theorem contDiffOn_inv_cplx {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ}
    {M : X → Matrix (Fin n) (Fin n) ℂ} {s : Set X}
    (h : ∀ a b, ContDiffOn ℝ ∞ (fun v => M v a b) s) (hd : ∀ v ∈ s, (M v).det ≠ 0) (a b : Fin n) :
    ContDiffOn ℝ ∞ (fun v => (M v)⁻¹ a b) s := by
  have e : ∀ v, (M v)⁻¹ a b = ((M v).det)⁻¹ * (M v).adjugate a b := fun v => by
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rfl
  simp only [e, Matrix.adjugate_apply]
  refine ContDiffOn.mul ((contDiffOn_det_cplx h).inv hd) (contDiffOn_det_cplx fun c d => ?_)
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiffOn_const
  · exact h _ _

theorem reframe_contDiffOn : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g : ℕ} (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (γ : Sp g), IsPeriodMap B τ → IsPeriodMap B (fun b => moeb γ (τ b)) → ContDiffOn ℝ ∞ (reframe τ γ) (cov B g) := by
  intro E _ _ _ g B τ γ hτ hγ
  have hU := GlobalTheory.SiegelAction.den_isUnit_of_isPeriodMap B τ γ hγ
  have hden : ∀ k l, ContDiffOn ℝ ∞ (fun P : Pt E g => den γ (τ P.1) k l) (cov B g) := by
    intro k l
    simp only [den, Matrix.add_apply, Matrix.mul_apply, Matrix.map_apply]
    exact (ContDiffOn.sum fun m _ => contDiffOn_const.mul (GlobalTheory.FlatSmooth.contDiffOn_tau hτ m l)).add
      contDiffOn_const
  have hent : ∀ i j, ContDiffOn ℝ ∞ (fun P : Pt E g => (den γ (τ P.1))⁻¹ i j) (cov B g) :=
    contDiffOn_inv_cplx hden fun P hP =>
      ((Matrix.isUnit_iff_isUnit_det _).1 (hU P.1 hP.1)).ne_zero
  refine contDiffOn_fst.prodMk (contDiffOn_pi.2 fun j => ?_)
  simp only [reframe, Matrix.vecMul, dotProduct]
  refine ContDiffOn.sum fun i _ => ContDiffOn.mul ?_ (hent i j)
  exact ((contDiff_apply ℝ ℂ i).comp contDiff_snd).contDiffOn

end GlobalTheory.ReframeSmooth
