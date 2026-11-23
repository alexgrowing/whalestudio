import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

namespace GlobalTheory.FlatClosed

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {x : X}

theorem contDiffAt_det {ι : Type} [Fintype ι] [DecidableEq ι] {M : X → Matrix ι ι ℝ}
    (h : ∀ a b, ContDiffAt ℝ ∞ (fun y => M y a b) x) : ContDiffAt ℝ ∞ (fun y => (M y).det) x := by
  simp only [Matrix.det_apply']
  exact ContDiffAt.sum fun σ _ => contDiffAt_const.mul (contDiffAt_prod fun i _ => h _ _)

theorem contDiffAt_inv {ι : Type} [Fintype ι] [DecidableEq ι] {M : X → Matrix ι ι ℝ}
    (h : ∀ a b, ContDiffAt ℝ ∞ (fun y => M y a b) x) (h0 : (M x).det ≠ 0) (a b : ι) :
    ContDiffAt ℝ ∞ (fun y => (M y)⁻¹ a b) x := by
  have e : (fun y => (M y)⁻¹ a b) =
      fun y => ((M y).det)⁻¹ * ((M y).updateRow b (Pi.single a 1)).det := by
    funext y
    rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply, Ring.inverse_eq_inv',
      smul_eq_mul]
  rw [e]
  refine ((contDiffAt_det h).inv h0).mul (contDiffAt_det fun i i' => ?_)
  by_cases hi : i = b
  · subst hi
    simpa using contDiffAt_const
  · simpa [Matrix.updateRow_ne hi] using h i i'

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g : ℕ}

theorem contDiffAt_flat {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} (hτ : IsPeriodMap B τ)
    {P : Pt E g} (hP : P ∈ cov B g) : ContDiffAt ℝ ∞ (flat τ) P := by
  have hb : P.1 ∈ B := hP.1
  have hent : ∀ i j, ContDiffAt ℝ ∞ (fun Q : Pt E g => τ Q.1 i j) P := fun i j =>
    (((GlobalTheory.SCV.contDiffOn_of_differentiableOn hτ.1 (hτ.2.1 i j) ∞).contDiffAt
      (hτ.1.mem_nhds hb)).restrict_scalars ℝ).comp P contDiffAt_fst
  have him : ∀ i j, ContDiffAt ℝ ∞ (fun Q : Pt E g => ((τ Q.1).map Complex.im) i j) P :=
    fun i j => (Complex.imCLM.contDiff.contDiffAt).comp P (hent i j)
  have hre : ∀ i j, ContDiffAt ℝ ∞ (fun Q : Pt E g => ((τ Q.1).map Complex.re) i j) P :=
    fun i j => (Complex.reCLM.contDiff.contDiffAt).comp P (hent i j)
  have hdet : ((τ P.1).map Complex.im).det ≠ 0 := (hτ.2.2 _ hb).2.det_pos.ne'
  have hinv := contDiffAt_inv him hdet
  have hzi : ∀ k, ContDiffAt ℝ ∞ (fun Q : Pt E g => (Q.2 k).im) P := fun k =>
    (Complex.imCLM.contDiff.comp ((contDiff_apply ℝ ℂ k).comp contDiff_snd)).contDiffAt
  have hzr : ∀ k, ContDiffAt ℝ ∞ (fun Q : Pt E g => (Q.2 k).re) P := fun k =>
    (Complex.reCLM.contDiff.comp ((contDiff_apply ℝ ℂ k).comp contDiff_snd)).contDiffAt
  have hp : ∀ i, ContDiffAt ℝ ∞ (fun Q : Pt E g =>
      ∑ k, (Q.2 k).im * ((τ Q.1).map Complex.im)⁻¹ k i) P := fun i =>
    ContDiffAt.sum fun k _ => (hzi k).mul (hinv k i)
  rw [contDiffAt_pi]
  rintro (i | i)
  · simpa [flat, flatOf, Matrix.vecMul, dotProduct] using hp i
  · have hprod : ∀ a b, ContDiffAt ℝ ∞ (fun Q : Pt E g =>
        (((τ Q.1).map Complex.im)⁻¹ * (τ Q.1).map Complex.re) a b) P := fun a b => by
      simp only [Matrix.mul_apply]
      exact ContDiffAt.sum fun l _ => (hinv a l).mul (hre l b)
    have : ContDiffAt ℝ ∞ (fun Q : Pt E g => (Q.2 i).re -
        ∑ k, (Q.2 k).im * (((τ Q.1).map Complex.im)⁻¹ * (τ Q.1).map Complex.re) k i) P :=
      (hzr i).sub (ContDiffAt.sum fun k _ => (hzi k).mul (hprod k i))
    simpa [flat, flatOf, Matrix.vecMul, dotProduct] using this

theorem extDeriv_om0 : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ},
    IsPeriodMap B τ → ∀ P ∈ cov B g, extDeriv (om0 τ) P = 0 := by
  intro g E _ _ _ B τ hτ P hP
  have e : om0 τ = fun Q => ((fun _ : Fl g => symp g) (flat τ Q)).compContinuousLinearMap
      (fderiv ℝ (flat τ) Q) := rfl
  rw [e, extDeriv_pullback (differentiableAt_const _) (contDiffAt_flat hτ hP)
    (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)]
  have h0 : extDeriv (fun _ : Fl g => symp g) (flat τ P) = 0 := by
    ext v
    simp [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  rw [h0]
  ext v
  simp

end GlobalTheory.FlatClosed
