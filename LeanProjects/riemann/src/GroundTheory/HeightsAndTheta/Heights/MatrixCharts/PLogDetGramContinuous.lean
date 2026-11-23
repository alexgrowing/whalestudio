import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsPsh
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.DetIneq
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PshMatrix
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Metric MCPsh
open scoped MatrixOrder ComplexOrder

noncomputable section

namespace MCPsh

theorem continuousOn_inv_of_posDef {X : Type} [TopologicalSpace X] {s : Set X} {g : ℕ}
    {Y : X → Matrix (Fin g) (Fin g) ℝ} (hY : ContinuousOn Y s) (hpd : ∀ x ∈ s, (Y x).PosDef) :
    ContinuousOn (fun x => (Y x)⁻¹) s := by
  intro x hx
  have hdet : (Y x).det ≠ 0 := (hpd x hx).det_pos.ne'
  have hinvR : ContinuousAt (Ring.inverse : ℝ → ℝ) (Y x).det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  have hinvAt : ContinuousAt (Inv.inv : Matrix (Fin g) (Fin g) ℝ → Matrix (Fin g) (Fin g) ℝ)
      (Y x) := continuousAt_matrix_inv _ hinvR
  exact hinvAt.comp_continuousWithinAt (hY x hx)

theorem gram_posDef {g rk : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} {F : Matrix (Fin g) (Fin rk) ℂ}
    (hY : Y.PosDef) (hF : F.rank = rk) :
    (Fᴴ * (Y⁻¹).map (fun x : ℝ => (x : ℂ)) * F).PosDef := by
  have hinj : Function.Injective F.mulVec := mulVec_injective_of_rank (by rw [hF, Fintype.card_fin])
  have := (cx_posDef hY).inv.conjTranspose_mul_mul_same hinj
  rwa [cx_inv ((Matrix.isUnit_iff_isUnit_det _).mp hY.isUnit)] at this

theorem continuous_gram (g rk : ℕ) :
    Continuous (fun p : Matrix (Fin g) (Fin rk) ℂ × Matrix (Fin g) (Fin g) ℝ =>
      p.1ᴴ * p.2.map (fun x : ℝ => (x : ℂ)) * p.1) := by
  have h1 : Continuous (fun p : Matrix (Fin g) (Fin rk) ℂ × Matrix (Fin g) (Fin g) ℝ => p.1) :=
    continuous_fst
  have h2 : Continuous (fun p : Matrix (Fin g) (Fin rk) ℂ × Matrix (Fin g) (Fin g) ℝ =>
      p.2.map (fun x : ℝ => (x : ℂ))) := continuous_snd.matrix_map Complex.continuous_ofReal
  exact (h1.matrix_conjTranspose.matrix_mul h2).matrix_mul h1

end MCPsh

theorem LogDetGramContinuous.proof : LogDetGramContinuous.Statement := by
  intro X _ s g rk Y F hY hF hpd hr
  have hYinv := continuousOn_inv_of_posDef hY hpd
  have hΦ : Continuous (fun p : Matrix (Fin g) (Fin rk) ℂ × Matrix (Fin g) (Fin g) ℝ =>
      (p.1ᴴ * p.2.map (fun x : ℝ => (x : ℂ)) * p.1).det.re) :=
    Complex.continuous_re.comp (continuous_gram g rk).matrix_det
  have hG := hΦ.comp_continuousOn (hF.prodMk hYinv)
  simp only [Function.comp_def] at hG
  show ContinuousOn (fun x => Real.log ((F x)ᴴ * ((Y x)⁻¹).map (fun x : ℝ => (x : ℂ)) * F x).det.re) s
  refine hG.log fun x hx => ?_
  have h := MCDet.re_det_pos (gram_posDef (hpd x hx) (hr x hx))
  rw [RCLike.re_to_complex] at h
  exact h.ne'

end

end GroundTheory.Heights₂.Heights
