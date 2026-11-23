import Formalism.HermitianCurvature.HermitianCurvatureProofs.MatExtMulVec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SubMulRight

namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration.MM

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

noncomputable section

variable {X : Type*} [MeasurableSpace X] {n : ℕ}

def MeasM (A : X → Matrix (Fin n) (Fin n) ℂ) : Prop := Measurable fun x => (Matrix.of.symm (A x) : Fin n → Fin n → ℂ)

theorem measM_iff {A : X → Matrix (Fin n) (Fin n) ℂ} : MeasM A ↔ ∀ i j, Measurable fun x => A x i j := by
  simp only [MeasM, measurable_pi_iff]
  exact Iff.rfl

theorem measM_const (C : Matrix (Fin n) (Fin n) ℂ) : MeasM (fun _ : X => C) := measurable_const

theorem measM_of_cont {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    {f : Y → Matrix (Fin n) (Fin n) ℂ} (hf : Continuous fun y => (Matrix.of.symm (f y) : Fin n → Fin n → ℂ))
    {g : X → Y} (hg : Measurable g) : MeasM (fun x => f (g x)) := hf.measurable.comp hg

theorem measM_mul {A B : X → Matrix (Fin n) (Fin n) ℂ} (hA : MeasM A) (hB : MeasM B) : MeasM (fun x => A x * B x) := by
  rw [measM_iff] at hA hB ⊢
  intro i j
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun l _ => (hA i l).mul (hB l j)

theorem measM_star {A : X → Matrix (Fin n) (Fin n) ℂ} (hA : MeasM A) : MeasM (fun x => (A x)ᴴ) := by
  rw [measM_iff] at hA ⊢
  intro i j
  simp only [Matrix.conjTranspose_apply]
  exact continuous_star.measurable.comp (hA j i)

theorem cont_det : Continuous fun M : Fin n → Fin n → ℂ => (Matrix.of M).det :=
  Continuous.matrix_det continuous_id

theorem cont_adj : Continuous fun M : Fin n → Fin n → ℂ => (Matrix.of.symm (Matrix.of M).adjugate : Fin n → Fin n → ℂ) :=
  Continuous.matrix_adjugate continuous_id

theorem measM_inv {A : X → Matrix (Fin n) (Fin n) ℂ} (hA : MeasM A) : MeasM (fun x => (A x)⁻¹) := by
  have hd : Measurable fun x => (A x).det := cont_det.measurable.comp hA
  have hadj : MeasM (fun x => (A x).adjugate) := cont_adj.measurable.comp hA
  rw [measM_iff] at hadj ⊢
  intro i j
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact hd.inv.mul (hadj i j)

variable {k r : ℕ}

theorem measM_nEich (z : Fin (2 * r + k + 1) → ℂ) {ξ : X → Fin r → ℂ} (hξ : Measurable ξ) :
    MeasM (fun x => C2.nEich k r z (ξ x)) := by
  have hxi : Continuous fun ξ : Fin r → ℂ => C2.xiV k r ξ := by
    refine continuous_pi fun i => ?_
    by_cases h : i.val < r
    · simp only [C2.xiV, h, ↓reduceDIte]
      exact continuous_apply _
    · simp only [C2.xiV, h, ↓reduceDIte]
      exact continuous_const
  have hc : Continuous fun ξ : Fin r → ℂ => (C2.nEich k r z ξ : Matrix _ _ ℂ) := by
    unfold C2.nEich
    have h1 : Continuous fun ξ : Fin r → ℂ => vecMulVec (C2.xiV k r ξ) (star (Hpk k r *ᵥ z)) :=
      hxi.matrix_vecMulVec continuous_const
    have h2 : Continuous fun ξ : Fin r → ℂ => vecMulVec z (star (Hpk k r *ᵥ C2.xiV k r ξ)) :=
      continuous_const.matrix_vecMulVec (continuous_const.matrix_mulVec hxi).star
    have h3 : Continuous fun ξ : Fin r → ℂ => vecMulVec (C2.xiV k r ξ) (star (Hpk k r *ᵥ C2.xiV k r ξ)) :=
      hxi.matrix_vecMulVec (continuous_const.matrix_mulVec hxi).star
    fun_prop
  exact measM_of_cont (f := fun ξ => C2.nEich k r z ξ) hc hξ

theorem measM_submatrix_castSucc {A : X → Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hA : MeasM A) :
    MeasM (fun x => (A x).submatrix Fin.castSucc Fin.castSucc) := by
  rw [measM_iff] at hA ⊢
  intro i j
  exact hA _ _

theorem measM_mX {A : X → Matrix (Fin r) (Fin r) ℂ} (hA : MeasM A) : MeasM (fun x => C2.mX k r (A x)) := by
  have hinv : MeasM fun x => ((A x)ᴴ)⁻¹ := measM_inv (measM_star hA)
  rw [measM_iff] at hA hinv ⊢
  intro i j
  simp only [C2.mX]
  split_ifs
  all_goals first | exact measurable_const | exact hA _ _ | exact hinv _ _

theorem measM_tau (z : Fin (2 * r + k + 1) → ℂ) {v : X → Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hv : MeasM v) :
    MeasM (fun x => C2.tauM k r z (v x)) := by
  show MeasM fun x => C2.nEich k r z (fun a => v x a.castSucc (Fin.last r)) *
    C2.mX k r ((v x).submatrix Fin.castSucc Fin.castSucc)
  refine measM_mul (measM_nEich z ?_) (measM_mX (measM_submatrix_castSucc hv))
  exact measurable_pi_lambda _ fun a => (measM_iff.1 hv) _ _

end

end Formalism.FourierDecayAlt.P.StabilizerDisintegration.MM
