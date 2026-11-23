import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.MinVec

theorem tpow_mul' {ι : Type} [Fintype ι] (d : ℕ) (x y : Matrix ι ι ℂ) :
    tpow d (x * y) = tpow d x * tpow d y := by
  classical
  ext a b
  simp only [tpow, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ, Finset.prod_mul_distrib]

theorem tpow_one' {ι : Type} [Fintype ι] [DecidableEq ι] (d : ℕ) :
    tpow d (1 : Matrix ι ι ℂ) = 1 := by
  ext a b
  simp only [tpow, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.prod_ite_zero]
  simp [funext_iff]

theorem act_mul' {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ} (d : Fin m → ℕ) (v : TIdx ι d → ℂ)
    (x y : Matrix ι ι ℂ) : act d (act d v x) y = act d v (x * y) := by
  funext k
  simp only [act]
  rw [tpow_mul', ← Matrix.vecMul_vecMul]

theorem act_one' {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ} (d : Fin m → ℕ) (v : TIdx ι d → ℂ) :
    act d v 1 = v := by
  funext k
  simp only [act]
  rw [tpow_one', Matrix.vecMul_one]

theorem norm_sq_le_nsq {κ : Type} [Fintype κ] (v : κ → ℂ) (k : κ) : ‖v k‖ ^ 2 ≤ nsq v :=
  Finset.single_le_sum (f := fun k => ‖v k‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ k)

theorem continuous_nsq {κ : Type} [Fintype κ] : Continuous (nsq : (κ → ℂ) → ℝ) := by
  unfold nsq
  fun_prop

theorem exists_isMinVec_of_isClosed (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ)
    (v : TIdx ι d → ℂ) (hc : IsClosed (orb d v)) : ∃ w ∈ orb d v, IsMinVec d w := by
  have hv : v ∈ orb d v := ⟨1, det_one, (act_one' d v).symm⟩
  set K : Set (TIdx ι d → ℂ) := orb d v ∩ {w | nsq w ≤ nsq v} with hK
  have hKc : IsClosed K := hc.inter (isClosed_le continuous_nsq continuous_const)
  have hKb : Bornology.IsBounded K := by
    refine (Metric.isBounded_closedBall (x := (0 : TIdx ι d → ℂ)) (r := Real.sqrt (nsq v))).subset ?_
    intro w hw
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro k
    exact Real.le_sqrt_of_sq_le ((norm_sq_le_nsq w k).trans hw.2)
  have hcomp : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKc hKb
  obtain ⟨w, hwK, hmin⟩ := hcomp.exists_isMinOn ⟨v, hv, le_refl (nsq v)⟩ continuous_nsq.continuousOn
  refine ⟨w, hwK.1, ?_⟩
  rintro u ⟨y, hy, rfl⟩
  obtain ⟨x, hx, hwx⟩ := hwK.1
  have hu : act d w y ∈ orb d v := ⟨x * y, by rw [det_mul, hx, hy, one_mul], by rw [hwx, act_mul']⟩
  by_cases h : nsq (act d w y) ≤ nsq v
  · exact hmin (show act d w y ∈ K from ⟨hu, h⟩)
  · exact le_trans hwK.2 (le_of_lt (not_le.mp h))

end GlobalTheory.ClassFin.MinVec
