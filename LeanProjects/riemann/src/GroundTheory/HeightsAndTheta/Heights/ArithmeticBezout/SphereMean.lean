import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SphereMeanSlice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Measure Set Real

noncomputable section

namespace SphereMean

theorem setAverage_log_fst_sub (m : ℕ) :
    ⨍ y in ballSet (m + 1) 1, (log ‖y 0‖ - log (sqNorm y) / 2) = -(harmonic m : ℝ) / 2 := by
  obtain ⟨h1i, h1⟩ := integral_ballSet_neg_log_fst m
  obtain ⟨h2i, h2⟩ := integral_ballSet_neg_log_sqNorm m
  have hV : 0 < volume.real (ballSet (m + 1) 1) :=
    ENNReal.toReal_pos (volume_ballSet_one_pos _).ne' (volume_ballSet_one_ne_top _)
  have hfun : (fun y : Fin (m + 1) → ℂ => log ‖y 0‖ - log (sqNorm y) / 2) =
      fun y => (-log (sqNorm y)) / 2 - (-log ‖y 0‖) := by
    funext y
    ring
  rw [setAverage_eq, hfun, integral_sub (h2i.div_const 2) h1i, integral_div, h1, h2,
    harmonic_succ]
  push_cast
  rw [smul_eq_mul]
  field_simp
  ring

theorem volume_fst_eq_zero (m : ℕ) : volume {y : Fin (m + 1) → ℂ | y 0 = 0} = 0 := by
  let K : Submodule ℝ (Fin (m + 1) → ℂ) :=
    LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (m + 1) => ℂ) 0)
  have hK : (K : Set (Fin (m + 1) → ℂ)) = {y | y 0 = 0} := by
    ext y
    simp only [K, SetLike.mem_coe, LinearMap.mem_ker, LinearMap.proj_apply, mem_ofPred_eq]
  have hne : K ≠ ⊤ := by
    intro h
    have : (Pi.single 0 1 : Fin (m + 1) → ℂ) ∈ K := h ▸ Submodule.mem_top
    simp only [K, LinearMap.mem_ker, LinearMap.proj_apply, Pi.single_eq_same] at this
    exact one_ne_zero this
  rw [← hK]
  exact addHaar_submodule _ _ hne

theorem setAverage_log_fst_normalized (m : ℕ) :
    ⨍ y in ballSet (m + 1) 1, log ‖((√(sqNorm y) : ℝ) : ℂ)⁻¹ * y 0‖ = -(harmonic m : ℝ) / 2 := by
  rw [← setAverage_log_fst_sub m]
  apply average_congr
  refine ae_restrict_of_ae ?_
  have h0 := measure_eq_zero_iff_ae_notMem.mp (volume_fst_eq_zero m)
  filter_upwards [h0] with y hy
  have hy' : y 0 ≠ 0 := fun h => hy h
  have hs : 0 < sqNorm y := sqNorm_pos_of_ne_zero (fun h => hy' (by simp [h]))
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    log_mul (inv_ne_zero (Real.sqrt_pos.mpr hs).ne') (norm_ne_zero_iff.mpr hy'), log_inv,
    log_sqrt hs.le]
  ring

theorem std_norm_eq (n : ℕ) (v : Fin n → ℂ) : (HermNorm.std n).norm v = √(sqNorm v) := by
  simp [HermNorm.norm, HermNorm.std, sqNorm]

end SphereMean

open SphereMean in

theorem sphereMeanLinear : SphereMeanLinear.Statement := by
  intro n p hp
  cases n with
  | zero => simp at hp
  | succ m =>

  let e := (Equiv.uniqueProd (Fin (m + 1)) (Fin 1)).symm
  let L1 : (Fin 1 × Fin (m + 1) → ℂ) ≃L[ℝ] (Fin (m + 1) → ℂ) :=
    (LinearEquiv.funCongrLeft ℝ ℂ e).toContinuousLinearEquiv
  have hL1 : ∀ u j, L1 u j = u (0, j) := by
    intro u j
    simp [L1, e]
  let G1 : (Fin (m + 1) → ℂ) → ℝ := fun v =>
    log ‖∑ j, (((√(sqNorm v) : ℝ) : ℂ)⁻¹ * v j) * star (p j)‖
  have hS : {u : Fin 1 × Fin (m + 1) → ℂ |
      ∀ i, (HermNorm.std (m + 1)).norm (fun j => u (i, j)) < 1} = L1 ⁻¹' ballSet (m + 1) 1 := by
    ext u
    simp only [mem_ofPred_eq, mem_preimage, ballSet, std_norm_eq, Fin.forall_fin_one]
    have : (fun j => u (0, j)) = L1 u := funext fun j => (hL1 u j).symm
    rw [this, Real.sqrt_lt' one_pos, one_pow]
  have hstep1 : sphereMean (HermNorm.std (m + 1)) 1
      (fun z => Real.log ‖∑ j, z (0, j) * star (p j)‖) = ⨍ u in L1 ⁻¹' ballSet (m + 1) 1, G1 (L1 u) := by
    unfold sphereMean
    rw [hS]
    congr 1
    funext u
    have : (fun j => u (0, j)) = L1 u := funext fun j => (hL1 u j).symm
    simp only [G1, std_norm_eq, this, hL1]
  rw [hstep1, setAverage_comp_linearEquiv volume volume L1 (ballSet (m + 1) 1) G1]

  let p' : EuclideanSpace ℂ (Fin (m + 1)) := WithLp.toLp 2 p
  have hp' : ‖p'‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp [p', hp]
  have hon : Orthonormal ℂ (({0} : Set (Fin (m + 1))).domRestrict fun _ => p') := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [Subsingleton.elim i j, if_pos rfl,
      show (({0} : Set (Fin (m + 1))).domRestrict fun _ => p') j = p' from rfl,
      inner_self_eq_norm_sq_to_K, hp']
    simp
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
  have hb0 : b 0 = p' := hb 0 (mem_singleton 0)
  let Ulin : (Fin (m + 1) → ℂ) ≃ₗ[ℂ] (Fin (m + 1) → ℂ) :=
    (WithLp.linearEquiv 2 ℂ (Fin (m + 1) → ℂ)).symm ≪≫ₗ b.repr.toLinearEquiv ≪≫ₗ
      WithLp.linearEquiv 2 ℂ (Fin (m + 1) → ℂ)
  let U : (Fin (m + 1) → ℂ) ≃L[ℝ] (Fin (m + 1) → ℂ) :=
    (Ulin.restrictScalars ℝ).toContinuousLinearEquiv
  have hUapp : ∀ v, U v = (b.repr (WithLp.toLp 2 v)).ofLp := fun v => rfl
  have hU0 : ∀ v, U v 0 = ∑ j, v j * star (p j) := by
    intro v
    rw [hUapp, OrthonormalBasis.repr_apply_apply, hb0, PiLp.inner_apply]
    simp [p', RCLike.inner_apply]
  have hUn : ∀ v, sqNorm (U v) = sqNorm v := by
    intro v
    have h := b.repr.norm_map (WithLp.toLp 2 v)
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq] at h
    have h2 := congrArg (· ^ 2) h
    simp only [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h2
    simpa [sqNorm, hUapp] using h2
  let G2 : (Fin (m + 1) → ℂ) → ℝ := fun w => log ‖((√(sqNorm w) : ℝ) : ℂ)⁻¹ * w 0‖
  have hG : ∀ v, G1 v = G2 (U v) := by
    intro v
    simp only [G1, G2, hUn, hU0, Finset.mul_sum, mul_assoc]
  have hB : ballSet (m + 1) 1 = U ⁻¹' ballSet (m + 1) 1 := by
    ext v
    simp [ballSet, hUn]
  have hstep2 : ⨍ v in ballSet (m + 1) 1, G1 v = ⨍ v in U ⁻¹' ballSet (m + 1) 1, G2 (U v) := by
    rw [← hB]
    congr 1
    funext v
    exact hG v
  rw [hstep2, setAverage_comp_linearEquiv volume volume U (ballSet (m + 1) 1) G2]
  simp only [G2]
  rw [setAverage_log_fst_normalized m]
  simp

end

end GroundTheory.Heights₂.Heights
