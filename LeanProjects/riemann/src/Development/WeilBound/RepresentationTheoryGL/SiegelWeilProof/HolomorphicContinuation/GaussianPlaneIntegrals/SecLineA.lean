import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.AssemblyAlt
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.OneAddPowMulExpLe

noncomputable section

open MeasureTheory MvPolynomial Filter Topology

namespace PositivityTheory.Rg.Sw.FFTSteps.SecondLineEstimates

variable {m n : ℕ}

instance instHaarMat : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure :=
  MeasureTheory.Measure.pi.isAddHaarMeasure _

def sq (x : Fin m → Fin n → ℂ) : ℝ := ∑ a, ∑ i, ‖x a i‖ ^ 2

lemma sq_nonneg' (x : Fin m → Fin n → ℂ) : 0 ≤ sq x := by
  unfold sq; positivity

lemma continuous_sq : Continuous (sq : (Fin m → Fin n → ℂ) → ℝ) := by
  unfold sq
  exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp (continuous_apply a)).norm.pow 2

lemma col_sq_le (x : Fin m → Fin n → ℂ) (i : Fin n) : ∑ a, ‖x a i‖ ^ 2 ≤ sq x := by
  unfold sq
  exact Finset.sum_le_sum fun a _ =>
    Finset.single_le_sum (f := fun j => ‖x a j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)

lemma coord_sq_le (x : Fin m → Fin n → ℂ) (a : Fin m) (i : Fin n) : ‖x a i‖ ^ 2 ≤ sq x :=
  (Finset.single_le_sum (f := fun b => ‖x b i‖ ^ 2) (fun b _ => by positivity) (Finset.mem_univ a)).trans
    (col_sq_le x i)

lemma coord_le (x : Fin m → Fin n → ℂ) (a : Fin m) (i : Fin n) : ‖x a i‖ ≤ 1 + sq x := by
  have h := coord_sq_le x a i
  nlinarith [sq_nonneg (‖x a i‖ - 1), norm_nonneg (x a i)]

lemma norm_sq_le (x : Fin m → Fin n → ℂ) : ‖x‖ ^ 2 ≤ sq x := by
  have h : ‖x‖ ≤ Real.sqrt (sq x) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun a =>
      (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    have := Real.abs_le_sqrt (coord_sq_le x a i)
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  calc ‖x‖ ^ 2 ≤ (Real.sqrt (sq x)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = sq x := Real.sq_sqrt (sq_nonneg' x)

lemma pow_mul_exp_le (K : ℕ) {β : ℝ} (hβ : 0 < β) :
    ∃ M : ℝ, ∀ s : ℝ, 0 ≤ s → (1 + s) ^ K * Real.exp (-β * s) ≤ M :=
  _root_.UpperTheory.Reformulated.B.P6.r22b.PositivityTheory.Rg.Sw.FFTSteps.SecondLineEstimates.pow_mul_exp_le K hβ

lemma integrable_poly_gauss (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    Integrable (fun x : Fin m → Fin n → ℂ => (1 + sq x) ^ N * Real.exp (-β * sq x)) := by
  set L : ℕ := Module.finrank ℝ (Fin m → Fin n → ℂ) + 1 with hL
  obtain ⟨M, hM⟩ := pow_mul_exp_le (N + L) hβ
  have hint : Integrable (fun x : Fin m → Fin n → ℂ => (1 + ‖x‖) ^ (-((2 * L : ℕ) : ℝ))) :=
    integrable_one_add_norm (by rw [hL]; push_cast; linarith)
  refine (hint.const_mul (2 ^ L * M)).mono' ?_ ?_
  · exact (((continuous_const.add continuous_sq).pow N).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_sq))).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    have hs := sq_nonneg' x
    have hb : 0 < (1 + ‖x‖) ^ (2 * L) := by positivity
    rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg (by positivity), Real.rpow_natCast]
    have hx2 : (1 + ‖x‖) ^ 2 ≤ 2 * (1 + sq x) := by
      nlinarith [norm_sq_le x, sq_nonneg (‖x‖ - 1)]
    have hxL : (1 + ‖x‖) ^ (2 * L) ≤ 2 ^ L * (1 + sq x) ^ L := by
      calc (1 + ‖x‖) ^ (2 * L) = ((1 + ‖x‖) ^ 2) ^ L := by rw [pow_mul]
        _ ≤ (2 * (1 + sq x)) ^ L := pow_le_pow_left₀ (by positivity) hx2 L
        _ = 2 ^ L * (1 + sq x) ^ L := mul_pow _ _ _
    have key : (1 + sq x) ^ N * Real.exp (-β * sq x) * (1 + ‖x‖) ^ (2 * L) ≤ 2 ^ L * M := by
      calc (1 + sq x) ^ N * Real.exp (-β * sq x) * (1 + ‖x‖) ^ (2 * L)
          ≤ (1 + sq x) ^ N * Real.exp (-β * sq x) * (2 ^ L * (1 + sq x) ^ L) :=
            mul_le_mul_of_nonneg_left hxL (by positivity)
        _ = 2 ^ L * ((1 + sq x) ^ (N + L) * Real.exp (-β * sq x)) := by ring
        _ ≤ 2 ^ L * M := mul_le_mul_of_nonneg_left (hM _ hs) (by positivity)
    rw [le_mul_inv_iff₀ hb]
    exact key

end PositivityTheory.Rg.Sw.FFTSteps.SecondLineEstimates
