import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.FourierCoeffUnitCubeTranslateOfEntirePeriodic

open Matrix MeasureTheory Complex
open scoped Real

noncomputable section

namespace GlobalTheory.TauPeriod

def ex {g : ℕ} (n : Fin g → ℤ) (z : Fin g → ℂ) : ℂ :=
  cexp (2 * π * I * ∑ i, (n i : ℂ) * z i)

def cf {g : ℕ} (f : (Fin g → ℂ) → ℂ) (n : Fin g → ℤ) : ℂ :=
  ∫ x in Set.Icc (0 : Fin g → ℝ) 1,
    f (fun i => (x i : ℂ)) * cexp (-(2 * π * I) * ∑ i, (n i : ℂ) * (x i : ℂ))

def l1 {g : ℕ} (n : Fin g → ℤ) : ℝ := ∑ i, |(n i : ℝ)|

theorem weightAbsEntrySum_nonneg {g : ℕ} (n : Fin g → ℤ) : 0 ≤ l1 n :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem ex_add {g : ℕ} (n : Fin g → ℤ) (z w : Fin g → ℂ) : ex n (z + w) = ex n z * ex n w := by
  simp only [ex, ← Complex.exp_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem ex_zero {g : ℕ} (z : Fin g → ℂ) : ex 0 z = 1 := by
  simp [ex]

theorem differentiable_ex {g : ℕ} (n : Fin g → ℤ) : Differentiable ℂ (ex n) := by
  unfold ex
  fun_prop

theorem ex_add_single {g : ℕ} (n : Fin g → ℤ) (z : Fin g → ℂ) (j : Fin g) :
    ex n (z + Pi.single j 1) = ex n z := by
  rw [ex_add]
  have : ex n (Pi.single j 1) = 1 := by
    have e : ∑ i, (n i : ℂ) * (Pi.single j (1 : ℂ) : Fin g → ℂ) i = (n j : ℂ) := by
      simp [Pi.single_apply]
    rw [ex, e, show 2 * π * I * (n j : ℂ) = (n j : ℂ) * (2 * π * I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I (n j)
  rw [this, mul_one]

theorem norm_ex {g : ℕ} (n : Fin g → ℤ) (z : Fin g → ℂ) :
    ‖ex n z‖ = Real.exp (-(2 * π) * ∑ i, (n i : ℝ) * (z i).im) := by
  rw [ex, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Finset.mul_sum, Complex.re_sum]

theorem cf_translate {g : ℕ} (f : (Fin g → ℂ) → ℂ) (hf : Differentiable ℂ f)
    (hper : ∀ (i : Fin g) z, f (z + Pi.single i 1) = f z) (n : Fin g → ℤ) (w : Fin g → ℂ) :
    cf (fun z => f (z + w)) n = ex n w * cf f n :=
  GlobalTheory.fourierCoeff_unitCube_translate_of_entire_periodic g f hf hper n w

theorem summable_exp_neg_l1Norm {g : ℕ} {c : ℝ} (hc : 0 < c) :
    Summable fun n : Fin g → ℤ => Real.exp (-c * l1 n) := by
  classical
  have h0 : Summable fun n : ℕ => Real.exp (-c * n) := by
    have := summable_geometric_of_lt_one (Real.exp_pos (-c)).le
      (Real.exp_lt_one_iff.2 (by linarith))
    refine this.congr fun n => ?_
    rw [← Real.exp_nat_mul]; congr 1; ring
  have h1 : Summable fun n : ℤ => Real.exp (-c * |(n : ℝ)|) :=
    Summable.of_nat_of_neg (by simpa using h0) (by simpa using h0)
  refine summable_of_sum_le (c := ∏ _i : Fin g, ∑' n : ℤ, Real.exp (-c * |(n : ℝ)|))
    (fun _ => (Real.exp_pos _).le) fun S => ?_
  calc ∑ m ∈ S, Real.exp (-c * l1 m)
      ≤ ∑ m ∈ Fintype.piFinset (fun i => S.image fun m : Fin g → ℤ => m i),
          Real.exp (-c * l1 m) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun m hm => Fintype.mem_piFinset.2 fun i => Finset.mem_image_of_mem _ hm)
          fun _ _ _ => (Real.exp_pos _).le
    _ = ∏ i, ∑ n ∈ S.image (fun m : Fin g → ℤ => m i), Real.exp (-c * |((n : ℤ) : ℝ)|) := by
        rw [Finset.prod_univ_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [← Real.exp_sum, l1, Finset.mul_sum]
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)
        fun _ _ => h1.sum_le_tsum _ fun _ _ => (Real.exp_pos _).le

end GlobalTheory.TauPeriod
