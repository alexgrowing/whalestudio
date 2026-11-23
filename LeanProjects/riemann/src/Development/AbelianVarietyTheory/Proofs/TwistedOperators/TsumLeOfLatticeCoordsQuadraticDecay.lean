import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerAlong
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped ENNReal

namespace GlobalTheory.TwBoundFour

def wt (N : ℕ) (c : ℤ) : ℝ≥0∞ := ENNReal.ofReal (1 / (1 + ((c : ℝ) / N) ^ 2))

lemma real_bound (N : ℕ) (hN : 0 < N) (y : ℝ) (hy : 0 < y) :
    1 / (1 + (y / N) ^ 2) ≤ (N:ℝ)^2 * (1 / y^2) := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  rw [div_pow, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  field_simp
  nlinarith [sq_nonneg y, sq_nonneg (N:ℝ)]

lemma half_sum_le (N : ℕ) (hN : 0 < N) :
    ∑' m : ℕ, ENNReal.ofReal (1 / (1 + (((m:ℝ) + 1) / N) ^ 2)) ≤ ENNReal.ofReal (2 * (N:ℝ)^2) := by
  have hz : HasSum (fun m : ℕ => (1:ℝ) / ((m:ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have h := (hasSum_nat_add_iff' (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr hasSum_zeta_two
    simpa using h
  have hz2 : HasSum (fun m : ℕ => (N:ℝ)^2 * (1 / ((m:ℝ) + 1) ^ 2)) ((N:ℝ)^2 * (Real.pi ^ 2 / 6)) :=
    hz.mul_left _
  calc ∑' m : ℕ, ENNReal.ofReal (1 / (1 + (((m:ℝ) + 1) / N) ^ 2))
      ≤ ∑' m : ℕ, ENNReal.ofReal ((N:ℝ)^2 * (1 / ((m:ℝ) + 1) ^ 2)) :=
        ENNReal.tsum_le_tsum fun m => ENNReal.ofReal_le_ofReal (real_bound N hN _ (by positivity))
    _ = ENNReal.ofReal ((N:ℝ)^2 * (Real.pi ^ 2 / 6)) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hz2.summable, hz2.tsum_eq]
    _ ≤ ENNReal.ofReal (2 * (N:ℝ)^2) := by
        apply ENNReal.ofReal_le_ofReal
        have hp := Real.pi_lt_d2
        have hp0 := Real.pi_pos
        have : Real.pi ^ 2 / 6 ≤ 2 := by nlinarith
        nlinarith [sq_nonneg (N:ℝ)]

lemma int_sum_le (N : ℕ) (hN : 0 < N) :
    ∑' c : ℤ, wt N c ≤ ENNReal.ofReal (5 * (N:ℝ)^2) := by
  rw [tsum_of_add_one_of_neg_add_one ENNReal.summable ENNReal.summable]
  have h1 : ∑' m : ℕ, wt N ((m:ℤ) + 1) ≤ ENNReal.ofReal (2 * (N:ℝ)^2) := by
    refine le_trans (le_of_eq ?_) (half_sum_le N hN)
    congr 1; funext m; simp [wt]
  have h2 : ∑' m : ℕ, wt N (-((m:ℤ) + 1)) ≤ ENNReal.ofReal (2 * (N:ℝ)^2) := by
    refine le_trans (le_of_eq ?_) (half_sum_le N hN)
    congr 1; funext m; unfold wt; congr 1; push_cast; ring
  have h0 : wt N 0 = 1 := by simp [wt]
  have hN1 : (1:ℝ) ≤ (N:ℝ)^2 := by
    have : (1:ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  calc _ ≤ ENNReal.ofReal (2 * (N:ℝ)^2) + 1 + ENNReal.ofReal (2 * (N:ℝ)^2) := by
        rw [h0]; gcongr
    _ = ENNReal.ofReal (2 * (N:ℝ)^2 + 1 + 2 * (N:ℝ)^2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_one]
    _ ≤ ENNReal.ofReal (5 * (N:ℝ)^2) := ENNReal.ofReal_le_ofReal (by linarith)

lemma pi_sum_le (n : ℕ) (f : ℤ → ℝ≥0∞) :
    ∑' c : Fin n → ℤ, ∏ j, f (c j) ≤ (∑' z, f z) ^ n := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  let t : Fin n → Finset ℤ := fun j => s.image (fun x => x j)
  have hs : s ⊆ Fintype.piFinset t := by
    intro x hx
    rw [Fintype.mem_piFinset]
    intro j
    exact Finset.mem_image_of_mem _ hx
  calc ∑ c ∈ s, ∏ j, f (c j) ≤ ∑ c ∈ Fintype.piFinset t, ∏ j, f (c j) :=
        Finset.sum_le_sum_of_subset hs
    _ = ∏ j, ∑ z ∈ t j, f z := (Finset.prod_univ_sum t (fun _ z => f z)).symm
    _ ≤ ∏ _j : Fin n, ∑' z, f z := Finset.prod_le_prod' fun j _ => ENNReal.sum_le_tsum _
    _ = (∑' z, f z) ^ n := by simp

theorem tsum_le {Y : Type} (n N : ℕ) (hN : 0 < N) (a : Y → ENNReal) (T : Fin n → Y → ℝ)
    (hinj : ∀ y y', a y ≠ 0 → a y' ≠ 0 → (∀ j, T j y = T j y') → y = y')
    (hint : ∀ y, a y ≠ 0 → ∀ j, ∃ c : ℤ, (N : ℝ) * T j y = c) (S : ENNReal)
    (hS : ∀ y, a y * ∏ j, ENNReal.ofReal (1 + T j y ^ 2) ≤ S) :
    ∑' y, a y ≤ S * ENNReal.ofReal ((5 * (N : ℝ) ^ 2) ^ n) := by
  classical
  have hN' : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  let cf : Function.support a → Fin n → ℤ := fun y j => Classical.choose (hint y.1 y.2 j)
  have hcf : ∀ (y : Function.support a) j, (N : ℝ) * T j y.1 = cf y j :=
    fun y j => Classical.choose_spec (hint y.1 y.2 j)
  have hT : ∀ (y : Function.support a) j, T j y.1 = (cf y j : ℝ) / N := fun y j => by
    rw [eq_div_iff hN', mul_comm]; exact hcf y j
  have hcinj : Function.Injective cf := by
    intro y y' h
    apply Subtype.ext
    apply hinj y.1 y'.1 y.2 y'.2
    intro j
    rw [hT y j, hT y' j, h]
  have hbound : ∀ y : Function.support a, a y.1 ≤ S * ∏ j, wt N (cf y j) := by
    intro y
    have hP : (∏ j, ENNReal.ofReal (1 + T j y.1 ^ 2)) * ∏ j, wt N (cf y j) = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun j _ => ?_
      have hpos : (0:ℝ) < 1 + T j y.1 ^ 2 := by positivity
      rw [wt, ← hT y j, ← ENNReal.ofReal_mul hpos.le, mul_one_div_cancel hpos.ne', ENNReal.ofReal_one]
    calc a y.1 = a y.1 * ((∏ j, ENNReal.ofReal (1 + T j y.1 ^ 2)) * ∏ j, wt N (cf y j)) := by
          rw [hP, mul_one]
      _ = (a y.1 * ∏ j, ENNReal.ofReal (1 + T j y.1 ^ 2)) * ∏ j, wt N (cf y j) := by
          rw [mul_assoc]
      _ ≤ S * ∏ j, wt N (cf y j) := by gcongr; exact hS y.1
  rw [← tsum_subtype_support]
  calc ∑' y : Function.support a, a y.1 ≤ ∑' y : Function.support a, S * ∏ j, wt N (cf y j) :=
        ENNReal.tsum_le_tsum hbound
    _ = S * ∑' y : Function.support a, ∏ j, wt N (cf y j) := ENNReal.tsum_mul_left
    _ ≤ S * ∑' c : Fin n → ℤ, ∏ j, wt N (c j) := by
        gcongr
        exact ENNReal.tsum_comp_le_tsum_of_injective hcinj (fun c => ∏ j, wt N (c j))
    _ ≤ S * (∑' z, wt N z) ^ n := by gcongr; exact pi_sum_le n (wt N)
    _ ≤ S * ENNReal.ofReal (5 * (N:ℝ)^2) ^ n := by gcongr; exact int_sum_le N hN
    _ = S * ENNReal.ofReal ((5 * (N : ℝ) ^ 2) ^ n) := by
        rw [ENNReal.ofReal_pow (by positivity)]

end GlobalTheory.TwBoundFour
