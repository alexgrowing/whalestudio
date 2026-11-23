import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.FlowGS

def tri (E : ℕ → ℝ) (Y : ℕ → ℂ) (τ : ℝ) (ρ : ℕ → ℝ) (a j : ℕ) : ℂ :=
  if j < a then 0 else if j = a then (ρ (a + 1) : ℂ) / ρ a
  else (τ : ℂ) * Y a * E j * star (Y j) / ((ρ a : ℂ) * ρ (a + 1))

private theorem tri_eq_zero_of_gt (E : ℕ → ℝ) (Y : ℕ → ℂ) (τ : ℝ) (ρ : ℕ → ℝ) {a j : ℕ} (h : j < a) :
    tri E Y τ ρ a j = 0 := by
  unfold tri; rw [if_pos h]

private theorem tri_self (E : ℕ → ℝ) (Y : ℕ → ℂ) (τ : ℝ) (ρ : ℕ → ℝ) (a : ℕ) :
    tri E Y τ ρ a a = (ρ (a + 1) : ℂ) / ρ a := by
  unfold tri; rw [if_neg (lt_irrefl a), if_pos rfl]

private theorem tri_of_lt (E : ℕ → ℝ) (Y : ℕ → ℂ) (τ : ℝ) (ρ : ℕ → ℝ) {a j : ℕ} (h : a < j) :
    tri E Y τ ρ a j = (τ : ℂ) * Y a * E j * star (Y j) / ((ρ a : ℂ) * ρ (a + 1)) := by
  unfold tri; rw [if_neg (show ¬ j < a by omega), if_neg (show ¬ j = a by omega)]

theorem tri_gram (E : ℕ → ℝ) (Y : ℕ → ℂ) (τ : ℝ) (ρ : ℕ → ℝ) (hE : ∀ a, E a * E a = 1) (hρ : ∀ a, ρ a ≠ 0)
    (h0 : ρ 0 = 1) (hs : ∀ a, (ρ (a + 1) : ℂ) ^ 2 = (ρ a : ℂ) ^ 2 + τ * E a * (Y a * star (Y a))) (i j k : ℕ) :
    ∑ a ∈ Finset.range k, star (tri E Y τ ρ a i) * E a * tri E Y τ ρ a j =
      if k ≤ i ∧ k ≤ j then τ * (E i * Y i) * (E j * star (Y j)) * (1 - 1 / (ρ k : ℂ) ^ 2)
      else (if i = j then (E i : ℂ) else 0) + τ * (E i * Y i) * (E j * star (Y j)) := by
  have hr : ∀ a, (ρ a : ℂ) * (ρ a : ℂ)⁻¹ = 1 := fun a => mul_inv_cancel₀ (by exact_mod_cast hρ a)
  induction k with
  | zero => simp [h0]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have hk := hs k
    have hrk := hr k
    have hrk1 := hr (k + 1)
    rcases lt_trichotomy i k with hi | hi | hi
    · rw [tri_eq_zero_of_gt E Y τ ρ hi, if_neg (show ¬(k ≤ i ∧ k ≤ j) from fun h => by omega),
        if_neg (show ¬(k + 1 ≤ i ∧ k + 1 ≤ j) from fun h => by omega)]
      simp
    · rw [hi]
      rcases lt_trichotomy j k with hj | hj | hj
      · rw [tri_eq_zero_of_gt E Y τ ρ hj, if_neg (show ¬(k ≤ k ∧ k ≤ j) from fun h => by omega),
          if_neg (show ¬(k + 1 ≤ k ∧ k + 1 ≤ j) from fun h => by omega)]
        simp
      · rw [hj, tri_self, if_pos (show k ≤ k ∧ k ≤ k from ⟨le_rfl, le_rfl⟩),
          if_neg (show ¬(k + 1 ≤ k ∧ k + 1 ≤ k) from fun h => by omega), if_pos (rfl : k = k)]
        simp only [Complex.star_def, map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_conj] at hk ⊢
        linear_combination ((E k : ℂ) * ((ρ k : ℂ) * (ρ k : ℂ)⁻¹ + 1)) * hrk + ((ρ k : ℂ)⁻¹ ^ 2 * (E k : ℂ)) * hk
      · rw [tri_self, tri_of_lt E Y τ ρ hj, if_pos (show k ≤ k ∧ k ≤ j from ⟨le_rfl, hj.le⟩),
          if_neg (show ¬(k + 1 ≤ k ∧ k + 1 ≤ j) from fun h => by omega), if_neg (show ¬(k = j) from by omega)]
        simp only [Complex.star_def, map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_conj] at hk ⊢
        linear_combination ((τ : ℂ) * (E k : ℂ) * Y k * (E j : ℂ) * (starRingEnd ℂ) (Y j) * (ρ k : ℂ)⁻¹ ^ 2) * hrk1
    · rcases lt_trichotomy j k with hj | hj | hj
      · rw [tri_eq_zero_of_gt E Y τ ρ hj, if_neg (show ¬(k ≤ i ∧ k ≤ j) from fun h => by omega),
          if_neg (show ¬(k + 1 ≤ i ∧ k + 1 ≤ j) from fun h => by omega)]
        simp
      · rw [hj, tri_self, tri_of_lt E Y τ ρ hi, if_pos (show k ≤ i ∧ k ≤ k from ⟨hi.le, le_rfl⟩),
          if_neg (show ¬(k + 1 ≤ i ∧ k + 1 ≤ k) from fun h => by omega), if_neg (show ¬(i = k) from by omega)]
        simp only [Complex.star_def, map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_conj] at hk ⊢
        linear_combination ((τ : ℂ) * (E i : ℂ) * Y i * (E k : ℂ) * (starRingEnd ℂ) (Y k) * (ρ k : ℂ)⁻¹ ^ 2) * hrk1
      · rw [tri_of_lt E Y τ ρ hi, tri_of_lt E Y τ ρ hj, if_pos (show k ≤ i ∧ k ≤ j from ⟨hi.le, hj.le⟩),
          if_pos (show k + 1 ≤ i ∧ k + 1 ≤ j from ⟨hi, hj⟩)]
        simp only [Complex.star_def, map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_conj] at hk ⊢
        linear_combination ((τ : ℂ) * ((E i : ℂ) * Y i) * ((E j : ℂ) * (starRingEnd ℂ) (Y j))) *
          (-((ρ k : ℂ)⁻¹ ^ 2 * (ρ (k + 1) : ℂ)⁻¹ ^ 2) * hk
            - (ρ (k + 1) : ℂ)⁻¹ ^ 2 * ((ρ k : ℂ) * (ρ k : ℂ)⁻¹ + 1) * hrk
            + (ρ k : ℂ)⁻¹ ^ 2 * ((ρ (k + 1) : ℂ) * (ρ (k + 1) : ℂ)⁻¹ + 1) * hrk1)

theorem tri_vec (E : ℕ → ℝ) (Y : ℕ → ℂ) (τ : ℝ) (ρ : ℕ → ℝ) (hρ : ∀ a, ρ a ≠ 0)
    (hs : ∀ a, (ρ (a + 1) : ℂ) ^ 2 = (ρ a : ℂ) ^ 2 + τ * E a * (Y a * star (Y a))) (a k : ℕ) :
    ∑ j ∈ Finset.range k, tri E Y τ ρ a j * Y j =
      if k ≤ a then 0 else Y a * (ρ k : ℂ) ^ 2 / ((ρ a : ℂ) * ρ (a + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    rcases lt_trichotomy k a with hk | hk | hk
    · rw [tri_eq_zero_of_gt E Y τ ρ hk, if_pos hk.le, if_pos (show k + 1 ≤ a from hk)]
      simp
    · rw [hk, tri_self, if_pos le_rfl, if_neg (show ¬(a + 1 ≤ a) from by omega)]
      have h1 : (ρ (a + 1) : ℂ) * (ρ (a + 1) : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (by exact_mod_cast hρ (a + 1))
      linear_combination (-((ρ (a + 1) : ℂ) * (ρ a : ℂ)⁻¹ * Y a)) * h1
    · rw [tri_of_lt E Y τ ρ hk, if_neg (show ¬(k ≤ a) from by omega), if_neg (show ¬(k + 1 ≤ a) from by omega)]
      linear_combination (-(Y a * (ρ a : ℂ)⁻¹ * (ρ (a + 1) : ℂ)⁻¹)) * hs k

theorem partial_nonneg (q n : ℕ) (g : ℕ → ℝ) (hg : ∀ a, 0 ≤ g a) (hz : ∀ a, n ≤ a → g a = 0)
    (hn : ∑ a ∈ Finset.range n, ReciprocityTheory.ChartRestriction.G.FD.sgn q a * g a = 0) (k : ℕ) :
    0 ≤ ∑ a ∈ Finset.range k, ReciprocityTheory.ChartRestriction.G.FD.sgn q a * g a := by
  by_cases hkq : k ≤ q
  · apply Finset.sum_nonneg
    intro a ha
    have : a < q := by rw [Finset.mem_range] at ha; omega
    simp only [ReciprocityTheory.ChartRestriction.G.FD.sgn, if_pos this, one_mul]
    exact hg a
  · push_neg at hkq
    have hmn : ∑ a ∈ Finset.range (max k n), ReciprocityTheory.ChartRestriction.G.FD.sgn q a * g a = 0 := by
      rw [← Finset.sum_range_add_sum_Ico _ (le_max_right k n), hn, zero_add]
      apply Finset.sum_eq_zero
      intro a ha
      rw [hz a (Finset.mem_Ico.mp ha).1, mul_zero]
    rw [← Finset.sum_range_add_sum_Ico _ (le_max_left k n)] at hmn
    have hneg : ∑ a ∈ Finset.Ico k (max k n), ReciprocityTheory.ChartRestriction.G.FD.sgn q a * g a =
        -∑ a ∈ Finset.Ico k (max k n), g a := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      have : ¬ a < q := by have := (Finset.mem_Ico.mp ha).1; omega
      simp only [ReciprocityTheory.ChartRestriction.G.FD.sgn, if_neg this]
      ring
    rw [hneg] at hmn
    have : 0 ≤ ∑ a ∈ Finset.Ico k (max k n), g a := Finset.sum_nonneg fun a _ => hg a
    linarith

theorem partial_le (q n : ℕ) (g : ℕ → ℝ) (hg : ∀ a, 0 ≤ g a) (hz : ∀ a, n ≤ a → g a = 0) (k : ℕ) :
    ∑ a ∈ Finset.range k, ReciprocityTheory.ChartRestriction.G.FD.sgn q a * g a ≤ ∑ a ∈ Finset.range n, g a := by
  calc ∑ a ∈ Finset.range k, ReciprocityTheory.ChartRestriction.G.FD.sgn q a * g a ≤ ∑ a ∈ Finset.range k, g a := by
        apply Finset.sum_le_sum
        intro a _
        have h1 : ReciprocityTheory.ChartRestriction.G.FD.sgn q a ≤ 1 := by
          unfold ReciprocityTheory.ChartRestriction.G.FD.sgn; split_ifs <;> norm_num
        nlinarith [hg a]
    _ ≤ ∑ a ∈ Finset.range (max k n), g a :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (le_max_left k n)) (fun a _ _ => hg a)
    _ = ∑ a ∈ Finset.range n, g a := by
        rw [← Finset.sum_range_add_sum_Ico _ (le_max_right k n)]
        rw [Finset.sum_eq_zero (s := Finset.Ico n (max k n)), add_zero]
        intro a ha
        exact hz a (Finset.mem_Ico.mp ha).1

def sgnM (n q : ℕ) : Mt n := diagonal fun a : Fin n => ((ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ)

theorem core (n q : ℕ) (y : Fin n → ℂ) (hy : star y ⬝ᵥ (sgnM n q).mulVec y = 0) (t : ℝ) (ht : 0 ≤ t) :
    ∃ b : Mt n, UpT b ∧
      bᴴ * sgnM n q * b = sgnM n q + ((2 * t : ℝ) : ℂ) • vecMulVec ((sgnM n q).mulVec y) (star y ᵥ* sgnM n q) ∧
      (∀ a, ‖b a a‖ ≤ (1 + 2 * ∑ c, ‖y c‖ ^ 2) * (1 + t) ∧ ‖b a a‖⁻¹ ≤ (1 + 2 * ∑ c, ‖y c‖ ^ 2) * (1 + t)) ∧
      ∀ a, ‖(b.mulVec y) a‖ ^ 2 * (1 + t) ≤ ‖y a‖ ^ 2 + 1 := by
  obtain ⟨Y, hYd⟩ : ∃ Y : ℕ → ℂ, ∀ c, Y c = if h : c < n then y ⟨c, h⟩ else 0 := ⟨_, fun _ => rfl⟩
  have hY : ∀ i : Fin n, Y i = y i := fun i => by rw [hYd, dif_pos i.isLt]
  have hYz : ∀ c, n ≤ c → Y c = 0 := fun c hc => by rw [hYd, dif_neg (show ¬ c < n by omega)]
  obtain ⟨g, hgd⟩ : ∃ g : ℕ → ℝ, ∀ c, g c = ‖Y c‖ ^ 2 := ⟨_, fun _ => rfl⟩
  have hgnn : ∀ c, 0 ≤ g c := fun c => by rw [hgd]; positivity
  have hgz : ∀ c, n ≤ c → g c = 0 := fun c hc => by rw [hgd, hYz c hc]; simp
  have hPn : ∑ c ∈ Finset.range n, ReciprocityTheory.ChartRestriction.G.FD.sgn q c * g c = 0 := by
    have h1 : ((∑ c ∈ Finset.range n, ReciprocityTheory.ChartRestriction.G.FD.sgn q c * g c : ℝ) : ℂ) =
        star y ⬝ᵥ (sgnM n q).mulVec y := by
      rw [Finset.sum_range]
      simp only [hgd, hY, dotProduct, sgnM, Matrix.mulVec_diagonal, Pi.star_apply]
      push_cast
      apply Finset.sum_congr rfl
      intro i _
      have := Complex.conj_mul' (y i)
      rw [Complex.star_def]
      linear_combination (-((ReciprocityTheory.ChartRestriction.G.FD.sgn q i : ℝ) : ℂ)) * this
    have h2 := h1.trans hy
    exact_mod_cast h2
  have hPnn : ∀ k, 0 ≤ ∑ c ∈ Finset.range k, ReciprocityTheory.ChartRestriction.G.FD.sgn q c * g c :=
    fun k => partial_nonneg q n g hgnn hgz hPn k
  have hPle : ∀ k, ∑ c ∈ Finset.range k, ReciprocityTheory.ChartRestriction.G.FD.sgn q c * g c ≤ ∑ c ∈ Finset.range n, g c :=
    fun k => partial_le q n g hgnn hgz k
  obtain ⟨ρ, hρd⟩ : ∃ ρ : ℕ → ℝ, ∀ k,
      ρ k = Real.sqrt (1 + 2 * t * ∑ c ∈ Finset.range k, ReciprocityTheory.ChartRestriction.G.FD.sgn q c * g c) := ⟨_, fun _ => rfl⟩
  have hρsq : ∀ k, ρ k ^ 2 = 1 + 2 * t * ∑ c ∈ Finset.range k, ReciprocityTheory.ChartRestriction.G.FD.sgn q c * g c := fun k => by
    rw [hρd, Real.sq_sqrt]; nlinarith [hPnn k, mul_nonneg ht (hPnn k)]
  have hρnn : ∀ k, 0 ≤ ρ k := fun k => by rw [hρd]; exact Real.sqrt_nonneg _
  have hρ1 : ∀ k, 1 ≤ ρ k := fun k => by nlinarith [hρsq k, hρnn k, hPnn k, mul_nonneg ht (hPnn k)]
  have hρ0 : ∀ k, ρ k ≠ 0 := fun k => (lt_of_lt_of_le one_pos (hρ1 k)).ne'
  have h0 : ρ 0 = 1 := by rw [hρd]; simp
  have hE : ∀ a, ReciprocityTheory.ChartRestriction.G.FD.sgn q a * ReciprocityTheory.ChartRestriction.G.FD.sgn q a = 1 := fun a => by
    unfold ReciprocityTheory.ChartRestriction.G.FD.sgn; split_ifs <;> norm_num
  have hs : ∀ a, (ρ (a + 1) : ℂ) ^ 2 = (ρ a : ℂ) ^ 2 +
      ((2 * t : ℝ) : ℂ) * ((ReciprocityTheory.ChartRestriction.G.FD.sgn q a : ℝ) : ℂ) * (Y a * star (Y a)) := by
    intro a
    have hr : ρ (a + 1) ^ 2 = ρ a ^ 2 + 2 * t * ReciprocityTheory.ChartRestriction.G.FD.sgn q a * ‖Y a‖ ^ 2 := by
      rw [hρsq, hρsq, Finset.sum_range_succ, hgd]; ring
    have hc := congrArg (fun x : ℝ => (x : ℂ)) hr
    rw [Complex.star_def, Complex.mul_conj']
    push_cast at hc ⊢
    linear_combination hc
  have hlow : ∀ a c : Fin n, c < a → tri (ReciprocityTheory.ChartRestriction.G.FD.sgn q) Y (2 * t) ρ a c = 0 :=
    fun a c h => tri_eq_zero_of_gt _ _ _ _ (Fin.lt_iff_val_lt_val.mp h)
  refine ⟨Matrix.of fun a j : Fin n => tri (ReciprocityTheory.ChartRestriction.G.FD.sgn q) Y (2 * t) ρ a j, ?_, ?_, ?_, ?_⟩
  · unfold UpT
    refine ⟨?_, fun a c h => by simpa using hlow a c h⟩
    have hUT : (Matrix.of fun a j : Fin n => tri (ReciprocityTheory.ChartRestriction.G.FD.sgn q) Y (2 * t) ρ a j).IsUpperTriangular :=
      fun i j h => by simpa using hlow i j h
    rw [Matrix.det_of_isUpperTriangular hUT, Finset.prod_ne_zero_iff]
    intro a _
    simp only [Matrix.of_apply]
    rw [tri_self]
    exact div_ne_zero (by exact_mod_cast hρ0 _) (by exact_mod_cast hρ0 _)
  · ext i j
    have key := tri_gram (ReciprocityTheory.ChartRestriction.G.FD.sgn q) Y (2 * t) ρ hE hρ0 h0 hs i j n
    rw [if_neg (show ¬ (n ≤ (i : ℕ) ∧ n ≤ (j : ℕ)) from fun h => by have := i.isLt; omega),
      Finset.sum_range] at key
    simp only [hY] at key
    rw [Matrix.mul_apply]
    simp only [sgnM, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.add_apply,
      Matrix.diagonal_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.mulVec_diagonal,
      Matrix.vecMul_diagonal, Pi.star_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      simp only [eq_self_iff_true, if_true] at key ⊢
      linear_combination key
    · have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
      simp only [hij, hij', if_false] at key ⊢
      linear_combination key
  · have hG : ∑ c, ‖y c‖ ^ 2 = ∑ c ∈ Finset.range n, g c := by
      rw [Finset.sum_range]; simp only [hgd, hY]
    have hGnn : 0 ≤ ∑ c ∈ Finset.range n, g c := Finset.sum_nonneg fun c _ => hgnn c
    have hρle : ∀ k, ρ k ≤ 1 + 2 * t * ∑ c ∈ Finset.range n, g c := fun k => by
      nlinarith [hρsq k, hρ1 k, hPle k, mul_le_mul_of_nonneg_left (hPle k) ht]
    have hM : 1 + 2 * t * ∑ c ∈ Finset.range n, g c ≤ (1 + 2 * ∑ c ∈ Finset.range n, g c) * (1 + t) := by
      nlinarith [mul_nonneg ht hGnn]
    intro a
    simp only [Matrix.of_apply]
    rw [tri_self, hG, ← Complex.ofReal_div, Complex.norm_of_nonneg (div_nonneg (hρnn _) (hρnn _)), inv_div]
    constructor
    · calc ρ ((a : ℕ) + 1) / ρ a ≤ ρ ((a : ℕ) + 1) := div_le_self (hρnn _) (hρ1 _)
        _ ≤ _ := (hρle _).trans hM
    · calc ρ a / ρ ((a : ℕ) + 1) ≤ ρ a := div_le_self (hρnn _) (hρ1 _)
        _ ≤ _ := (hρle _).trans hM
  · intro a
    have key := tri_vec (ReciprocityTheory.ChartRestriction.G.FD.sgn q) Y (2 * t) ρ hρ0 hs a n
    rw [if_neg (show ¬ (n ≤ (a : ℕ)) from by have := a.isLt; omega), Finset.sum_range] at key
    simp only [hY] at key
    have hρn : (ρ n : ℂ) ^ 2 = 1 := by
      have : ρ n ^ 2 = 1 := by rw [hρsq, hPn]; ring
      exact_mod_cast this
    rw [hρn, mul_one] at key
    have hv : (Matrix.of fun a j : Fin n => tri (ReciprocityTheory.ChartRestriction.G.FD.sgn q) Y (2 * t) ρ a j).mulVec y a =
        y a / ((ρ a * ρ ((a : ℕ) + 1) : ℝ) : ℂ) := by
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
      rw [key, Complex.ofReal_mul]
    have hsg : ReciprocityTheory.ChartRestriction.G.FD.sgn q a = 1 ∨ ReciprocityTheory.ChartRestriction.G.FD.sgn q a = -1 := by
      unfold ReciprocityTheory.ChartRestriction.G.FD.sgn; split_ifs <;> simp
    have hPs : ∑ c ∈ Finset.range ((a : ℕ) + 1), ReciprocityTheory.ChartRestriction.G.FD.sgn q c * g c =
        ∑ c ∈ Finset.range (a : ℕ), ReciprocityTheory.ChartRestriction.G.FD.sgn q c * g c + ReciprocityTheory.ChartRestriction.G.FD.sgn q a * ‖y a‖ ^ 2 := by
      rw [Finset.sum_range_succ, hgd, hY]
    have hA := hPnn a
    have hB := hPnn ((a : ℕ) + 1)
    have hz : 0 ≤ ‖y a‖ ^ 2 := by positivity
    have hAB : 1 + 2 * t * ‖y a‖ ^ 2 ≤
        (1 + 2 * t * ∑ c ∈ Finset.range (a : ℕ), ReciprocityTheory.ChartRestriction.G.FD.sgn q c * g c) *
          (1 + 2 * t * ∑ c ∈ Finset.range ((a : ℕ) + 1), ReciprocityTheory.ChartRestriction.G.FD.sgn q c * g c) := by
      rw [hPs] at hB ⊢
      rcases hsg with h | h
      · rw [h] at hB ⊢
        nlinarith [mul_nonneg ht hA, mul_nonneg ht hz, sq_nonneg (t * ∑ c ∈ Finset.range (a : ℕ), ReciprocityTheory.ChartRestriction.G.FD.sgn q c * g c),
          mul_nonneg (mul_nonneg ht hA) (mul_nonneg ht hz)]
      · rw [h] at hB ⊢
        nlinarith [mul_nonneg ht hB, mul_nonneg ht hz, mul_nonneg (mul_nonneg ht hB) (mul_nonneg ht hB),
          mul_nonneg (mul_nonneg ht hz) (mul_nonneg ht hB), mul_nonneg ht hA]
    rw [hv, norm_div, Complex.norm_of_nonneg (mul_nonneg (hρnn _) (hρnn _)), div_pow, mul_pow, hρsq, hρsq,
      div_mul_eq_mul_div, div_le_iff₀ (by nlinarith [mul_nonneg ht hA, mul_nonneg ht hB, mul_nonneg (mul_nonneg ht hA) (mul_nonneg ht hB)])]
    nlinarith [hAB, mul_le_mul_of_nonneg_left hAB (by positivity : (0 : ℝ) ≤ ‖y a‖ ^ 2 + 1), mul_nonneg ht hz,
      mul_nonneg (mul_nonneg ht hz) hz]

theorem prod_zpow_le {n : ℕ} (v : Fin n → ℂ) (w : Fin n → ℤ) (M : ℝ) (h : ∀ a, ‖v a‖ ≤ M ∧ ‖v a‖⁻¹ ≤ M) :
    ‖∏ a, v a ^ w a‖ ≤ M ^ (∑ a, (w a).natAbs) := by
  rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod (fun a _ => norm_nonneg _)
  intro a _
  obtain ⟨h1, h2⟩ := h a
  rw [norm_zpow]
  rcases Int.natAbs_eq (w a) with hw | hw
  · conv_lhs => rw [hw]
    rw [zpow_natCast]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 _
  · conv_lhs => rw [hw]
    rw [_root_.zpow_neg, zpow_natCast, ← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) h2 _

private theorem star_mulVec_dotProduct_mulVec_eq_conjTranspose {n : ℕ} (M N : Mt n) (v : Fin n → ℂ) :
    star (M *ᵥ v) ⬝ᵥ (N *ᵥ (M *ᵥ v)) = star v ⬝ᵥ ((Mᴴ * N * M) *ᵥ v) := by
  conv_rhs => rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]

private theorem unit_lemma_5 {n : ℕ} {Hm v : Mt n} (h : vᴴ * Hm * v = Hm) (hH : Hm.det ≠ 0) : IsUnit v.det := by
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul] at h1
  refine isUnit_iff_ne_zero.mpr fun h0 => hH ?_
  rw [← h1, h0, mul_zero]

theorem flowGS : ∀ (n : ℕ) (Hm : Mt n) (q : ℕ) (x₀ : Mt n), OrthFr Hm q x₀ → ∀ (w : Fin n → ℤ) (e : Fin n → ℂ), star e ⬝ᵥ Hm.mulVec e = 0 → ∀ u ∈ Formalism.QuantumDeterminants.UH Hm, ∃ (C : ℝ) (A : ℕ), ∀ t : ℝ, 0 ≤ t → ∃ u' ∈ Formalism.QuantumDeterminants.UH Hm, ∃ b, UpT b ∧ (1 - (t : ℂ) • vecMulVec e (star e ᵥ* Hm)) * u * x₀ = u' * x₀ * b ∧ ‖∏ a, b a a ^ w a‖ ≤ C * (1 + t) ^ A ∧ ∀ i, ‖(u'⁻¹.mulVec e) i‖ ^ 2 * (1 + t) ≤ C := by
  intro n Hm q x₀ hx w e he u hu
  obtain ⟨_, hX⟩ := hx
  have hS : x₀ᴴ * Hm * x₀ = -sgnM n q := by
    rw [hX, sgnM, Matrix.diagonal_neg]
  have hSdet : (sgnM n q).det ≠ 0 := by
    rw [sgnM, Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    intro a _
    show ((ReciprocityTheory.ChartRestriction.G.FD.sgn q a : ℝ) : ℂ) ≠ 0
    unfold ReciprocityTheory.ChartRestriction.G.FD.sgn; split_ifs <;> norm_num
  have hd : (x₀ᴴ * Hm * x₀).det ≠ 0 := by
    rw [hS, Matrix.det_neg]; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hSdet
  rw [Matrix.det_mul, Matrix.det_mul] at hd
  have hxu : IsUnit x₀.det := isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul hd)
  have hHdet : Hm.det ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hd)
  have hxHu : IsUnit x₀ᴴ.det := by
    rw [Matrix.det_conjTranspose]; exact hxu.star
  have hXu : IsUnit x₀ := (Matrix.isUnit_iff_isUnit_det x₀).mpr hxu
  have hXHu : IsUnit x₀ᴴ := (Matrix.isUnit_iff_isUnit_det _).mpr hxHu
  have hSH : (sgnM n q)ᴴ = sgnM n q := by
    rw [sgnM, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    first
    | exact Complex.conj_ofReal _
    | simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
  have hHH : Hmᴴ = Hm := by
    have h1 : x₀ᴴ * Hmᴴ * x₀ = x₀ᴴ * Hm * x₀ := by
      have h2 := congrArg Matrix.conjTranspose hS
      rw [Matrix.conjTranspose_neg, hSH, ← hS] at h2
      rw [← h2]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    exact hXHu.mul_left_cancel (hXu.mul_right_cancel h1)
  have hu' : uᴴ * Hm * u = Hm := hu
  have huu : IsUnit u.det := unit_lemma_5 hu' hHdet
  obtain ⟨f, hf⟩ : ∃ f : Fin n → ℂ, f = u⁻¹ *ᵥ e := ⟨_, rfl⟩
  obtain ⟨y, hyd⟩ : ∃ y : Fin n → ℂ, y = x₀⁻¹ *ᵥ f := ⟨_, rfl⟩
  have huf : u *ᵥ f = e := by rw [hf, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ huu, Matrix.one_mulVec]
  have hxy : x₀ *ᵥ y = f := by rw [hyd, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hxu, Matrix.one_mulVec]
  have hSy : star y ⬝ᵥ (sgnM n q).mulVec y = 0 := by
    have hS' : sgnM n q = -(x₀ᴴ * Hm * x₀) := by rw [hS, neg_neg]
    rw [hS', Matrix.neg_mulVec, dotProduct_neg, ← star_mulVec_dotProduct_mulVec_eq_conjTranspose, hxy, ← hu', ← star_mulVec_dotProduct_mulVec_eq_conjTranspose, huf, he, neg_zero]
  obtain ⟨M, hM⟩ : ∃ M : Mt n, M = u * x₀ := ⟨_, rfl⟩
  have hMM : Mᴴ * (Hm * M) = -sgnM n q := by
    have h0 : x₀ᴴ * (uᴴ * Hm * u) * x₀ = -sgnM n q := by rw [hu', hS]
    rw [hM, ← h0]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hMMl : Mᴴ * Hm * M = -sgnM n q := by rw [Matrix.mul_assoc]; exact hMM
  have hMy : M *ᵥ y = e := by rw [hM, ← Matrix.mulVec_mulVec, hxy, huf]
  have he' : (star e ᵥ* Hm) ⬝ᵥ e = 0 := by rw [← Matrix.dotProduct_mulVec]; exact he
  have hVe : vecMulVec e (star e ᵥ* Hm) *ᵥ e = 0 := by
    rw [Matrix.vecMulVec_mulVec, he', MulOpposite.op_zero, zero_smul]
  have hVH : (vecMulVec e (star e ᵥ* Hm))ᴴ = vecMulVec (Hm *ᵥ e) (star e) := by
    rw [Matrix.conjTranspose_vecMulVec, Matrix.star_vecMul, star_star, hHH]
  have h1 : (vecMulVec e (star e ᵥ* Hm))ᴴ * Hm = vecMulVec (Hm *ᵥ e) (star e ᵥ* Hm) := by
    rw [hVH, Matrix.vecMulVec_mul]
  have h2 : Hm * vecMulVec e (star e ᵥ* Hm) = vecMulVec (Hm *ᵥ e) (star e ᵥ* Hm) := Matrix.mul_vecMulVec _ _ _
  have h3 : (vecMulVec e (star e ᵥ* Hm))ᴴ * (Hm * vecMulVec e (star e ᵥ* Hm)) = 0 := by
    rw [← Matrix.mul_assoc, h1, Matrix.mul_vecMulVec, Matrix.vecMulVec_mulVec, he', MulOpposite.op_zero, zero_smul,
      Matrix.zero_vecMulVec]
  have expand : ∀ (c : ℂ) (P Q : Mt n),
      (1 - c • P) * Hm * (1 - c • Q) = Hm - c • (Hm * Q) - c • (P * Hm) + (c * c) • (P * (Hm * Q)) := by
    intro c P Q
    simp only [sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_smul,
      Matrix.mul_assoc]
    abel
  have ha : Mᴴ *ᵥ (Hm *ᵥ e) = -(sgnM n q *ᵥ y) := by
    rw [← hMy]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [hMM, Matrix.neg_mulVec]
  have hb : star e ᵥ* Hm ᵥ* M = -(star y ᵥ* sgnM n q) := by
    rw [← hMy, Matrix.star_mulVec]
    simp only [Matrix.vecMul_vecMul, Matrix.mul_assoc]
    rw [hMM, Matrix.vecMul_neg]
  have hMW : Mᴴ * vecMulVec (Hm *ᵥ e) (star e ᵥ* Hm) * M = vecMulVec (-(sgnM n q *ᵥ y)) (-(star y ᵥ* sgnM n q)) := by
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ha, hb]
  refine ⟨(1 + 2 * ∑ c, ‖y c‖ ^ 2) ^ (∑ a, (w a).natAbs) + ∑ i, (∑ j, ‖x₀ i j‖ ^ 2) * ∑ j, (‖y j‖ ^ 2 + 1),
    ∑ a, (w a).natAbs, ?_⟩
  intro t ht
  obtain ⟨b, hbU, hbS, hbd, hby⟩ := core n q y hSy t ht
  have hbdet : b.det ≠ 0 := by unfold UpT at hbU; exact hbU.1
  have hbu : IsUnit b.det := isUnit_iff_ne_zero.mpr hbdet
  obtain ⟨Z, hZ⟩ : ∃ Z : Mt n, Z = x₀ * b := ⟨_, rfl⟩
  have hZu : IsUnit Z.det := by rw [hZ, Matrix.det_mul]; exact hxu.mul hbu
  have hZHu : IsUnit Zᴴ.det := by rw [Matrix.det_conjTranspose]; exact hZu.star
  obtain ⟨G, hGd⟩ : ∃ G : Mt n, G = 1 - (t : ℂ) • vecMulVec e (star e ᵥ* Hm) := ⟨_, rfl⟩
  have hct : star (t : ℂ) = t := Complex.conj_ofReal t
  have hGe : G *ᵥ e = e := by
    rw [hGd, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hVe, smul_zero, sub_zero]
  have h2t : ((2 * t : ℝ) : ℂ) = (t : ℂ) + (t : ℂ) := by push_cast; ring
  have hGHG : Gᴴ * Hm * G = Hm - ((2 * t : ℝ) : ℂ) • vecMulVec (Hm *ᵥ e) (star e ᵥ* Hm) := by
    rw [hGd, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, hct, expand, h3, smul_zero,
      add_zero, h2, h1, h2t, add_smul, sub_sub]
  have hKK : (G * M)ᴴ * Hm * (G * M) =
      -(sgnM n q + ((2 * t : ℝ) : ℂ) • vecMulVec (sgnM n q *ᵥ y) (star y ᵥ* sgnM n q)) := by
    calc (G * M)ᴴ * Hm * (G * M) = Mᴴ * (Gᴴ * Hm * G) * M := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Mᴴ * Hm * M - ((2 * t : ℝ) : ℂ) • (Mᴴ * vecMulVec (Hm *ᵥ e) (star e ᵥ* Hm) * M) := by
          rw [hGHG, mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul]
      _ = _ := by
          rw [hMMl, hMW, Matrix.neg_vecMulVec, Matrix.vecMulVec_neg, neg_neg]
          abel
  have hZZ : Zᴴ * Hm * Z = -(sgnM n q + ((2 * t : ℝ) : ℂ) • vecMulVec (sgnM n q *ᵥ y) (star y ᵥ* sgnM n q)) := by
    rw [← hbS]
    calc Zᴴ * Hm * Z = bᴴ * (x₀ᴴ * Hm * x₀) * b := by
          rw [hZ]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hS, mul_neg, neg_mul]
  have hKZ : (G * M)ᴴ * Hm * (G * M) = Zᴴ * Hm * Z := hKK.trans hZZ.symm
  obtain ⟨U, hUd⟩ : ∃ U : Mt n, U = G * M * Z⁻¹ := ⟨_, rfl⟩
  have hUH : Uᴴ * Hm * U = Hm := by
    calc Uᴴ * Hm * U = Z⁻¹ᴴ * ((G * M)ᴴ * Hm * (G * M)) * Z⁻¹ := by
          rw [hUd]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Z⁻¹ᴴ * (Zᴴ * Hm * Z) * Z⁻¹ := by rw [hKZ]
      _ = Hm := by
          rw [Matrix.conjTranspose_nonsing_inv]
          simp only [Matrix.mul_assoc]
          rw [Matrix.mul_nonsing_inv _ hZu, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left _ _ hZHu]
  have hUu : IsUnit U.det := unit_lemma_5 hUH hHdet
  have hUxb : U * x₀ * b = G * M := by
    rw [hUd, Matrix.mul_assoc (G * M * Z⁻¹) x₀ b, ← hZ, Matrix.nonsing_inv_mul_cancel_right _ _ hZu]
  obtain ⟨v, hvd⟩ : ∃ v : Fin n → ℂ, v = x₀ *ᵥ (b *ᵥ y) := ⟨_, rfl⟩
  have hUv : U *ᵥ v = e := by
    rw [hvd, Matrix.mulVec_mulVec y x₀ b, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hUxb, ← Matrix.mulVec_mulVec,
      hMy, hGe]
  have hinv : U⁻¹ *ᵥ e = v := by
    rw [← hUv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hUu, Matrix.one_mulVec]
  have hC2 : 0 ≤ ∑ i, (∑ j, ‖x₀ i j‖ ^ 2) * ∑ j, (‖y j‖ ^ 2 + 1) := by positivity
  have hC1 : 0 ≤ (1 + 2 * ∑ c, ‖y c‖ ^ 2) ^ (∑ a, (w a).natAbs) := by positivity
  refine ⟨U, hUH, b, hbU, ?_, ?_, ?_⟩
  · rw [← hGd, hUxb, hM, Matrix.mul_assoc]
  · refine (prod_zpow_le (fun a => b a a) w ((1 + 2 * ∑ c, ‖y c‖ ^ 2) * (1 + t)) hbd).trans ?_
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC2) (pow_nonneg (by linarith) _)
  · intro i
    rw [hinv]
    have hvi : v i = ∑ j, x₀ i j * (b *ᵥ y) j := by rw [hvd]; rfl
    have hn1 : ‖v i‖ ≤ ∑ j, ‖x₀ i j‖ * ‖(b *ᵥ y) j‖ := by
      rw [hvi]; exact (norm_sum_le _ _).trans (le_of_eq (by simp only [norm_mul]))
    have hn2 : ‖v i‖ ^ 2 ≤ (∑ j, ‖x₀ i j‖ ^ 2) * ∑ j, ‖(b *ᵥ y) j‖ ^ 2 :=
      (pow_le_pow_left₀ (norm_nonneg _) hn1 2).trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
    have hn3 : (∑ j, ‖(b *ᵥ y) j‖ ^ 2) * (1 + t) ≤ ∑ j, (‖y j‖ ^ 2 + 1) := by
      rw [Finset.sum_mul]; exact Finset.sum_le_sum fun j _ => hby j
    have hn4 : (∑ j, ‖x₀ i j‖ ^ 2) * ∑ j, (‖y j‖ ^ 2 + 1) ≤ ∑ i, (∑ j, ‖x₀ i j‖ ^ 2) * ∑ j, (‖y j‖ ^ 2 + 1) :=
      Finset.single_le_sum (f := fun i => (∑ j, ‖x₀ i j‖ ^ 2) * ∑ j, (‖y j‖ ^ 2 + 1))
        (fun i _ => show (0 : ℝ) ≤ (∑ j, ‖x₀ i j‖ ^ 2) * ∑ j, (‖y j‖ ^ 2 + 1) by positivity) (Finset.mem_univ i)
    have hX0 : 0 ≤ ∑ j, ‖x₀ i j‖ ^ 2 := by positivity
    calc ‖v i‖ ^ 2 * (1 + t) ≤ (∑ j, ‖x₀ i j‖ ^ 2) * (∑ j, ‖(b *ᵥ y) j‖ ^ 2) * (1 + t) :=
          mul_le_mul_of_nonneg_right hn2 (by linarith)
      _ = (∑ j, ‖x₀ i j‖ ^ 2) * ((∑ j, ‖(b *ᵥ y) j‖ ^ 2) * (1 + t)) := by ring
      _ ≤ (∑ j, ‖x₀ i j‖ ^ 2) * ∑ j, (‖y j‖ ^ 2 + 1) := mul_le_mul_of_nonneg_left hn3 hX0
      _ ≤ _ := hn4.trans (le_add_of_nonneg_left hC1)

end GlobalTheory.HolDict.FlowGS
