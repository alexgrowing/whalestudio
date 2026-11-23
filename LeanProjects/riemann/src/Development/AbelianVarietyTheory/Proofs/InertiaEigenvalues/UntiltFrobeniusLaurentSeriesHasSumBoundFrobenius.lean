import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section

open Formalism.Per Filter Topology
open scoped Formalism.Per

namespace GlobalTheory.PSer.Laws

variable {l : ℕ} [Fact l.Prime]

theorem pw_zero (x : Fl l) : pw 0 x = x := by simp [pw]

theorem pw_succ (k : ℤ) (x : Fl l) : pw (k + 1) x = pw k x ^ l := by
  unfold pw
  rw [add_comm, zpow_add, zpow_one]
  rfl

theorem pw_add (a b : ℤ) (x : Fl l) : pw (a + b) x = pw a (pw b x) := by
  unfold pw
  rw [zpow_add]
  rfl

theorem pw_nat (n : ℕ) (x : Fl l) : pw (n : ℤ) x = x ^ l ^ n := by
  induction n with
  | zero => simp [pw_zero]
  | succ n ih => rw [Nat.cast_succ, pw_succ, ih, ← pow_mul, pow_succ]

theorem sh_pow (x : Fl l) (n : ℕ) : sh (x ^ n) = sh x ^ n := by
  unfold sh
  rw [map_pow]; push_cast; rfl

theorem l_pos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
theorem two_le_l : (2 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le

theorem norm_sh_pw (k : ℤ) (x : Fl l) : ‖sh (pw k x)‖ = ‖sh x‖ ^ ((l : ℝ) ^ k) := by
  have hl := l_pos (l := l)
  induction k using Int.induction_on with
  | zero => simp [pw_zero]
  | succ k ih =>
    rw [pw_succ, sh_pow, norm_pow, ih, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _),
      zpow_add_one₀ hl.ne']
  | pred k ih =>
    have h1 : pw (-(k : ℤ)) x = pw (-(k : ℤ) - 1) x ^ l := by
      rw [← pw_succ]; congr 1; ring
    rw [h1, sh_pow, norm_pow] at ih
    have h2 : (‖sh x‖ ^ ((l : ℝ) ^ (-(k : ℤ) - 1))) ^ l = ‖sh x‖ ^ ((l : ℝ) ^ (-(k : ℤ))) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← zpow_add_one₀ hl.ne']
      congr 2; ring
    rw [← h2] at ih
    exact (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)
      (Fact.out : l.Prime).ne_zero).1 ih

theorem norm_l : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [GlobalTheory.RingBasics.norm_eq_val, PadicComplex.valuation_p]; simp

def sz (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) (n : ℤ) : ℝ :=
  ‖(l : ℂ_[l])‖ ^ (-n) * r ^ ((l : ℝ) ^ (n * h + j : ℤ))

theorem norm_term (h j : ℕ) (x : Fl l) (n : ℤ) :
    ‖(l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x)‖ = sz l h j ‖sh x‖ n := by
  rw [norm_mul, norm_zpow, norm_sh_pw]; rfl

theorem sz_nonneg (h j : ℕ) {r : ℝ} (hr : 0 ≤ r) (n : ℤ) : 0 ≤ sz l h j r n :=
  mul_nonneg (zpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg hr _)

theorem sz_mono (h j : ℕ) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (n : ℤ) :
    sz l h j r n ≤ sz l h j s n :=
  mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr hrs (zpow_nonneg l_pos.le _))
    (zpow_nonneg (norm_nonneg _) _)

theorem tendsto_sz {h : ℕ} (hh : 1 ≤ h) (j : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (sz l h j r) cofinite (𝓝 0) := by
  have hl := l_pos (l := l)
  have hl2 := two_le_l (l := l)
  rw [Int.cofinite_eq, tendsto_sup]
  constructor
  · have hb : Tendsto (fun n : ℤ => (l : ℝ) ^ n) atBot (𝓝 0) := by
      have := (tendsto_rpow_atBot_of_base_gt_one (l : ℝ) (by linarith)).comp
        ((tendsto_intCast_atBot_iff (R := ℝ)).2 (tendsto_id (α := ℤ) (x := atBot)))
      refine this.congr fun n => ?_
      simp
    refine squeeze_zero (sz_nonneg h j hr) (fun n => ?_) hb
    unfold sz
    rw [norm_l, inv_zpow', neg_neg]
    exact mul_le_of_le_one_right (zpow_nonneg hl.le _)
      (Real.rpow_le_one hr hr1.le (zpow_nonneg hl.le _))
  · rw [← Nat.map_cast_int_atTop, tendsto_map'_iff]
    have h1 : Tendsto (fun n : ℕ => l ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (Fact.out : l.Prime).one_lt
    have h2 := (tendsto_self_mul_const_pow_of_lt_one hr hr1).comp h1
    refine squeeze_zero (fun n => sz_nonneg h j hr _) (fun n => ?_) h2
    simp only [Function.comp, sz]
    rw [norm_l, inv_zpow', neg_neg, zpow_natCast, Nat.cast_pow]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hl.le _)
    have : ((n : ℤ) * h + j : ℤ) = ((n * h + j : ℕ) : ℤ) := by push_cast; ring
    rw [this, zpow_natCast, ← Nat.cast_pow, Real.rpow_natCast]
    refine pow_le_pow_of_le_one hr hr1.le (Nat.pow_le_pow_right (Fact.out : l.Prime).pos ?_)
    nlinarith

theorem summable_lam {h : ℕ} (hh : 1 ≤ h) (j : ℕ) {x : Fl l} (hx : ‖sh x‖ < 1) :
    Summable fun n : ℤ => (l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_term]
  exact tendsto_sz hh j (norm_nonneg _) hx

theorem bdd_sz {h : ℕ} (hh : 1 ≤ h) (j : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    BddAbove (Set.range (sz l h j r)) :=
  (tendsto_sz hh j hr hr1).bddAbove_range_of_cofinite

theorem gam_nonneg (h j : ℕ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ gam l h j r :=
  Real.iSup_nonneg (sz_nonneg h j hr)

theorem norm_lam_le {h : ℕ} (hh : 1 ≤ h) (j : ℕ) {x : Fl l} {r : ℝ} (hx : ‖sh x‖ ≤ r) (hr : r < 1) :
    ‖lam h j x‖ ≤ gam l h j r := by
  have h0 : 0 ≤ r := (norm_nonneg _).trans hx
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (gam_nonneg h j h0) fun n => ?_
  rw [norm_term]
  exact (sz_mono h j (norm_nonneg _) hx n).trans (le_ciSup (bdd_sz hh j h0 hr) n)

theorem lam_shift (h j : ℕ) (x : Fl l) : lam h (j + h) x = l * lam h j x := by
  unfold lam
  rw [← tsum_mul_left, ← (Equiv.addRight (1 : ℤ)).tsum_eq
    (fun n : ℤ => (l : ℂ_[l]) * ((l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x)))]
  refine tsum_congr fun n => ?_
  have h1 : (n * h + ((j + h : ℕ) : ℤ)) = (n + 1) * h + j := by push_cast; ring
  simp only [Equiv.coe_addRight]
  rw [h1, ← mul_assoc, ← zpow_one_add₀ GlobalTheory.RingBasics.p_ne_zero]
  congr 2; ring

theorem lam_pow (h j k : ℕ) (x : Fl l) : lam h j (x ^ l ^ k) = lam h (j + k) x := by
  unfold lam
  refine tsum_congr fun n => ?_
  rw [← pw_nat, ← pw_add]
  congr 3
  push_cast; ring

end GlobalTheory.PSer.Laws

namespace GlobalTheory.PSer

open Laws

theorem lam_hasSum_norm_le_frob : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) (x : Fl l), 1 ≤ h → r < 1 →
    ‖sh x‖ ≤ r → HasSum (fun n : ℤ => (l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x)) (lam h j x) ∧
      ‖lam h j x‖ ≤ gam l h j r ∧ lam h j (x ^ l ^ h) = (l : ℂ_[l]) * lam h j x ∧
      lam h j (x ^ l) = lam h (j + 1) x := by
  intro l _ h j r x hh hr hx
  refine ⟨(summable_lam hh j (hx.trans_lt hr)).hasSum, norm_lam_le hh j hx hr, ?_, ?_⟩
  · rw [lam_pow, lam_shift]
  · have := lam_pow (l := l) h j 1 x
    rwa [pow_one] at this

end GlobalTheory.PSer

end
