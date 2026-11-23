import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Foundations.MultipliableAndSgNeZero

noncomputable section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam GlobalTheory.Sieg.Model Filter Topology

namespace GlobalTheory.Sieg.DlogOne

def gP (q a : ℂ) : ℂ := ∏' m : ℕ, (1 - q ^ (m + 1) * a)

def gS (q a : ℂ) : ℂ := ∑' m : ℕ, q ^ (m + 1) * a / (1 - q ^ (m + 1) * a)

open scoped UpperHalfPlane MatrixGroups Manifold in
open Filter Topology in
theorem _root_.GlobalTheory.Sieg.DlogOne.hasProd_gP {q : ℂ} (hq : ‖q‖ < 1) (a : ℂ) :
    HasProd (fun m : ℕ => 1 - q ^ (m + 1) * a) (_root_.GlobalTheory.Sieg.DlogOne.gP q a) := by
  have hs : Summable fun m : ℕ => ‖-(q ^ (m + 1) * a)‖ := by
    have := (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_right (‖q‖ * ‖a‖)
    refine this.congr fun m => ?_
    rw [norm_neg, norm_mul, norm_pow, pow_succ]
    ring
  have hm := multipliable_one_add_of_summable hs
  simp only [← sub_eq_add_neg] at hm
  exact hm.hasProd

theorem gP_ne_zero {q : ℂ} (hq : ‖q‖ < 1) {a : ℂ} (h : ∀ m : ℕ, 1 - q ^ (m + 1) * a ≠ 0) : gP q a ≠ 0 := by
  obtain ⟨P, hP, pP⟩ := hasProd_geom hq a h
  rwa [gP, pP.tprod_eq]

open scoped UpperHalfPlane MatrixGroups Manifold in
open Filter Topology in
theorem _root_.GlobalTheory.Sieg.DlogOne.summable_lambert {q : ℂ} (hq : ‖q‖ < 1) (a : ℂ) :
    Summable fun m : ℕ => q ^ (m + 1) / (1 - q ^ (m + 1) * a) := by
  have hq0 : Tendsto (fun m : ℕ => q ^ (m + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).comp (tendsto_add_atTop_nat 1)
  have hden : Tendsto (fun m : ℕ => (1 - q ^ (m + 1) * a)⁻¹) atTop (𝓝 1) := by
    have : Tendsto (fun m : ℕ => 1 - q ^ (m + 1) * a) atTop (𝓝 (1 - 0 * a)) :=
      tendsto_const_nhds.sub (hq0.mul tendsto_const_nhds)
    simpa using this.inv₀ (by simp)
  have hsum : Summable fun m : ℕ => ‖q‖ ^ (m + 1) := by
    simpa [pow_succ] using (summable_geometric_of_lt_one (norm_nonneg _) hq).mul_right ‖q‖
  refine summable_of_isBigO_nat hsum ?_
  have h1 : (fun m : ℕ => (1 - q ^ (m + 1) * a)⁻¹) =O[atTop] (fun _ => (1 : ℝ)) :=
    hden.isBigO_one ℝ
  have h2 : (fun m : ℕ => q ^ (m + 1)) =O[atTop] (fun m : ℕ => ‖q‖ ^ (m + 1)) :=
    Asymptotics.isBigO_of_le _ fun m => by simp [norm_pow]
  simpa [div_eq_mul_inv] using h2.mul h1

theorem multLoc {q : ℂ} (hq : ‖q‖ < 1) (R : ℝ) :
    MultipliableLocallyUniformlyOn (fun (m : ℕ) (a : ℂ) => 1 - q ^ (m + 1) * a) (Metric.ball 0 R) := by
  simp only [sub_eq_add_neg]
  refine (((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg _)
        hq)).mul_right R).multipliableLocallyUniformlyOn_nat_one_add Metric.isOpen_ball
        (.of_forall fun n z hz ↦ ?_) (fun _ ↦ by fun_prop)
  rw [norm_neg, norm_mul, norm_pow]
  have : ‖z‖ ≤ R := (mem_ball_zero_iff.1 hz).le
  gcongr

theorem differentiableAt_gP {q : ℂ} (hq : ‖q‖ < 1) (a : ℂ) : DifferentiableAt ℂ (gP q) a := by
  have ha : a ∈ Metric.ball (0 : ℂ) (‖a‖ + 1) := by simp
  have := (multLoc hq (‖a‖ + 1)).hasProdLocallyUniformlyOn.differentiableOn
    (.of_forall fun _ ↦ by simpa [Finset.prod_fn] using
      DifferentiableOn.finsetProd (fun _ _ ↦ by fun_prop)) Metric.isOpen_ball
  exact this.differentiableAt (Metric.isOpen_ball.mem_nhds ha)

def LD (f : ℂ → ℂ) (L z : ℂ) : Prop := HasDerivAt f (L * f z) z

theorem LD.mul {f g : ℂ → ℂ} {L M z : ℂ} (hf : LD f L z) (hg : LD g M z) :
    LD (fun w => f w * g w) (L + M) z := by
  have := HasDerivAt.fun_mul hf hg
  refine HasDerivAt.congr_deriv this ?_
  ring

theorem LD.pow {f : ℂ → ℂ} {L z : ℂ} (hf : LD f L z) (k : ℕ) : LD (fun w => f w ^ k) (k * L) z := by
  induction k with
  | zero => simpa [LD] using hasDerivAt_const z (1 : ℂ)
  | succ k ih =>
    have := ih.mul hf
    simp only [← pow_succ] at this
    convert this using 1; push_cast; ring

theorem LD.inv {f : ℂ → ℂ} {L z : ℂ} (hf : LD f L z) (h0 : f z ≠ 0) : LD (fun w => (f w)⁻¹) (-L) z := by
  have := HasDerivAt.fun_inv hf h0
  refine HasDerivAt.congr_deriv this ?_
  field_simp

theorem LD.div {f g : ℂ → ℂ} {L M z : ℂ} (hf : LD f L z) (hg : LD g M z) (h0 : g z ≠ 0) :
    LD (fun w => f w / g w) (L - M) z := by
  simpa only [div_eq_mul_inv, sub_eq_add_neg] using hf.mul (hg.inv h0)

theorem LD.zpow_neg {f : ℂ → ℂ} {L z : ℂ} (hf : LD f L z) (h0 : f z ≠ 0) (k : ℤ) :
    LD (fun w => (-f w) ^ k) (k * L) z := by
  have h1 : -f z ≠ 0 := neg_ne_zero.2 h0
  have := (hasDerivAt_zpow k (-f z) (Or.inl h1)).comp z (HasDerivAt.fun_neg hf)
  refine HasDerivAt.congr_deriv this ?_
  rw [zpow_sub_one₀ h1]; field_simp

theorem LD.gP {q : ℂ} (hq : ‖q‖ < 1) {f : ℂ → ℂ} {L z : ℂ} (hf : LD f L z)
    (h : ∀ m : ℕ, 1 - q ^ (m + 1) * f z ≠ 0) : LD (fun w => gP q (f w)) (-(L * gS q (f z))) z := by
  have ha : f z ∈ Metric.ball (0 : ℂ) (‖f z‖ + 1) := by simp
  have e : ∀ m : ℕ, logDeriv (fun a : ℂ => 1 - q ^ (m + 1) * a) (f z) =
      -(q ^ (m + 1) / (1 - q ^ (m + 1) * f z)) := by
    intro m
    simp [logDeriv_apply, neg_div]
  have hne := gP_ne_zero hq h
  have key := logDeriv_tprod_eq_tsum Metric.isOpen_ball ha (f := fun (m : ℕ) (a : ℂ) => 1 - q ^ (m + 1) * a) h
    (fun _ => by fun_prop) (by simpa only [e] using (summable_lambert hq (f z)).neg) (multLoc hq _) hne
  simp only [e, tsum_neg] at key
  have key' : deriv (DlogOne.gP q) (f z) / DlogOne.gP q (f z) = -∑' m : ℕ, q ^ (m + 1) / (1 - q ^ (m + 1) * f z) := key
  rw [div_eq_iff hne] at key'
  have := (differentiableAt_gP hq (f z)).hasDerivAt.comp z hf
  have e2 : gS q (f z) = (∑' m : ℕ, q ^ (m + 1) / (1 - q ^ (m + 1) * f z)) * f z := by
    rw [gS, ← tsum_mul_right]; exact tsum_congr fun m => by ring
  refine HasDerivAt.congr_deriv this ?_
  rw [key', e2]; ring

def E (q t : ℂ) : ℂ := -(t / (1 - t)) - gS q t + gS q t⁻¹

open scoped UpperHalfPlane MatrixGroups Manifold in
open Filter Topology in
theorem _root_.GlobalTheory.Sieg.DlogOne.tprod_cthFac_eq {q : ℂ} (hq : ‖q‖ < 1) (c : ℕ) {t : ℂ}
    (h : _root_.GlobalTheory.Sieg.DlogOne.gP q (t ^ c) * _root_.GlobalTheory.Sieg.DlogOne.gP q (t ^ c)⁻¹ ≠ 0) :
    ∏' m : ℕ, _root_.GlobalTheory.Sieg.cthFac c q t (m + 1) =
      _root_.GlobalTheory.Sieg.DlogOne.gP q t ^ (c ^ 2) * _root_.GlobalTheory.Sieg.DlogOne.gP q t⁻¹ ^ (c ^ 2) /
        (_root_.GlobalTheory.Sieg.DlogOne.gP q (t ^ c) * _root_.GlobalTheory.Sieg.DlogOne.gP q (t ^ c)⁻¹) := by
  have hA := (_root_.GlobalTheory.Sieg.Model.hasProd_pow (_root_.GlobalTheory.Sieg.DlogOne.hasProd_gP hq t) (c ^ 2)).mul
    (_root_.GlobalTheory.Sieg.Model.hasProd_pow (_root_.GlobalTheory.Sieg.DlogOne.hasProd_gP hq t⁻¹) (c ^ 2))
  have hB := _root_.GlobalTheory.Sieg.Model.hasProd_inv
    ((_root_.GlobalTheory.Sieg.DlogOne.hasProd_gP hq (t ^ c)).mul (_root_.GlobalTheory.Sieg.DlogOne.hasProd_gP hq (t ^ c)⁻¹)) h
  rw [div_eq_mul_inv, ← (hA.mul hB).tprod_eq]
  congr 1

open scoped UpperHalfPlane MatrixGroups Manifold in
open Filter Topology in
theorem _root_.GlobalTheory.Sieg.DlogOne.ee_int_mul (n : ℤ) (z : ℂ) :
    _root_.GlobalTheory.Sieg.ee (n * z) = _root_.GlobalTheory.Sieg.ee z ^ n := by
  unfold _root_.GlobalTheory.Sieg.ee
  rw [← Complex.exp_int_mul]
  congr 1
  ring

def u (x : Fin 2 → ℚ) (τ : ℍ) (n : ℤ) : ℂ := ee (((x 0 + n : ℚ) : ℂ) * τ + x 1)

open scoped UpperHalfPlane MatrixGroups Manifold in
open Filter Topology in
private lemma u_eq_ee_zpow_mul_ee_pt (x : Fin 2 → ℚ) (τ : ℍ) (n : ℤ) :
    _root_.GlobalTheory.Sieg.DlogOne.u x τ n =
      _root_.GlobalTheory.Sieg.ee τ ^ n * _root_.GlobalTheory.Sieg.ee (_root_.GlobalTheory.Sieg.pt x τ) := by
  rw [← _root_.GlobalTheory.Sieg.DlogOne.ee_int_mul, ← _root_.GlobalTheory.Sieg.Model.ee_add]
  unfold _root_.GlobalTheory.Sieg.DlogOne.u _root_.GlobalTheory.Sieg.pt
  congr 1
  push_cast
  ring

open scoped UpperHalfPlane MatrixGroups Manifold in
open Filter Topology in
private lemma im_shifted_lattice_point (x : Fin 2 → ℚ) (τ : ℍ) (p : ℤ) :
    (((x 0 + p : ℚ) : ℂ) * (τ : ℂ) + ((x 1 : ℚ) : ℂ)).im = ((x 0 + p : ℚ) : ℝ) * τ.im := by
  simp

open scoped UpperHalfPlane MatrixGroups Manifold in
open Filter Topology in
private lemma norm_u_lt_one_of_pos {x : Fin 2 → ℚ} {τ : ℍ} {p : ℤ}
    (h : 0 < x 0 + p) : ‖_root_.GlobalTheory.Sieg.DlogOne.u x τ p‖ < 1 := by
  rw [_root_.GlobalTheory.Sieg.DlogOne.u, _root_.GlobalTheory.Sieg.Model.norm_ee, Real.exp_lt_one_iff, neg_lt_zero,
    im_shifted_lattice_point]
  have ha : (0 : ℝ) < ((x 0 + p : ℚ) : ℝ) := by exact_mod_cast h
  exact mul_pos (mul_pos two_pos Real.pi_pos) (mul_pos ha τ.im_pos)

open scoped UpperHalfPlane MatrixGroups Manifold in
open Filter Topology in
private lemma hasSum_fTerm_fiber_of_pos {x : Fin 2 → ℚ} {τ : ℍ} {p : ℤ} (h : 0 < x 0 + p) :
    HasSum (fun n : ℤ => _root_.GlobalTheory.Sieg.fTerm 1 x τ (p, n))
      (_root_.GlobalTheory.Sieg.DlogOne.u x τ p / (1 - _root_.GlobalTheory.Sieg.DlogOne.u x τ p)) := by
  have hu := norm_u_lt_one_of_pos (τ := τ) h
  have hgeo : HasSum (fun n : ℕ => _root_.GlobalTheory.Sieg.DlogOne.u x τ p ^ (n + 1))
      (_root_.GlobalTheory.Sieg.DlogOne.u x τ p / (1 - _root_.GlobalTheory.Sieg.DlogOne.u x τ p)) := by
    simpa only [pow_succ', div_eq_mul_inv] using
      (hasSum_geometric_of_norm_lt_one hu).mul_left (_root_.GlobalTheory.Sieg.DlogOne.u x τ p)
  have hnat : HasSum (fun n : ℕ => _root_.GlobalTheory.Sieg.fTerm 1 x τ (p, (n : ℤ)))
      (_root_.GlobalTheory.Sieg.DlogOne.u x τ p / (1 - _root_.GlobalTheory.Sieg.DlogOne.u x τ p)) := by
    refine (hasSum_nat_add_iff' 1).mp ?_
    have h0 : _root_.GlobalTheory.Sieg.fTerm 1 x τ (p, ((0 : ℕ) : ℤ)) = 0 := by
      simp [_root_.GlobalTheory.Sieg.fTerm]
    simp only [Finset.range_one, Finset.sum_singleton, h0, sub_zero]
    refine hgeo.congr_fun fun n => ?_
    have hn : (0 : ℤ) < ((n + 1 : ℕ) : ℤ) := by positivity
    simp only [_root_.GlobalTheory.Sieg.fTerm]
    split_ifs with hc
    · rw [Int.sign_eq_one_of_pos hn, mul_assoc _ (_root_.GlobalTheory.Sieg.ee _),
        ← _root_.GlobalTheory.Sieg.Model.ee_add, _root_.GlobalTheory.Sieg.DlogOne.u, ← _root_.GlobalTheory.Sieg.Model.ee_nat_mul]
      simp only [Int.cast_one, one_mul, Nat.sub_self, pow_zero]
      congr 1
      push_cast
      ring
    · exfalso
      apply hc
      have : (0 : ℚ) < ((n + 1 : ℕ) : ℤ) := by exact_mod_cast hn
      exact mul_pos h this
  have hneg : HasSum (fun n : ℕ => _root_.GlobalTheory.Sieg.fTerm 1 x τ (p, -((n : ℤ) + 1))) 0 := by
    refine hasSum_zero.congr_fun fun n => ?_
    simp only [_root_.GlobalTheory.Sieg.fTerm]
    split_ifs with hc
    · exfalso
      push_cast at hc
      nlinarith [(n.cast_nonneg : (0 : ℚ) ≤ n)]
    · rfl
  simpa only [add_zero] using
    HasSum.of_nat_of_neg_add_one (f := fun n : ℤ => _root_.GlobalTheory.Sieg.fTerm 1 x τ (p, n)) hnat hneg

open scoped UpperHalfPlane MatrixGroups Manifold in
open Filter Topology in
private lemma ee_neg' (z : ℂ) :
    _root_.GlobalTheory.Sieg.ee (-z) = (_root_.GlobalTheory.Sieg.ee z)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← _root_.GlobalTheory.Sieg.Model.ee_add, neg_add_cancel]
  simp [_root_.GlobalTheory.Sieg.ee]

open scoped UpperHalfPlane MatrixGroups Manifold in
open Filter Topology in
private lemma norm_inv_u_lt_one_of_neg {x : Fin 2 → ℚ} {τ : ℍ} {p : ℤ}
    (h : x 0 + p < 0) : ‖(_root_.GlobalTheory.Sieg.DlogOne.u x τ p)⁻¹‖ < 1 := by
  rw [_root_.GlobalTheory.Sieg.DlogOne.u, ← ee_neg', _root_.GlobalTheory.Sieg.Model.norm_ee,
    Real.exp_lt_one_iff, neg_lt_zero, Complex.neg_im, im_shifted_lattice_point]
  have ha : ((x 0 + p : ℚ) : ℝ) < 0 := by exact_mod_cast h
  nlinarith [Real.pi_pos, τ.im_pos, mul_neg_of_neg_of_pos ha τ.im_pos]

open scoped UpperHalfPlane MatrixGroups Manifold in
open Filter Topology in
private lemma hasSum_fTerm_fiber_of_neg {x : Fin 2 → ℚ} {τ : ℍ} {p : ℤ} (h : x 0 + p < 0) :
    HasSum (fun n : ℤ => _root_.GlobalTheory.Sieg.fTerm 1 x τ (p, n))
      (-((_root_.GlobalTheory.Sieg.DlogOne.u x τ p)⁻¹ / (1 - (_root_.GlobalTheory.Sieg.DlogOne.u x τ p)⁻¹))) := by
  have hw := norm_inv_u_lt_one_of_neg (τ := τ) h
  have hgeo : HasSum (fun n : ℕ => -((_root_.GlobalTheory.Sieg.DlogOne.u x τ p)⁻¹ ^ (n + 1)))
      (-((_root_.GlobalTheory.Sieg.DlogOne.u x τ p)⁻¹ / (1 - (_root_.GlobalTheory.Sieg.DlogOne.u x τ p)⁻¹))) := by
    simpa only [pow_succ', div_eq_mul_inv] using
      ((hasSum_geometric_of_norm_lt_one hw).mul_left (_root_.GlobalTheory.Sieg.DlogOne.u x τ p)⁻¹).neg
  have hnat : HasSum (fun n : ℕ => _root_.GlobalTheory.Sieg.fTerm 1 x τ (p, (n : ℤ))) 0 := by
    refine hasSum_zero.congr_fun fun n => ?_
    simp only [_root_.GlobalTheory.Sieg.fTerm]
    split_ifs with hc
    · exfalso
      push_cast at hc
      nlinarith [(n.cast_nonneg : (0 : ℚ) ≤ n)]
    · rfl
  have hneg : HasSum (fun n : ℕ => _root_.GlobalTheory.Sieg.fTerm 1 x τ (p, -((n : ℤ) + 1)))
      (-((_root_.GlobalTheory.Sieg.DlogOne.u x τ p)⁻¹ / (1 - (_root_.GlobalTheory.Sieg.DlogOne.u x τ p)⁻¹))) := by
    refine hgeo.congr_fun fun n => ?_
    have hn : -((n : ℤ) + 1) < 0 := by omega
    simp only [_root_.GlobalTheory.Sieg.fTerm]
    split_ifs with hc
    · rw [Int.sign_eq_neg_one_of_neg hn, mul_assoc _ (_root_.GlobalTheory.Sieg.ee _),
        ← _root_.GlobalTheory.Sieg.Model.ee_add, _root_.GlobalTheory.Sieg.DlogOne.u, ← ee_neg',
        ← _root_.GlobalTheory.Sieg.Model.ee_nat_mul]
      simp only [Nat.sub_self, pow_zero, mul_one, Int.cast_neg, Int.cast_one, neg_one_mul]
      congr 2
      push_cast
      ring
    · exfalso
      apply hc
      push_cast
      nlinarith [(n.cast_nonneg : (0 : ℚ) ≤ n)]
  simpa only [zero_add] using
    HasSum.of_nat_of_neg_add_one (f := fun n : ℤ => _root_.GlobalTheory.Sieg.fTerm 1 x τ (p, n)) hnat hneg

open scoped UpperHalfPlane MatrixGroups Manifold in
open Filter Topology in
private lemma summable_lambert_term {q : ℂ} (hq : ‖q‖ < 1) (a : ℂ) :
    Summable fun m : ℕ => q ^ (m + 1) * a / (1 - q ^ (m + 1) * a) :=
  ((_root_.GlobalTheory.Sieg.DlogOne.summable_lambert hq a).mul_left a).congr fun m => by ring

open scoped UpperHalfPlane MatrixGroups Manifold in
open Filter Topology in
private lemma hasSum_lambert_gS {q : ℂ} (hq : ‖q‖ < 1) (a : ℂ) :
    HasSum (fun m : ℕ => q ^ (m + 1) * a / (1 - q ^ (m + 1) * a)) (_root_.GlobalTheory.Sieg.DlogOne.gS q a) :=
  (summable_lambert_term hq a).hasSum

open scoped UpperHalfPlane MatrixGroups Manifold in
open Filter Topology in
private lemma E_ee_pt_eq_neg_F_of_mem_Ico {x : Fin 2 → ℚ}
    (hx : ¬ (x 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ x 1 ∈ Set.range ((↑) : ℤ → ℚ)))
    (h0 : 0 ≤ x 0) (h1 : x 0 < 1) (τ : ℍ) :
    _root_.GlobalTheory.Sieg.DlogOne.E (_root_.GlobalTheory.Sieg.ee τ)
        (_root_.GlobalTheory.Sieg.ee (_root_.GlobalTheory.Sieg.pt x τ)) =
      -(_root_.GlobalTheory.Sieg.F 1 x τ - 1 / 2 + x 0) := by
  have hq : ‖_root_.GlobalTheory.Sieg.ee τ‖ < 1 := _root_.GlobalTheory.Sieg.Model.norm_ee_lt_one τ
  have hne := _root_.GlobalTheory.Sieg.Model.ne_one_of_not_int hx τ
  set q := _root_.GlobalTheory.Sieg.ee τ with hq_def
  set t := _root_.GlobalTheory.Sieg.ee (_root_.GlobalTheory.Sieg.pt x τ) with ht_def
  have hu : ∀ n : ℤ, _root_.GlobalTheory.Sieg.DlogOne.u x τ n = q ^ n * t :=
    fun n => u_eq_ee_zpow_mul_ee_pt x τ n
  let g : ℤ → ℂ := fun p => if 0 < x 0 + p then
      _root_.GlobalTheory.Sieg.DlogOne.u x τ p / (1 - _root_.GlobalTheory.Sieg.DlogOne.u x τ p)
    else if x 0 + p < 0 then
      -((_root_.GlobalTheory.Sieg.DlogOne.u x τ p)⁻¹ / (1 - (_root_.GlobalTheory.Sieg.DlogOne.u x τ p)⁻¹))
    else 0
  have hfib : ∀ p : ℤ, HasSum (fun n : ℤ => _root_.GlobalTheory.Sieg.fTerm 1 x τ (p, n)) (g p) := by
    intro p
    simp only [g]
    split_ifs with hp hp'
    · exact hasSum_fTerm_fiber_of_pos hp
    · exact hasSum_fTerm_fiber_of_neg hp'
    · have hz : x 0 + p = 0 := by linarith [not_lt.mp hp, not_lt.mp hp']
      refine hasSum_zero.congr_fun fun n => ?_
      simp [_root_.GlobalTheory.Sieg.fTerm, hz]
  have hg := (_root_.GlobalTheory.Sieg.Model.summable_fTerm 1 x τ).hasSum.prod_fiberwise hfib
  have hgpos : ∀ n : ℕ, g ((n + 1 : ℕ) : ℤ) = q ^ (n + 1) * t / (1 - q ^ (n + 1) * t) := by
    intro n
    have hc : 0 < x 0 + (((n + 1 : ℕ) : ℤ) : ℚ) := by
      push_cast
      linarith [(n.cast_nonneg : (0 : ℚ) ≤ n)]
    simp only [g, if_pos hc, hu, zpow_natCast]
  have hgneg : ∀ n : ℕ, g (-((n : ℤ) + 1)) = -(q ^ (n + 1) * t⁻¹ / (1 - q ^ (n + 1) * t⁻¹)) := by
    intro n
    have h2 : x 0 + ((-((n : ℤ) + 1) : ℤ) : ℚ) < 0 := by
      push_cast
      linarith [(n.cast_nonneg : (0 : ℚ) ≤ n)]
    have h3 : ¬ 0 < x 0 + ((-((n : ℤ) + 1) : ℤ) : ℚ) := not_lt.mpr h2.le
    have h4 : (_root_.GlobalTheory.Sieg.DlogOne.u x τ (-((n : ℤ) + 1)))⁻¹ = q ^ (n + 1) * t⁻¹ := by
      rw [hu, mul_inv, zpow_neg, inv_inv]
      norm_cast
    simp only [g, if_neg h3, if_pos h2, h4]
  have hnat : HasSum (fun n : ℕ => g n) (g 0 + _root_.GlobalTheory.Sieg.DlogOne.gS q t) := by
    refine (hasSum_nat_add_iff' 1).mp ?_
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, add_sub_cancel_left]
    exact (hasSum_lambert_gS hq t).congr_fun fun n => hgpos n
  have hneg : HasSum (fun n : ℕ => g (-((n : ℤ) + 1))) (-_root_.GlobalTheory.Sieg.DlogOne.gS q t⁻¹) := by
    exact (hasSum_lambert_gS hq t⁻¹).neg.congr_fun fun n => hgneg n
  have hsum : ∑' p, _root_.GlobalTheory.Sieg.fTerm 1 x τ p =
      g 0 + _root_.GlobalTheory.Sieg.DlogOne.gS q t + -_root_.GlobalTheory.Sieg.DlogOne.gS q t⁻¹ :=
    hg.unique (HasSum.of_nat_of_neg_add_one (f := g) hnat hneg)
  have hg0 : g 0 = if x 0 = 0 then 0 else t / (1 - t) := by
    rcases h0.eq_or_lt with h | h
    · simp [g, ← h]
    · simp [g, h, h.ne', hu]
  have hfr : Int.fract (x 0) = x 0 := Int.fract_eq_self.mpr ⟨h0, h1⟩
  rw [_root_.GlobalTheory.Sieg.F, hsum, hg0]
  simp only [_root_.GlobalTheory.Sieg.DlogOne.E, _root_.GlobalTheory.Sieg.f0, ↓reduceIte, hfr]
  rcases h0.eq_or_lt with h | h
  · have hx0 : x 0 = 0 := h.symm
    have hte : t = _root_.GlobalTheory.Sieg.ee (x 1) := by
      rw [ht_def, _root_.GlobalTheory.Sieg.pt, hx0]
      simp
    have h1t : 1 - t ≠ 0 := by simpa using (hne 0).1
    rw [if_pos hx0, if_pos hx0, ← hte, hx0]
    field_simp
    ring
  · rw [if_neg h.ne', if_neg h.ne']
    ring

open scoped UpperHalfPlane MatrixGroups Manifold in
open Filter Topology in
private lemma E_mul_left_eq_sub_one {q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) {t : ℂ}
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    _root_.GlobalTheory.Sieg.DlogOne.E q (q * t) = _root_.GlobalTheory.Sieg.DlogOne.E q t - 1 := by
  have h1 : _root_.GlobalTheory.Sieg.DlogOne.gS q t = q * t / (1 - q * t) + _root_.GlobalTheory.Sieg.DlogOne.gS q (q * t) := by
    unfold _root_.GlobalTheory.Sieg.DlogOne.gS
    rw [(summable_lambert_term hq t).tsum_eq_zero_add]
    congr 1
    · simp
    · exact tsum_congr fun m => by ring
  have hterm : ∀ m : ℕ, q ^ (m + 1) * (q * t)⁻¹ = q ^ m * t⁻¹ := fun m => by
    rw [pow_succ, mul_inv]
    field_simp
  have hsum : Summable fun m : ℕ => q ^ m * t⁻¹ / (1 - q ^ m * t⁻¹) :=
    (summable_nat_add_iff 1).mp (summable_lambert_term hq t⁻¹)
  have h2 : _root_.GlobalTheory.Sieg.DlogOne.gS q (q * t)⁻¹ = t⁻¹ / (1 - t⁻¹) + _root_.GlobalTheory.Sieg.DlogOne.gS q t⁻¹ := by
    unfold _root_.GlobalTheory.Sieg.DlogOne.gS
    simp_rw [hterm]
    rw [hsum.tsum_eq_zero_add]
    simp only [pow_zero, one_mul]
  have key : t⁻¹ / (1 - t⁻¹) = -(t / (1 - t)) - 1 := by
    have h3 : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
    have h4 : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
    field_simp
    ring
  simp only [_root_.GlobalTheory.Sieg.DlogOne.E]
  rw [h1, h2, key]
  ring

open scoped UpperHalfPlane MatrixGroups Manifold in
open Filter Topology in
private lemma E_zpow_mul_eq_sub {q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) {t : ℂ}
    (ht0 : t ≠ 0) (ht : ∀ k : ℤ, q ^ k * t ≠ 1) (k : ℤ) :
    _root_.GlobalTheory.Sieg.DlogOne.E q (q ^ k * t) = _root_.GlobalTheory.Sieg.DlogOne.E q t - k := by
  refine Int.induction_on k ?_ ?_ ?_
  · simp
  · intro n ih
    rw [zpow_add_one₀ hq0, mul_comm (q ^ (n : ℤ)) q, mul_assoc,
      E_mul_left_eq_sub_one hq hq0 (mul_ne_zero (zpow_ne_zero _ hq0) ht0) (ht n), ih]
    push_cast
    ring
  · intro n ih
    have h := E_mul_left_eq_sub_one hq hq0
      (mul_ne_zero (zpow_ne_zero (-(n : ℤ) - 1) hq0) ht0) (ht (-(n : ℤ) - 1))
    rw [← mul_assoc, ← zpow_one_add₀ hq0, show 1 + (-(n : ℤ) - 1) = -n by ring, ih] at h
    push_cast at h ⊢
    linear_combination -h

open scoped UpperHalfPlane MatrixGroups Manifold in
open Filter Topology in
theorem _root_.GlobalTheory.Sieg.DlogOne.E_eq {x : Fin 2 → ℚ}
    (hx : ¬ (x 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ x 1 ∈ Set.range ((↑) : ℤ → ℚ))) (τ : ℍ) :
    _root_.GlobalTheory.Sieg.DlogOne.E (_root_.GlobalTheory.Sieg.ee τ) (_root_.GlobalTheory.Sieg.ee (_root_.GlobalTheory.Sieg.pt x τ)) =
      -(_root_.GlobalTheory.Sieg.F 1 x τ - 1 / 2 + x 0) := by
  let y : Fin 2 → ℚ := ![Int.fract (x 0), x 1]
  have hy0 : y 0 = Int.fract (x 0) := rfl
  have hy1 : y 1 = x 1 := rfl
  have hy : ¬ (y 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ y 1 ∈ Set.range ((↑) : ℤ → ℚ)) := by
    rintro ⟨⟨m, hm⟩, h1⟩
    rw [hy1] at h1
    refine hx ⟨⟨m + ⌊x 0⌋, ?_⟩, h1⟩
    rw [hy0] at hm
    push_cast
    rw [hm, Int.fract_add_floor]
  have hq0 := _root_.GlobalTheory.Sieg.Model.ee_ne_zero (τ : ℂ)
  have hq := _root_.GlobalTheory.Sieg.Model.norm_ee_lt_one τ
  have hne := _root_.GlobalTheory.Sieg.Model.ne_one_of_not_int hy τ
  have ht0 := _root_.GlobalTheory.Sieg.Model.ee_ne_zero (_root_.GlobalTheory.Sieg.pt y τ)
  have hpt : _root_.GlobalTheory.Sieg.ee (_root_.GlobalTheory.Sieg.pt x τ) =
      _root_.GlobalTheory.Sieg.ee τ ^ ⌊x 0⌋ * _root_.GlobalTheory.Sieg.ee (_root_.GlobalTheory.Sieg.pt y τ) := by
    rw [← _root_.GlobalTheory.Sieg.DlogOne.ee_int_mul, ← _root_.GlobalTheory.Sieg.Model.ee_add]
    congr 1
    simp only [_root_.GlobalTheory.Sieg.pt, hy0, hy1, Int.fract]
    push_cast
    ring
  have hzt : ∀ j : ℤ, _root_.GlobalTheory.Sieg.ee τ ^ j *
      _root_.GlobalTheory.Sieg.ee (_root_.GlobalTheory.Sieg.pt y τ) ≠ 1 := by
    intro j hj
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg j
    · rw [zpow_natCast] at hj
      exact (hne m).1 (by rw [hj, sub_self])
    · rw [zpow_neg, zpow_natCast, inv_mul_eq_one₀ (pow_ne_zero _ hq0)] at hj
      exact (hne m).2 (by rw [← hj, mul_inv_cancel₀ (pow_ne_zero _ hq0), sub_self])
  have hF : _root_.GlobalTheory.Sieg.F 1 x τ = _root_.GlobalTheory.Sieg.F 1 y τ := by
    simp only [_root_.GlobalTheory.Sieg.F]
    congr 1
    · simp only [_root_.GlobalTheory.Sieg.f0, hy0, hy1, Int.fract_fract]
    · refine (tsum_congr fun p => ?_).trans
        (Equiv.tsum_eq (Equiv.prodCongr (Equiv.addRight ⌊x 0⌋) (Equiv.refl ℤ))
          (_root_.GlobalTheory.Sieg.fTerm 1 y τ))
      have key : x 0 + (p.1 : ℚ) = y 0 + ((p.1 + ⌊x 0⌋ : ℤ) : ℚ) := by
        rw [hy0, Int.fract]
        push_cast
        ring
      simp only [_root_.GlobalTheory.Sieg.fTerm, Equiv.prodCongr_apply, Equiv.coe_addRight,
        Equiv.coe_refl, Prod.map_apply, id_eq, hy1]
      rw [key]
      rfl
  have hbase := E_ee_pt_eq_neg_F_of_mem_Ico hy (Int.fract_nonneg _)
    (Int.fract_lt_one _) τ
  rw [hpt, E_zpow_mul_eq_sub hq hq0 ht0 hzt, hbase, hF, hy0]
  have hx0 : ((x 0 : ℚ) : ℂ) = ((Int.fract (x 0) : ℚ) : ℂ) + ((⌊x 0⌋ : ℤ) : ℂ) := by
    exact_mod_cast (Int.fract_add_floor (x 0)).symm
  rw [hx0]
  ring

end GlobalTheory.Sieg.DlogOne

namespace GlobalTheory.Sieg

open DlogOne

end GlobalTheory.Sieg
