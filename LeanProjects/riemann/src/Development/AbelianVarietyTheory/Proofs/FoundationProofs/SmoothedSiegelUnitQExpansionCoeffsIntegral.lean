import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelLinearOperations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelMulOfPosLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelCoeffAndFunctionUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.MultipliableAndSgNeZero

noncomputable section

open scoped UpperHalfPlane MatrixGroups Manifold Topology
open GlobalTheory.Sieg GlobalTheory.QFam Filter

namespace GlobalTheory.SiegQ

def tc (F : ℂ → ℂ) (n : ℕ) : ℂ := ((n.factorial : ℂ))⁻¹ * iteratedDeriv n F 0

def qv (M : ℕ) (τ : ℍ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * τ / M)

open scoped UpperHalfPlane MatrixGroups Manifold Topology in
open Filter in
theorem _root_.GlobalTheory.SiegQ.norm_qv_lt {M : ℕ} (hM : 0 < M) (τ : ℍ) : ‖_root_.GlobalTheory.SiegQ.qv M τ‖ < 1 := by
  rw [_root_.GlobalTheory.SiegQ.qv, Complex.norm_exp, ← Real.exp_zero, Real.exp_lt_exp]
  have hre : (2 * Real.pi * Complex.I * (τ : ℂ) / M).re = -(2 * Real.pi * τ.im / M) := by
    simp [Complex.div_natCast_re]; ring
  rw [hre]
  have := τ.im_pos
  have := Real.pi_pos
  have : (0 : ℝ) < M := by exact_mod_cast hM
  apply neg_neg_of_pos
  positivity

open scoped UpperHalfPlane MatrixGroups Manifold Topology in
open Filter in
theorem _root_.GlobalTheory.SiegQ.tc_zero (F : ℂ → ℂ) : _root_.GlobalTheory.SiegQ.tc F 0 = F 0 := by
  simp [_root_.GlobalTheory.SiegQ.tc]

open scoped UpperHalfPlane MatrixGroups Manifold Topology in
open Filter in
theorem _root_.GlobalTheory.SiegQ.hasQ_tc {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (Metric.ball 0 1)) {M : ℕ} (hM : 0 < M) :
    _root_.GlobalTheory.QFam.HasQ M (fun τ => F (_root_.GlobalTheory.SiegQ.qv M τ)) (_root_.GlobalTheory.SiegQ.tc F) := by
  unfold _root_.GlobalTheory.QFam.HasQ
  intro τ
  have hz : _root_.GlobalTheory.SiegQ.qv M τ ∈ Metric.ball (0 : ℂ) 1 := by
    simpa using _root_.GlobalTheory.SiegQ.norm_qv_lt hM τ
  have h := Complex.hasSum_taylorSeries_on_ball hF hz
  have heq : (fun n : ℕ => _root_.GlobalTheory.SiegQ.tc F n *
      Complex.exp (2 * Real.pi * Complex.I * n * τ / M)) =
      fun n : ℕ => (n.factorial : ℂ)⁻¹ • (_root_.GlobalTheory.SiegQ.qv M τ - 0) ^ n • iteratedDeriv n F 0 := by
    funext n
    have hexp : Complex.exp (2 * Real.pi * Complex.I * n * τ / M) = _root_.GlobalTheory.SiegQ.qv M τ ^ n := by
      rw [_root_.GlobalTheory.SiegQ.qv, ← Complex.exp_nat_mul]
      congr 1
      ring
    rw [hexp, _root_.GlobalTheory.SiegQ.tc, sub_zero, smul_eq_mul, smul_eq_mul]
    ring
  rw [heq]
  exact h

open scoped UpperHalfPlane MatrixGroups Manifold Topology in
open Filter in
theorem _root_.GlobalTheory.SiegQ.tc_congr {F G : ℂ → ℂ} (h : ∀ z : ℂ, ‖z‖ < 1 → F z = G z) :
    _root_.GlobalTheory.SiegQ.tc F = _root_.GlobalTheory.SiegQ.tc G := by
  funext n
  unfold _root_.GlobalTheory.SiegQ.tc
  congr 1
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with z hz
  exact h z (by simpa using hz)

open scoped UpperHalfPlane MatrixGroups Manifold Topology in
open Filter in
theorem _root_.GlobalTheory.SiegQ.tc_mul {F G : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (Metric.ball 0 1))
    (hG : DifferentiableOn ℂ G (Metric.ball 0 1)) :
    _root_.GlobalTheory.SiegQ.tc (fun z => F z * G z) =
      _root_.GlobalTheory.QFam.conv (_root_.GlobalTheory.SiegQ.tc F) (_root_.GlobalTheory.SiegQ.tc G) := by
  funext n
  have h0 : Metric.ball (0 : ℂ) 1 ∈ 𝓝 0 := Metric.ball_mem_nhds 0 one_pos
  have hF' : ContDiffAt ℂ n F 0 := (hF.contDiffOn Metric.isOpen_ball).contDiffAt h0
  have hG' : ContDiffAt ℂ n G 0 := (hG.contDiffOn Metric.isOpen_ball).contDiffAt h0
  simp only [_root_.GlobalTheory.SiegQ.tc, _root_.GlobalTheory.QFam.conv,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [show (fun z => F z * G z) = F * G from rfl, iteratedDeriv_mul hF' hG', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [Nat.cast_choose ℂ hi']
  have h1 : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have h2 : ((n - i).factorial : ℂ) ≠ 0 := by exact_mod_cast (n - i).factorial_ne_zero
  have h3 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

open scoped UpperHalfPlane MatrixGroups Manifold Topology in
open Filter in
theorem _root_.GlobalTheory.SiegQ.tc_const (c : ℂ) :
    _root_.GlobalTheory.SiegQ.tc (fun _ => c) = fun n => if n = 0 then c else 0 := by
  funext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [_root_.GlobalTheory.SiegQ.tc]
  · simp [_root_.GlobalTheory.SiegQ.tc, iteratedDeriv_const, hn.ne']

open scoped UpperHalfPlane MatrixGroups Manifold Topology in
open Filter in
theorem _root_.GlobalTheory.SiegQ.tc_lin (w : ℂ) (e : ℕ) :
    _root_.GlobalTheory.SiegQ.tc (fun z => 1 - w * z ^ e) =
      fun n => (if n = 0 then 1 else 0) - if n = e then w else 0 := by
  funext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rcases Nat.eq_zero_or_pos e with rfl | he
    · simp [_root_.GlobalTheory.SiegQ.tc]
    · simp [_root_.GlobalTheory.SiegQ.tc, he.ne', (Ne.symm he.ne')]
  · have h1 : iteratedDeriv n (fun z : ℂ => 1 - w * z ^ e) 0 =
        -(w * ((e.descFactorial n : ℂ) * 0 ^ (e - n))) := by
      rw [iteratedDeriv_const_sub hn, iteratedDeriv_neg, iteratedDeriv_const_mul_field,
        iteratedDeriv_pow]
    rw [_root_.GlobalTheory.SiegQ.tc, h1, if_neg hn.ne']
    rcases lt_trichotomy n e with h | rfl | h
    · simp [h.ne, Nat.sub_ne_zero_of_lt h]
    · have : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
      simp [Nat.descFactorial_self]
      field_simp
    · simp [h.ne', Nat.descFactorial_eq_zero_iff_lt.mpr h]

def Good (R : Subring ℂ) (F : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ F (Metric.ball 0 1) ∧ ∀ n, tc F n ∈ R

variable {R : Subring ℂ}

theorem Good.const {c : ℂ} (hc : c ∈ R) : Good R fun _ => c :=
  ⟨differentiableOn_const c, fun n => by rw [tc_const]; dsimp only; split_ifs; exacts [hc, R.zero_mem]⟩

theorem Good.mul {F G : ℂ → ℂ} (hF : Good R F) (hG : Good R G) : Good R fun z => F z * G z :=
  ⟨hF.1.mul hG.1, fun n => by
    rw [tc_mul hF.1 hG.1]
    exact R.sum_mem fun p _ => R.mul_mem (hF.2 _) (hG.2 _)⟩

theorem Good.pow {F : ℂ → ℂ} (hF : Good R F) (k : ℕ) : Good R fun z => F z ^ k := by
  induction k with
  | zero => simpa using Good.const R.one_mem
  | succ k ih => simpa [pow_succ] using ih.mul hF

theorem Good.prod {ι : Type} (s : Finset ι) {F : ι → ℂ → ℂ} (hF : ∀ i ∈ s, Good R (F i)) :
    Good R fun z => ∏ i ∈ s, F i z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Good.const R.one_mem
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (hF i (by simp)).mul (ih fun j hj => hF j (by simp [hj]))

theorem Good.lin {w : ℂ} (hw : w ∈ R) (e : ℕ) : Good R fun z => 1 - w * z ^ e :=
  ⟨by fun_prop, fun n => by
    rw [tc_lin]
    refine R.sub_mem ?_ ?_ <;> split_ifs
    exacts [R.one_mem, R.zero_mem, hw, R.zero_mem]⟩

theorem Good.inv {F : ℂ → ℂ} (hF : Good R F) (h0 : ∀ z : ℂ, ‖z‖ < 1 → F z ≠ 0) (hi : (F 0)⁻¹ ∈ R) :
    Good R fun z => (F z)⁻¹ := by
  have hd : DifferentiableOn ℂ (fun z => (F z)⁻¹) (Metric.ball 0 1) :=
    hF.1.inv fun z hz => h0 z (by simpa using hz)
  refine ⟨hd, fun n => ?_⟩
  have hc : conv (tc F) (tc fun z => (F z)⁻¹) = fun n => if n = 0 then 1 else 0 := by
    rw [← tc_mul hF.1 hd, ← tc_const]
    exact tc_congr fun z hz => mul_inv_cancel₀ (h0 z hz)
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simpa [tc_zero] using hi
    · have h := congrFun hc (n + 1)
      simp only [conv, Finset.Nat.antidiagonal_succ, Finset.sum_cons, Finset.sum_map, tc_zero,
        Nat.succ_ne_zero, if_false] at h
      have h1 := h0 0 (by simp)
      have : tc (fun z => (F z)⁻¹) (n + 1) = -(F 0)⁻¹ * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
          tc F (p.1 + 1) * tc (fun z => (F z)⁻¹) p.2 := by
        have h' : F 0 * tc (fun z => (F z)⁻¹) (n + 1) + ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
          tc F (p.1 + 1) * tc (fun z => (F z)⁻¹) p.2 = 0 := by simpa using h
        apply mul_left_cancel₀ h1
        rw [← mul_assoc, mul_neg, mul_inv_cancel₀ h1]
        linear_combination h'
      rw [this]
      refine R.mul_mem (R.neg_mem hi) (R.sum_mem fun p hp => R.mul_mem (hF.2 _) (ih _ ?_))
      have := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      omega

theorem tc_mul_lin {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (Metric.ball 0 1)) (w : ℂ) {e n : ℕ}
    (h : n < e) : tc (fun z => F z * (1 - w * z ^ e)) n = tc F n := by
  rw [tc_mul hF (by fun_prop), tc_lin, conv, Finset.sum_eq_single (n, 0)]
  · simp [show (0 : ℕ) ≠ e by omega]
  · intro p hp hne
    have := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have h2 : p.2 ≠ 0 := fun h2 => hne (Prod.ext (by simp; omega) h2)
    simp [h2, show p.2 ≠ e by omega]
  · simp

open scoped UpperHalfPlane MatrixGroups Manifold Topology in
open Filter in
variable {R : Subring ℂ} in
theorem _root_.GlobalTheory.SiegQ.tendsto_iteratedDeriv {F : ℕ → ℂ → ℂ} {G : ℂ → ℂ} (n : ℕ)
    (h : TendstoLocallyUniformlyOn F G atTop (Metric.ball 0 1))
    (hd : ∀ N, DifferentiableOn ℂ (F N) (Metric.ball 0 1)) :
    Tendsto (fun N => iteratedDeriv n (F N) 0) atTop (𝓝 (iteratedDeriv n G 0)) := by
  induction n generalizing F G with
  | zero => simpa using h.tendsto_at (Metric.mem_ball_self one_pos)
  | succ n ih =>
    simp only [iteratedDeriv_succ']
    exact ih (h.deriv (Eventually.of_forall hd) Metric.isOpen_ball)
      (fun N => (hd N).deriv Metric.isOpen_ball)

def ep (M : ℕ) (w : ℂ) (e : ℕ) (z : ℂ) : ℂ := ∏' m : ℕ, (1 - w * z ^ (e + m * M))

open scoped UpperHalfPlane MatrixGroups Manifold Topology in
open Filter in
variable {R : Subring ℂ} in
theorem _root_.GlobalTheory.SiegQ.norm_term_le {M : ℕ} (hM : 0 < M) {w : ℂ} (hw : ‖w‖ ≤ 1) {e : ℕ}
    (he : 0 < e) {z : ℂ} {r : ℝ}
    (hz : ‖z‖ ≤ r) (hr : r < 1) (m : ℕ) : ‖-(w * z ^ (e + m * M))‖ ≤ r ^ (m + 1) := by
  have hr0 : 0 ≤ r := (norm_nonneg z).trans hz
  have hm : m + 1 ≤ e + m * M := by
    have := Nat.le_mul_of_pos_right m hM
    omega
  rw [norm_neg, norm_mul, norm_pow]
  calc ‖w‖ * ‖z‖ ^ (e + m * M) ≤ 1 * r ^ (e + m * M) := by gcongr
    _ ≤ r ^ (m + 1) := by rw [one_mul]; exact pow_le_pow_of_le_one hr0 hr.le hm

theorem summable_term {M : ℕ} (hM : 0 < M) {w : ℂ} (hw : ‖w‖ ≤ 1) {e : ℕ} (he : 0 < e) {z : ℂ}
    (hz : ‖z‖ < 1) : Summable fun m : ℕ => ‖-(w * z ^ (e + m * M))‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_term_le hM hw he le_rfl hz)
    ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg _) hz))

open scoped UpperHalfPlane MatrixGroups Manifold Topology in
open Filter in
variable {R : Subring ℂ} in
theorem _root_.GlobalTheory.SiegQ.hasProd_ep {M : ℕ} (hM : 0 < M) {w : ℂ} (hw : ‖w‖ ≤ 1)
    {e : ℕ} (he : 0 < e) {z : ℂ} (hz : ‖z‖ < 1) :
    HasProd (fun m : ℕ => 1 - w * z ^ (e + m * M)) (_root_.GlobalTheory.SiegQ.ep M w e z) := by
  have hs : Summable fun m : ℕ => ‖-(w * z ^ (e + m * M))‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun m => _root_.GlobalTheory.SiegQ.norm_term_le hM hw he le_rfl hz m)
      ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg _) hz))
  have hm := multipliable_one_add_of_summable hs
  simp only [← sub_eq_add_neg] at hm
  exact hm.hasProd

open scoped UpperHalfPlane MatrixGroups Manifold Topology in
open Filter in
variable {R : Subring ℂ} in
theorem _root_.GlobalTheory.SiegQ.lin_ne_zero {w : ℂ} (hw : ‖w‖ ≤ 1) {e : ℕ} (he : 0 < e) {z : ℂ}
    (hz : ‖z‖ < 1) : 1 - w * z ^ e ≠ 0 := by
  intro h
  have h1 : ‖w * z ^ e‖ < 1 := by
    rw [norm_mul, norm_pow]
    calc ‖w‖ * ‖z‖ ^ e ≤ 1 * ‖z‖ ^ e := by gcongr
      _ < 1 := by rw [one_mul]; exact pow_lt_one₀ (norm_nonneg _) hz he.ne'
  have h2 : w * z ^ e = 1 := by linear_combination -h
  rw [h2, norm_one] at h1
  exact lt_irrefl _ h1

open scoped UpperHalfPlane MatrixGroups Manifold Topology in
open Filter in
variable {R : Subring ℂ} in
theorem _root_.GlobalTheory.SiegQ.ep_ne_zero {M : ℕ} (hM : 0 < M) {w : ℂ} (hw : ‖w‖ ≤ 1) {e : ℕ}
    (he : 0 < e) {z : ℂ}
    (hz : ‖z‖ < 1) : _root_.GlobalTheory.SiegQ.ep M w e z ≠ 0 := by
  rcases eq_or_ne z 0 with rfl | hz0
  · have h : ∀ m : ℕ, (1 : ℂ) - w * 0 ^ (e + m * M) = 1 := fun m => by
      simp [zero_pow (by omega : e + m * M ≠ 0)]
    simp only [_root_.GlobalTheory.SiegQ.ep, h, tprod_one]
    exact one_ne_zero
  have hq : z ^ M ≠ 0 := pow_ne_zero _ hz0
  have hfac : ∀ m : ℕ, (z ^ M) ^ (m + 1) * (w * z ^ e * (z ^ M)⁻¹) = w * z ^ (e + m * M) := by
    intro m
    rw [pow_succ, pow_add, mul_comm m M, pow_mul]
    field_simp
  have hqn : ‖z ^ M‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hz hM.ne'
  obtain ⟨P, hP, hprod⟩ := _root_.GlobalTheory.Sieg.Model.hasProd_geom hqn (w * z ^ e * (z ^ M)⁻¹)
    (fun m => by rw [hfac]; exact _root_.GlobalTheory.SiegQ.lin_ne_zero hw (by omega) hz)
  simp only [hfac] at hprod
  rw [_root_.GlobalTheory.SiegQ.ep, hprod.tprod_eq]
  exact hP

open scoped UpperHalfPlane MatrixGroups Manifold Topology in
open Filter in
variable {R : Subring ℂ} in
theorem _root_.GlobalTheory.SiegQ.ep_zero (M : ℕ) (w : ℂ) {e : ℕ} (he : 0 < e) :
    _root_.GlobalTheory.SiegQ.ep M w e 0 = 1 := by
  unfold _root_.GlobalTheory.SiegQ.ep
  have h : ∀ m : ℕ, (1 : ℂ) - w * 0 ^ (e + m * M) = 1 := fun m => by
    simp [zero_pow (by omega : e + m * M ≠ 0)]
  simp only [h, tprod_one]

open scoped UpperHalfPlane MatrixGroups Manifold Topology in
open Filter in
variable {R : Subring ℂ} in
theorem _root_.GlobalTheory.SiegQ.ep_locUnif {M : ℕ} (hM : 0 < M) {w : ℂ}
    (hw : ‖w‖ ≤ 1) {e : ℕ} (he : 0 < e) :
    HasProdLocallyUniformlyOn (fun (m : ℕ) (z : ℂ) => 1 - w * z ^ (e + m * M))
      (_root_.GlobalTheory.SiegQ.ep M w e) (Metric.ball 0 1) := by
  apply hasProdLocallyUniformlyOn_of_forall_compact Metric.isOpen_ball
  intro K hK hKc
  obtain ⟨r', hr', hKr⟩ := exists_lt_subset_ball hKc.isClosed hK
  have hr1 : max r' 0 < 1 := max_lt hr' one_pos
  have hsum : Summable (fun m : ℕ => max r' 0 ^ (m + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (le_max_right _ _) hr1)
  have h := Summable.hasProdUniformlyOn_nat_one_add
    (f := fun (m : ℕ) (z : ℂ) => -(w * z ^ (e + m * M))) hKc hsum
    (Eventually.of_forall fun m z hz => _root_.GlobalTheory.SiegQ.norm_term_le hM hw he
      ((mem_ball_zero_iff.mp (hKr hz)).le.trans (le_max_left _ _)) hr1 m)
    (fun m => by fun_prop)
  convert h using 1
  · funext m z
    ring
  · funext z
    simp [_root_.GlobalTheory.SiegQ.ep, sub_eq_add_neg]

open scoped UpperHalfPlane MatrixGroups Manifold Topology in
open Filter in
variable {R : Subring ℂ} in
private theorem good_const_foundation {c : ℂ} (hc : c ∈ R) : _root_.GlobalTheory.SiegQ.Good R (fun _ => c) := by
  refine ⟨differentiableOn_const c, fun n => ?_⟩
  rw [_root_.GlobalTheory.SiegQ.tc_const]
  dsimp only
  split_ifs
  · exact hc
  · exact R.zero_mem

open scoped UpperHalfPlane MatrixGroups Manifold Topology in
open Filter in
variable {R : Subring ℂ} in
private theorem good_mul' {F G : ℂ → ℂ} (hF : _root_.GlobalTheory.SiegQ.Good R F)
    (hG : _root_.GlobalTheory.SiegQ.Good R G) : _root_.GlobalTheory.SiegQ.Good R (fun z => F z * G z) := by
  refine ⟨hF.1.mul hG.1, fun n => ?_⟩
  rw [_root_.GlobalTheory.SiegQ.tc_mul hF.1 hG.1]
  unfold _root_.GlobalTheory.QFam.conv
  exact R.sum_mem fun p _ => R.mul_mem (hF.2 _) (hG.2 _)

open scoped UpperHalfPlane MatrixGroups Manifold Topology in
open Filter in
variable {R : Subring ℂ} in
private theorem good_finset_prod {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ}
    (h : ∀ i ∈ s, _root_.GlobalTheory.SiegQ.Good R (f i)) :
    _root_.GlobalTheory.SiegQ.Good R (fun z => ∏ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using good_const_foundation (R := R) R.one_mem
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact good_mul' (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

open scoped UpperHalfPlane MatrixGroups Manifold Topology in
open Filter in
variable {R : Subring ℂ} in
private theorem good_one_sub_mul_pow {w : ℂ} (hw : w ∈ R) (e : ℕ) :
    _root_.GlobalTheory.SiegQ.Good R (fun z => 1 - w * z ^ e) := by
  refine ⟨Differentiable.differentiableOn (by fun_prop), fun n => ?_⟩
  rw [_root_.GlobalTheory.SiegQ.tc_lin]
  dsimp only
  refine R.sub_mem ?_ ?_
  · split_ifs
    · exact R.one_mem
    · exact R.zero_mem
  · split_ifs
    · exact hw
    · exact R.zero_mem

open scoped UpperHalfPlane MatrixGroups Manifold Topology in
open Filter in
variable {R : Subring ℂ} in
private theorem conv_one_sub_monomial_of_lt (b : ℕ → ℂ) (w : ℂ) {k n : ℕ} (hk : n < k) :
    _root_.GlobalTheory.QFam.conv b (fun j => (if j = 0 then 1 else 0) - if j = k then w else 0) n =
      b n := by
  unfold _root_.GlobalTheory.QFam.conv
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_eq_single n]
  · simp [show (0 : ℕ) ≠ k by omega]
  · intro i hi hin
    have hi' := Finset.mem_range.mp hi
    have h1 : n - i ≠ 0 := by omega
    have h2 : n - i ≠ k := by omega
    simp [h1, h2]
  · intro h
    simp at h

open scoped UpperHalfPlane MatrixGroups Manifold Topology in
open Filter in
variable {R : Subring ℂ} in
theorem _root_.GlobalTheory.SiegQ.Good.ep {M : ℕ}
    (hM : 0 < M) {w : ℂ} (hw : ‖w‖ ≤ 1) (hR : w ∈ R) {e : ℕ} (he : 0 < e) :
    _root_.GlobalTheory.SiegQ.Good R (_root_.GlobalTheory.SiegQ.ep M w e) := by
  have hloc := (_root_.GlobalTheory.SiegQ.ep_locUnif hM hw he
    ).tendstoLocallyUniformlyOn_finsetRange
  have hpart : ∀ N, _root_.GlobalTheory.SiegQ.Good R
      (fun z => ∏ i ∈ Finset.range N, (1 - w * z ^ (e + i * M))) :=
    fun N => good_finset_prod _ fun i _ => good_one_sub_mul_pow hR _
  refine ⟨hloc.differentiableOn (Eventually.of_forall fun N => (hpart N).1) Metric.isOpen_ball,
    fun n => ?_⟩
  have hstab : ∀ N, n + 1 ≤ N →
      _root_.GlobalTheory.SiegQ.tc (fun z => ∏ i ∈ Finset.range N, (1 - w * z ^ (e + i * M))) n =
        _root_.GlobalTheory.SiegQ.tc
          (fun z => ∏ i ∈ Finset.range (n + 1), (1 - w * z ^ (e + i * M))) n := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => rfl
    | succ N hN ih =>
      rw [← ih]
      simp only [Finset.prod_range_succ]
      rw [_root_.GlobalTheory.SiegQ.tc_mul (hpart N).1 (good_one_sub_mul_pow hR _).1,
        _root_.GlobalTheory.SiegQ.tc_lin]
      have := Nat.le_mul_of_pos_right N hM
      exact conv_one_sub_monomial_of_lt _ w (by omega)
  have ht := _root_.GlobalTheory.SiegQ.tendsto_iteratedDeriv n hloc (fun N => (hpart N).1)
  have hlim : _root_.GlobalTheory.SiegQ.tc (_root_.GlobalTheory.SiegQ.ep M w e) n =
      _root_.GlobalTheory.SiegQ.tc
        (fun z => ∏ i ∈ Finset.range (n + 1), (1 - w * z ^ (e + i * M))) n := by
    unfold _root_.GlobalTheory.SiegQ.tc at hstab ⊢
    refine tendsto_nhds_unique (ht.const_mul ((n.factorial : ℂ)⁻¹))
      (tendsto_const_nhds.congr' ?_)
    filter_upwards [eventually_ge_atTop (n + 1)] with N hN
    exact (hstab N hN).symm
  rw [hlim]
  exact (hpart _).2 n

def kk (c : ℕ) : ℤ := ((c : ℤ) - (c : ℤ) ^ 2) / 2

def expo (c M a : ℕ) : ℤ :=
  (M * ((c ^ 2 - 1) / 12) : ℕ) + a * kk c + (∑ m ∈ Finset.range (c * a / M), (c * a - (m + 1) * M) : ℕ)

def unitPart (c M a : ℕ) (v z : ℂ) : ℂ :=
  (-v) ^ kk c * ((1 - v * z ^ a) ^ (c ^ 2) * (1 - v ^ c * z ^ (c * a))⁻¹) *
    (ep M v (M + a) z ^ (c ^ 2) * ep M v⁻¹ (M - a) z ^ (c ^ 2) * (ep M (v ^ c) (M + c * a) z)⁻¹ *
      ((∏ m ∈ Finset.range (c * a / M), -v ^ c * (1 - v ^ c * z ^ (c * a - (m + 1) * M))⁻¹) *
        (ep M (v ^ c)⁻¹ ((c * a / M + 1) * M - c * a) z)⁻¹))

theorem lt_succ_div_mul {M : ℕ} (hM : 0 < M) (k : ℕ) : k < (k / M + 1) * M := by
  have := Nat.lt_div_mul_add (a := k) hM
  linarith

open scoped UpperHalfPlane MatrixGroups Manifold Topology in
open Filter in
variable {R : Subring ℂ} in
private theorem inv_one_sub_inv_eq_neg_mul_inv_one_sub {x : ℂ} (hx : x ≠ 0) : (1 - x⁻¹)⁻¹ = -x * (1 - x)⁻¹ := by
  rw [show (1 : ℂ) - x⁻¹ = (x - 1) / x by field_simp, inv_div, div_eq_mul_inv,
    show x - 1 = -(1 - x) by ring, inv_neg]
  ring

open scoped UpperHalfPlane MatrixGroups Manifold Topology in
open Filter in
variable {R : Subring ℂ} in
theorem _root_.GlobalTheory.SiegQ.cth_eq {c M a : ℕ} (hM : 0 < M) (ha : a < M) {v z : ℂ}
    (hv : ‖v‖ = 1) (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    _root_.GlobalTheory.Sieg.cth c (z ^ M) (z ^ a * v) =
      z ^ _root_.GlobalTheory.SiegQ.expo c M a * _root_.GlobalTheory.SiegQ.unitPart c M a v z := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp at hv
  have hnv1 : ‖v⁻¹‖ ≤ 1 := by rw [norm_inv, hv, inv_one]
  have hnvc : ‖v ^ c‖ ≤ 1 := by rw [norm_pow, hv, one_pow]
  have hnvc' : ‖(v ^ c)⁻¹‖ ≤ 1 := by rw [norm_inv, norm_pow, hv, one_pow, inv_one]
  have hlt : c * a < (c * a / M + 1) * M := by
    have := Nat.lt_div_mul_add (a := c * a) hM
    rw [add_mul, one_mul]
    omega
  have hE : 0 < (c * a / M + 1) * M - c * a := by omega
  have hA := _root_.GlobalTheory.SiegQ.hasProd_ep hM hv.le (by omega : 0 < M + a) hz
  have hB := _root_.GlobalTheory.SiegQ.hasProd_ep hM hnv1 (by omega : 0 < M - a) hz
  have hC := _root_.GlobalTheory.SiegQ.hasProd_ep hM hnvc (by omega : 0 < M + c * a) hz
  have hD := _root_.GlobalTheory.SiegQ.hasProd_ep hM hnvc' hE hz
  have hC0 := _root_.GlobalTheory.SiegQ.ep_ne_zero hM hnvc (by omega : 0 < M + c * a) hz
  have hD0 := _root_.GlobalTheory.SiegQ.ep_ne_zero hM hnvc' hE hz
  obtain ⟨D, hDdef⟩ : ∃ D : ℕ → ℂ, D = fun m => 1 - (z ^ M) ^ (m + 1) * ((z ^ a * v) ^ c)⁻¹ :=
    ⟨_, rfl⟩
  have hDshift : ∀ j, D (j + c * a / M) =
      1 - (v ^ c)⁻¹ * z ^ ((c * a / M + 1) * M - c * a + j * M) := by
    intro j
    rw [hDdef]
    dsimp only
    congr 1
    have h1 : (j + c * a / M + 1) * M = j * M + (c * a / M + 1) * M := by ring
    have hexp : M * (j + c * a / M + 1) = ((c * a / M + 1) * M - c * a + j * M) + c * a := by
      rw [mul_comm, h1]
      omega
    rw [← pow_mul, mul_pow, ← pow_mul, hexp, pow_add, mul_comm a c]
    field_simp
  have hDinv : HasProd (fun m => (D m)⁻¹) ((∏ i ∈ Finset.range (c * a / M), (D i)⁻¹) *
      (_root_.GlobalTheory.SiegQ.ep M (v ^ c)⁻¹ ((c * a / M + 1) * M - c * a) z)⁻¹) := by
    apply HasProd.prod_range_mul
    simp only [hDshift]
    exact hD.inv₀ hD0
  have hfin : ∀ i ∈ Finset.range (c * a / M), (D i)⁻¹ =
      (-v ^ c * (1 - v ^ c * z ^ (c * a - (i + 1) * M))⁻¹) * z ^ (c * a - (i + 1) * M) := by
    intro i hi
    have hi' : (i + 1) * M ≤ c * a := (Nat.le_div_iff_mul_le hM).mp (Finset.mem_range.mp hi)
    have hx : D i = 1 - (v ^ c * z ^ (c * a - (i + 1) * M))⁻¹ := by
      rw [hDdef]
      dsimp only
      congr 1
      have hsplit : z ^ (a * c) = z ^ (M * (i + 1)) * z ^ (c * a - (i + 1) * M) := by
        rw [← pow_add]
        congr 1
        rw [mul_comm a c, mul_comm M (i + 1)]
        omega
      rw [← pow_mul, mul_pow, ← pow_mul, hsplit]
      field_simp
    rw [hx, inv_one_sub_inv_eq_neg_mul_inv_one_sub (mul_ne_zero (pow_ne_zero _ hv0) (pow_ne_zero _ hz0))]
    ring
  have hF : HasProd (fun m => _root_.GlobalTheory.Sieg.cthFac c (z ^ M) (z ^ a * v) (m + 1))
      (_root_.GlobalTheory.SiegQ.ep M v (M + a) z ^ (c ^ 2) *
        _root_.GlobalTheory.SiegQ.ep M v⁻¹ (M - a) z ^ (c ^ 2) *
        (_root_.GlobalTheory.SiegQ.ep M (v ^ c) (M + c * a) z)⁻¹ *
        ((∏ i ∈ Finset.range (c * a / M), (D i)⁻¹) *
          (_root_.GlobalTheory.SiegQ.ep M (v ^ c)⁻¹ ((c * a / M + 1) * M - c * a) z)⁻¹)) := by
    have h := (((hA.pow (c ^ 2)).mul (hB.pow (c ^ 2))).mul (hC.inv₀ hC0)).mul hDinv
    convert h using 1
    funext m
    have e1 : (z ^ M) ^ (m + 1) * (z ^ a * v) = v * z ^ (M + a + m * M) := by
      rw [← pow_mul, show M + a + m * M = M * (m + 1) + a by ring, pow_add]
      ring
    have e2 : (z ^ M) ^ (m + 1) * (z ^ a * v)⁻¹ = v⁻¹ * z ^ (M - a + m * M) := by
      have h1 : M * (m + 1) = m * M + M := by ring
      have h2 : M * (m + 1) = (M - a + m * M) + a := by omega
      rw [← pow_mul, h2, pow_add]
      field_simp
    have e3 : (z ^ M) ^ (m + 1) * (z ^ a * v) ^ c = v ^ c * z ^ (M + c * a + m * M) := by
      rw [← pow_mul, mul_pow, ← pow_mul, show M + c * a + m * M = M * (m + 1) + a * c by ring,
        pow_add]
      ring
    simp only [_root_.GlobalTheory.Sieg.cthFac]
    rw [e1, e2, e3, hDdef]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have hu : (-(z ^ a * v)) ^ (((c : ℤ) - (c : ℤ) ^ 2) / 2) =
      z ^ ((a : ℤ) * (((c : ℤ) - (c : ℤ) ^ 2) / 2)) * (-v) ^ (((c : ℤ) - (c : ℤ) ^ 2) / 2) := by
    rw [show -(z ^ a * v) = z ^ a * (-v) by ring, mul_zpow, zpow_mul, zpow_natCast]
  have e4 : (z ^ a * v) ^ c = v ^ c * z ^ (c * a) := by
    rw [mul_pow, ← pow_mul, mul_comm a c]
    ring
  rw [_root_.GlobalTheory.Sieg.cth, hF.tprod_eq, Finset.prod_congr rfl hfin, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hu, e4, _root_.GlobalTheory.SiegQ.expo, _root_.GlobalTheory.SiegQ.unitPart,
    zpow_add₀ hz0, zpow_add₀ hz0, zpow_natCast, zpow_natCast, ← pow_mul]
  simp only [_root_.GlobalTheory.SiegQ.kk, Nat.cast_mul]
  ring

theorem dvd_of_mem {c M a m : ℕ} (hm : m ∈ Finset.range (c * a / M)) (h : c * a - (m + 1) * M = 0) :
    0 < a ∧ M ∣ c * a := by
  have hm0 := Finset.mem_range.mp hm
  have hm' : (m + 1) * M ≤ c * a :=
    (Nat.mul_le_mul_right M hm0).trans (Nat.div_mul_le_self _ _)
  refine ⟨Nat.pos_of_ne_zero ?_, ⟨m + 1, by rw [mul_comm M]; omega⟩⟩
  rintro rfl
  simp at hm0

open scoped UpperHalfPlane MatrixGroups Manifold Topology in
open Filter in
variable {R : Subring ℂ} in
private theorem good_inv_of_ne_zero {F : ℂ → ℂ} (hF : _root_.GlobalTheory.SiegQ.Good R F)
    (h0 : ∀ z : ℂ, ‖z‖ < 1 → F z ≠ 0) (hu : (F 0)⁻¹ ∈ R) :
    _root_.GlobalTheory.SiegQ.Good R (fun z => (F z)⁻¹) := by
  have hd : DifferentiableOn ℂ (fun z => (F z)⁻¹) (Metric.ball 0 1) :=
    hF.1.inv fun z hz => h0 z (by simpa using hz)
  have hF0 : F 0 ≠ 0 := h0 0 (by simp)
  have hprod : _root_.GlobalTheory.SiegQ.tc (fun z => F z * (F z)⁻¹) = fun n => if n = 0 then 1 else 0 := by
    rw [_root_.GlobalTheory.SiegQ.tc_congr (G := fun _ => (1 : ℂ))
      (fun z hz => mul_inv_cancel₀ (h0 z hz)), _root_.GlobalTheory.SiegQ.tc_const]
  have hm := _root_.GlobalTheory.SiegQ.tc_mul hF.1 hd
  rw [hm] at hprod
  refine ⟨hd, fun n => ?_⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hn := congr_fun hprod n
    unfold _root_.GlobalTheory.QFam.conv at hn
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ'] at hn
    simp only [Nat.sub_zero, _root_.GlobalTheory.SiegQ.tc_zero] at hn
    have hrec : _root_.GlobalTheory.SiegQ.tc (fun z => (F z)⁻¹) n = (F 0)⁻¹ *
        ((if n = 0 then 1 else 0) - ∑ i ∈ Finset.range n, _root_.GlobalTheory.SiegQ.tc F (i + 1) *
          _root_.GlobalTheory.SiegQ.tc (fun z => (F z)⁻¹) (n - (i + 1))) := by
      rw [← hn]
      field_simp
      ring
    rw [hrec]
    refine R.mul_mem hu (R.sub_mem ?_ (R.sum_mem fun i hi => R.mul_mem (hF.2 _) (ih _ ?_)))
    · split_ifs
      · exact R.one_mem
      · exact R.zero_mem
    · have := Finset.mem_range.mp hi
      omega

open scoped UpperHalfPlane MatrixGroups Manifold Topology in
open Filter in
variable {R : Subring ℂ} in
private theorem good_pow' {F : ℂ → ℂ} (hF : _root_.GlobalTheory.SiegQ.Good R F) (n : ℕ) :
    _root_.GlobalTheory.SiegQ.Good R (fun z => F z ^ n) := by
  induction n with
  | zero => simpa using good_const_foundation (R := R) R.one_mem
  | succ n ih => simpa [pow_succ] using good_mul' ih hF

open scoped UpperHalfPlane MatrixGroups Manifold Topology in
open Filter in
variable {R : Subring ℂ} in
theorem _root_.GlobalTheory.SiegQ.good_unitPart {c M a : ℕ} (hc : 0 < c) (hM : 0 < M)
    (ha : a < M) {v : ℂ} (hv : ‖v‖ = 1)
    (h1 : v ∈ R) (h2 : v⁻¹ ∈ R) (h3 : a = 0 → (1 - v) ^ (c ^ 2) * (1 - v ^ c)⁻¹ ∈ R)
    (h4 : 0 < a → M ∣ c * a → v ^ c ≠ 1 ∧ (1 - v ^ c)⁻¹ ∈ R) :
    _root_.GlobalTheory.SiegQ.Good R (_root_.GlobalTheory.SiegQ.unitPart c M a v) := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp at hv
  have hn1 : ‖v‖ ≤ 1 := hv.le
  have hn2 : ‖v⁻¹‖ ≤ 1 := by rw [norm_inv, hv, inv_one]
  have hn3 : ‖v ^ c‖ ≤ 1 := by rw [norm_pow, hv, one_pow]
  have hn4 : ‖(v ^ c)⁻¹‖ ≤ 1 := by rw [norm_inv, norm_pow, hv, one_pow, inv_one]
  have hvc : v ^ c ∈ R := R.pow_mem h1 c
  have hvc' : (v ^ c)⁻¹ ∈ R := by
    rw [← inv_pow]
    exact R.pow_mem h2 c
  have hlt : c * a < (c * a / M + 1) * M := by
    have := Nat.lt_div_mul_add (a := c * a) hM
    rw [add_mul, one_mul]
    omega
  have hE : 0 < (c * a / M + 1) * M - c * a := by omega
  have hep : ∀ {w : ℂ} {e : ℕ}, ‖w‖ ≤ 1 → w ∈ R → 0 < e →
      _root_.GlobalTheory.SiegQ.Good R (_root_.GlobalTheory.SiegQ.ep M w e) :=
    fun hw hwR he =>
      _root_.GlobalTheory.SiegQ.Good.ep hM hw hwR he
  have hepinv : ∀ {w : ℂ} {e : ℕ}, ‖w‖ ≤ 1 → w ∈ R → 0 < e →
      _root_.GlobalTheory.SiegQ.Good R (fun z => (_root_.GlobalTheory.SiegQ.ep M w e z)⁻¹) :=
    fun hw hwR he => good_inv_of_ne_zero (hep hw hwR he)
      (fun z hz => _root_.GlobalTheory.SiegQ.ep_ne_zero hM hw he hz)
      (by rw [_root_.GlobalTheory.SiegQ.ep_zero M _ he, inv_one]; exact R.one_mem)
  have hzpow : (-v) ^ _root_.GlobalTheory.SiegQ.kk c ∈ R := by
    rcases Int.eq_nat_or_neg (_root_.GlobalTheory.SiegQ.kk c) with ⟨n, hn | hn⟩
    · rw [hn, zpow_natCast]
      exact R.pow_mem (R.neg_mem h1) n
    · rw [hn, zpow_neg, zpow_natCast, ← inv_pow, inv_neg]
      exact R.pow_mem (R.neg_mem h2) n
  have hfirst : _root_.GlobalTheory.SiegQ.Good R
      (fun z => (1 - v * z ^ a) ^ (c ^ 2) * (1 - v ^ c * z ^ (c * a))⁻¹) := by
    rcases Nat.eq_zero_or_pos a with rfl | ha0
    · simp only [pow_zero, mul_one, mul_zero]
      exact good_const_foundation (h3 rfl)
    · have hca : c * a ≠ 0 := by positivity
      refine good_mul' (good_pow' (good_one_sub_mul_pow h1 a) _)
        (good_inv_of_ne_zero (good_one_sub_mul_pow hvc _)
          (fun z hz => _root_.GlobalTheory.SiegQ.lin_ne_zero hn3 (by positivity) hz) ?_)
      simp [zero_pow hca, R.one_mem]
  have hfin : _root_.GlobalTheory.SiegQ.Good R (fun z => ∏ m ∈ Finset.range (c * a / M),
      -v ^ c * (1 - v ^ c * z ^ (c * a - (m + 1) * M))⁻¹) := by
    refine good_finset_prod _ fun m hm => good_mul' (good_const_foundation (R.neg_mem hvc)) ?_
    rcases Nat.eq_zero_or_pos (c * a - (m + 1) * M) with h0 | h0
    · rw [h0]
      simp only [pow_zero, mul_one]
      have ha0 : 0 < a := by
        rcases Nat.eq_zero_or_pos a with rfl | ha0
        · simp at hm
        · exact ha0
      have hle : (m + 1) * M ≤ c * a := (Nat.le_div_iff_mul_le hM).mp (Finset.mem_range.mp hm)
      have heq : c * a = (m + 1) * M := by omega
      exact good_const_foundation (h4 ha0 ⟨m + 1, by rw [heq, mul_comm]⟩).2
    · refine good_inv_of_ne_zero (good_one_sub_mul_pow hvc _)
        (fun z hz => _root_.GlobalTheory.SiegQ.lin_ne_zero hn3 h0 hz) ?_
      simp [zero_pow h0.ne', R.one_mem]
  unfold _root_.GlobalTheory.SiegQ.unitPart
  refine good_mul' (good_mul' (good_const_foundation hzpow) hfirst) ?_
  refine good_mul' (good_mul' (good_mul' ?_ ?_) (hepinv hn3 hvc (by omega)))
    (good_mul' hfin (hepinv hn4 hvc' hE))
  · exact good_pow' (hep hn1 h1 (by omega)) _
  · exact good_pow' (hep hn2 h2 (by omega)) _

open scoped UpperHalfPlane MatrixGroups Manifold Topology in
open Filter in
variable {R : Subring ℂ} in
theorem _root_.GlobalTheory.SiegQ.unitPart_zero_ne {c M a : ℕ} (hc : 0 < c) (hM : 0 < M) (ha : a < M)
    {v : ℂ} (hv : v ≠ 0)
    (h : M ∣ c * a → v ^ c ≠ 1) : _root_.GlobalTheory.SiegQ.unitPart c M a v 0 ≠ 0 := by
  have hE : 0 < (c * a / M + 1) * M - c * a := by
    have := Nat.lt_div_mul_add (a := c * a) hM
    rw [add_mul, one_mul]
    omega
  have h1 := _root_.GlobalTheory.SiegQ.ep_zero M v (by omega : 0 < M + a)
  have h2 := _root_.GlobalTheory.SiegQ.ep_zero M v⁻¹ (by omega : 0 < M - a)
  have h3 := _root_.GlobalTheory.SiegQ.ep_zero M (v ^ c) (by positivity : 0 < M + c * a)
  have h4 := _root_.GlobalTheory.SiegQ.ep_zero M (v ^ c)⁻¹ hE
  simp only [_root_.GlobalTheory.SiegQ.unitPart, h1, h2, h3, h4, one_pow, inv_one, mul_one, one_mul]
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · exact zpow_ne_zero _ (neg_ne_zero.mpr hv)
  · rcases Nat.eq_zero_or_pos a with rfl | ha0
    · have hv1 : v ^ c ≠ 1 := h (by simp)
      have hv1' : v ≠ 1 := by
        rintro rfl
        simp at hv1
      simp only [mul_zero, pow_zero, mul_one]
      exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hv1')))
        (inv_ne_zero (sub_ne_zero.mpr (Ne.symm hv1)))
    · have hca : c * a ≠ 0 := by positivity
      simp [zero_pow ha0.ne', zero_pow hca]
  · rw [Finset.prod_ne_zero_iff]
    intro m hm
    refine mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ hv)) (inv_ne_zero ?_)
    rcases Nat.eq_zero_or_pos (c * a - (m + 1) * M) with h0 | h0
    · rw [h0, pow_zero, mul_one, sub_ne_zero]
      refine (h ?_).symm
      have hm' : m + 1 ≤ c * a / M := Finset.mem_range.mp hm
      have hle : (m + 1) * M ≤ c * a := (Nat.le_div_iff_mul_le hM).mp hm'
      have heq : c * a = (m + 1) * M := by omega
      exact ⟨m + 1, by rw [heq, mul_comm]⟩
    · rw [zero_pow h0.ne']
      simp

theorem cyclo_mem {c M : ℕ} (hc : 0 < c) (hM : 0 < M) (hcM : Nat.Coprime c M) {v : ℂ} (hv : v ^ M = 1)
    (h1 : v ^ c ≠ 1) (hR : v ∈ R) : (1 - v) ^ (c ^ 2) * (1 - v ^ c)⁻¹ ∈ R := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (v ^ c) ^ k = v := by
    obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_of_coprime 1 hcM hM.ne'
    refine ⟨k, ?_⟩
    have e : ∀ n : ℕ, v ^ n = v ^ (n % M) := fun n => by
      conv_lhs => rw [← Nat.div_add_mod n M, pow_add, pow_mul, hv, one_pow, one_mul]
    rw [← pow_mul, e, hk, ← e, pow_one]
  have h2 : 1 - v ^ c ≠ 0 := sub_ne_zero.mpr h1.symm
  have h3 : (1 - v) * (1 - v ^ c)⁻¹ = ∑ i ∈ Finset.range k, (v ^ c) ^ i := by
    have := mul_neg_geom_sum (v ^ c) k
    rw [hk] at this
    rw [← this]
    field_simp
  obtain ⟨j, hj⟩ : ∃ j, c ^ 2 = j + 1 := ⟨c ^ 2 - 1, by have := pow_pos hc 2; omega⟩
  rw [hj, pow_succ, mul_assoc, h3]
  exact R.mul_mem (R.pow_mem (R.sub_mem R.one_mem hR) _) (R.sum_mem fun i _ => R.pow_mem (R.pow_mem hR _) _)

open scoped UpperHalfPlane MatrixGroups Manifold Topology in
open Filter in
variable {R : Subring ℂ} in

theorem _root_.GlobalTheory.SiegQ.sg_expansion_int : ∀ (c M a : ℕ), 0 < M → a < M →
    ∃ k : ℤ, ∀ b : ℕ, _root_.GlobalTheory.Sieg.admitted c ![(a : ℚ) / M, (b : ℚ) / M] →
      ∃ A : ℕ → ℂ, _root_.GlobalTheory.QFam.HasQ M (fun τ => _root_.GlobalTheory.Sieg.sg c ![(a : ℚ) / M, (b : ℚ) / M] τ *
        _root_.GlobalTheory.Sieg.ee (-((k : ℂ) / M) * (τ : ℂ))) A ∧ A 0 ≠ 0 ∧
        (∀ n, A n ∈ IntermediateField.adjoin ℚ {_root_.GlobalTheory.Sieg.ee (1 / (M : ℂ))}) ∧
        (Nat.Coprime c M → ∀ n, A n ∈ Subring.closure {_root_.GlobalTheory.Sieg.ee (1 / (M : ℂ))}) ∧
        (b = 0 → ∀ n, ∃ z : ℤ, A n = z) := by
  intro c M a hM ha
  refine ⟨_root_.GlobalTheory.SiegQ.expo c M a, fun b hadm => ?_⟩
  obtain ⟨hc1, -, hnot⟩ := hadm
  have hc0 : 0 < c := by omega
  have hMℂ : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  obtain ⟨ζ, hζ⟩ : ∃ ζ, ζ = _root_.GlobalTheory.Sieg.ee (1 / (M : ℂ)) := ⟨_, rfl⟩
  obtain ⟨v, hvdef⟩ : ∃ v, v = _root_.GlobalTheory.Sieg.ee ((b : ℂ) / M) := ⟨_, rfl⟩
  have hvζ : v = ζ ^ b := by
    rw [hvdef, hζ, ← _root_.GlobalTheory.Sieg.Model.ee_nat_mul]
    congr 1
    ring
  have hvn : ‖v‖ = 1 := by
    rw [hvdef, _root_.GlobalTheory.Sieg.Model.norm_ee]
    simp
  have hv0 : v ≠ 0 := by
    rw [hvdef]
    exact _root_.GlobalTheory.Sieg.Model.ee_ne_zero _
  have hint : M ∣ c * a → ¬ ∃ n : ℤ, (n : ℚ) = (c : ℚ) * ((b : ℚ) / M) := by
    intro hdvd hex
    apply hnot
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    obtain ⟨t, ht⟩ := hdvd
    refine ⟨⟨(t : ℤ), ?_⟩, hex⟩
    have hq : (c : ℚ) * a = t * M := by exact_mod_cast (by rw [ht, mul_comm] : c * a = t * M)
    push_cast
    rw [eq_comm, ← mul_div_assoc, div_eq_iff hMq, hq]
  have hv1 : M ∣ c * a → v ^ c ≠ 1 := by
    intro hdvd hvc
    apply hint hdvd
    have h := _root_.GlobalTheory.Sieg.Model.ee_eq_one (a := 0) (b := (c : ℚ) * ((b : ℚ) / M))
      UpperHalfPlane.I (by
        rw [← hvc, hvdef, ← _root_.GlobalTheory.Sieg.Model.ee_nat_mul]
        congr 1
        push_cast
        ring)
    exact h.2
  have hfun : (fun τ : ℍ => _root_.GlobalTheory.Sieg.sg c ![(a : ℚ) / M, (b : ℚ) / M] τ *
      _root_.GlobalTheory.Sieg.ee (-((_root_.GlobalTheory.SiegQ.expo c M a : ℂ) / M) * (τ : ℂ))) =
      fun τ => _root_.GlobalTheory.SiegQ.unitPart c M a v (_root_.GlobalTheory.SiegQ.qv M τ) := by
    funext τ
    obtain ⟨z, hzdef⟩ : ∃ z, z = _root_.GlobalTheory.SiegQ.qv M τ := ⟨_, rfl⟩
    rw [← hzdef]
    have hz : ‖z‖ < 1 := by
      rw [hzdef]
      exact _root_.GlobalTheory.SiegQ.norm_qv_lt hM τ
    have hz0 : z ≠ 0 := by
      rw [hzdef]
      exact Complex.exp_ne_zero _
    have e1 : _root_.GlobalTheory.Sieg.ee τ = z ^ M := by
      rw [hzdef, _root_.GlobalTheory.SiegQ.qv, ← Complex.exp_nat_mul, _root_.GlobalTheory.Sieg.ee]
      congr 1
      field_simp
    have e2 : _root_.GlobalTheory.Sieg.ee (_root_.GlobalTheory.Sieg.pt ![(a : ℚ) / M, (b : ℚ) / M] τ) =
        z ^ a * v := by
      rw [hzdef, _root_.GlobalTheory.SiegQ.qv, ← Complex.exp_nat_mul, hvdef, _root_.GlobalTheory.Sieg.ee,
        _root_.GlobalTheory.Sieg.ee, ← Complex.exp_add, _root_.GlobalTheory.Sieg.pt]
      congr 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      push_cast
      ring
    have e3 : _root_.GlobalTheory.Sieg.ee (-((_root_.GlobalTheory.SiegQ.expo c M a : ℂ) / M) * (τ : ℂ)) =
        z ^ (-_root_.GlobalTheory.SiegQ.expo c M a) := by
      rw [hzdef, _root_.GlobalTheory.SiegQ.qv, ← Complex.exp_int_mul, _root_.GlobalTheory.Sieg.ee]
      congr 1
      push_cast
      ring
    rw [_root_.GlobalTheory.Sieg.sg, e1, e2, e3, _root_.GlobalTheory.SiegQ.cth_eq hM ha hvn hz hz0,
      mul_comm (z ^ _root_.GlobalTheory.SiegQ.expo c M a), mul_assoc, ← zpow_add₀ hz0, add_neg_cancel,
      zpow_zero, mul_one]
  have hU := _root_.GlobalTheory.SiegQ.good_unitPart (R := ⊤) hc0 hM ha hvn
    (Subring.mem_top _) (Subring.mem_top _) (fun _ => Subring.mem_top _)
    (fun _ hd => ⟨hv1 hd, Subring.mem_top _⟩)
  refine ⟨_root_.GlobalTheory.SiegQ.tc (_root_.GlobalTheory.SiegQ.unitPart c M a v), ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfun]
    exact _root_.GlobalTheory.SiegQ.hasQ_tc hU.1 hM
  · rw [_root_.GlobalTheory.SiegQ.tc_zero]
    exact _root_.GlobalTheory.SiegQ.unitPart_zero_ne hc0 hM ha hv0 hv1
  · intro n
    rw [← hζ]
    set K := IntermediateField.adjoin ℚ ({ζ} : Set ℂ)
    have hζK : ζ ∈ K := IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton ζ)
    have hvK : v ∈ K := by
      rw [hvζ]
      exact pow_mem hζK b
    have hvK' : v⁻¹ ∈ K := K.inv_mem hvK
    have hcK : (1 - v ^ c)⁻¹ ∈ K := K.inv_mem (K.sub_mem K.one_mem (pow_mem hvK c))
    have h3K : (1 - v) ^ (c ^ 2) * (1 - v ^ c)⁻¹ ∈ K :=
      K.mul_mem (pow_mem (K.sub_mem K.one_mem hvK) (c ^ 2)) hcK
    have hK := _root_.GlobalTheory.SiegQ.good_unitPart (R := K.toSubalgebra.toSubring)
      hc0 hM ha hvn hvK hvK' (fun _ => h3K) (fun _ hd => ⟨hv1 hd, hcK⟩)
    exact hK.2 n
  · intro hcop n
    rw [← hζ]
    set S := Subring.closure ({ζ} : Set ℂ)
    have hζS : ζ ∈ S := Subring.subset_closure (Set.mem_singleton ζ)
    have hζ0 : ζ ≠ 0 := by
      rw [hζ]
      exact _root_.GlobalTheory.Sieg.Model.ee_ne_zero _
    have hζM : ζ ^ M = 1 := by
      rw [hζ, ← _root_.GlobalTheory.Sieg.Model.ee_nat_mul, show (M : ℂ) * (1 / M) = 1 by field_simp,
        _root_.GlobalTheory.Sieg.ee, mul_one, Complex.exp_two_pi_mul_I]
    have hζinv : ζ ^ (M - 1) = ζ⁻¹ :=
      (mul_eq_one_iff_eq_inv₀ hζ0).mp (by rw [← pow_succ, Nat.sub_add_cancel hM, hζM])
    have hvS : v ∈ S := by
      rw [hvζ]
      exact S.pow_mem hζS b
    have hvS' : v⁻¹ ∈ S := by
      rw [hvζ, ← inv_pow, ← hζinv]
      exact S.pow_mem (S.pow_mem hζS _) b
    have hvM : v ^ M = 1 := by rw [hvζ, ← pow_mul, mul_comm, pow_mul, hζM, one_pow]
    have h3 : a = 0 → (1 - v) ^ (c ^ 2) * (1 - v ^ c)⁻¹ ∈ S := by
      intro _
      by_cases hvc : v ^ c = 1
      · rw [hvc, sub_self, inv_zero, mul_zero]
        exact S.zero_mem
      · have hM1 : 1 < M := by
          by_contra h
          have hM1' : M = 1 := by omega
          apply hvc
          rw [hM1', pow_one] at hvM
          rw [hvM, one_pow]
        obtain ⟨m, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hM1
        have hvcm : (v ^ c) ^ m = v := by
          rw [← pow_mul, ← Nat.mod_add_div (c * m) M, pow_add, pow_mul, hvM, one_pow, mul_one, hm.2,
            pow_one]
        have key : 1 - v = (1 - v ^ c) * ∑ j ∈ Finset.range m, (v ^ c) ^ j := by
          rw [mul_neg_geom_sum, hvcm]
        have hne : (1 : ℂ) - v ^ c ≠ 0 := sub_ne_zero.mpr (Ne.symm hvc)
        have hc2 : c ^ 2 = (c ^ 2 - 1) + 1 := by
          have : 0 < c ^ 2 := by positivity
          omega
        have hval : (1 - v) ^ (c ^ 2) * (1 - v ^ c)⁻¹ =
            (1 - v) ^ (c ^ 2 - 1) * ∑ j ∈ Finset.range m, (v ^ c) ^ j := by
          rw [hc2, pow_succ, mul_assoc, Nat.add_sub_cancel]
          congr 1
          nth_rewrite 1 [key]
          rw [mul_right_comm, mul_inv_cancel₀ hne, one_mul]
        rw [hval]
        exact S.mul_mem (S.pow_mem (S.sub_mem S.one_mem hvS) _)
          (S.sum_mem fun j _ => S.pow_mem (S.pow_mem hvS c) j)
    have hS := _root_.GlobalTheory.SiegQ.good_unitPart (R := S) hc0 hM ha hvn hvS hvS' h3
      (fun ha0 hd => by
        exfalso
        have hMa : M ∣ a := Nat.Coprime.dvd_of_dvd_mul_left hcop.symm hd
        have := Nat.le_of_dvd ha0 hMa
        omega)
    exact hS.2 n
  · rintro rfl n
    have hv1' : v = 1 := by
      rw [hvdef]
      simp [_root_.GlobalTheory.Sieg.ee]
    have hZ := _root_.GlobalTheory.SiegQ.good_unitPart (R := (Int.castRingHom ℂ).range)
      hc0 hM ha hvn (by rw [hv1']; exact Subring.one_mem _)
      (by rw [hv1', inv_one]; exact Subring.one_mem _)
      (fun _ => by
        rw [hv1', sub_self, zero_pow (by positivity), zero_mul]
        exact Subring.zero_mem _)
      (fun _ hd => absurd (by rw [hv1', one_pow]) (hv1 hd))
    obtain ⟨t, ht⟩ := RingHom.mem_range.mp (hZ.2 n)
    exact ⟨t, by rw [← ht]; simp⟩

theorem sg_expansion : ∀ (c M a : ℕ), 0 < M → a < M → ∃ κ : ℚ, ∀ b : ℕ, admitted c ![(a : ℚ) / M, (b : ℚ) / M] → ∃ A : ℕ → ℂ, HasQ M (fun τ => sg c ![(a : ℚ) / M, (b : ℚ) / M] τ * ee (-(κ : ℂ) * (τ : ℂ))) A ∧ A 0 ≠ 0 ∧ (∀ n, A n ∈ IntermediateField.adjoin ℚ {ee (1 / (M : ℂ))}) ∧ (Nat.Coprime c M → ∀ n, A n ∈ Subring.closure {ee (1 / (M : ℂ))}) ∧ (b = 0 → ∀ n, ∃ k : ℤ, A n = k) := by
  intro c M a hM ha
  obtain ⟨k, hk⟩ := sg_expansion_int c M a hM ha
  refine ⟨(k : ℚ) / M, fun b hb => ?_⟩
  have e : (((k : ℚ) / M : ℚ) : ℂ) = (k : ℂ) / M := by push_cast; rfl
  rw [e]
  exact hk b hb

end GlobalTheory.SiegQ
