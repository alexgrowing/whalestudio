import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqZpowOfMemMaxUnramifiedSubfield
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

noncomputable section

namespace GlobalTheory.UnramSpan

open GlobalTheory.UnramValue

variable {l : ℕ} [Fact l.Prime]

theorem fg_rootRing {m : ℕ} (hm : 0 < m) : (rootRing l m).toSubmodule.FG := by
  classical
  have hfin : {x : Om l | x ^ m = 1}.Finite := by
    refine (Polynomial.nthRoots m (1 : Om l)).toFinset.finite_toSet.subset ?_
    intro x hx
    simpa [Polynomial.mem_nthRoots hm] using hx
  refine fg_adjoin_of_finite hfin ?_
  intro x hx
  refine IsIntegral.of_pow hm ?_
  rw [show x ^ m = 1 from hx]; exact isIntegral_one

theorem exists_mem_rootRing {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) (h1 : ‖x‖ ≤ 1) :
    ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ x ∈ rootRing l m := by
  have hp : l.Prime := Fact.out
  have hl0 : (l : Om l) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hp.one_lt
  obtain ⟨m, hm, hl, c, hc, h⟩ := exists_mul_mem hx
  refine ⟨m, hm, hl, ?_⟩
  have key : ∀ k : ℕ, (l : Om l) ^ k * x ∈ rootRing l m → x ∈ rootRing l m := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      obtain ⟨z, hz, ez⟩ := exists_eq_mul hm hl hk (by
        rw [norm_mul, norm_pow, norm_l]
        have : ((l : ℝ)⁻¹) ^ (k + 1) < 1 :=
          pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hl1) (Nat.succ_ne_zero k)
        calc _ ≤ ((l : ℝ)⁻¹) ^ (k + 1) * 1 := by gcongr
          _ < 1 := by simpa using this)
      apply ih
      have : (l : Om l) ^ k * x = z := by
        apply mul_left_cancel₀ hl0
        rw [← ez]; ring
      rwa [this]
  apply key c.valuation
  have e := PadicInt.unitCoeff_spec hc
  set u := PadicInt.unitCoeff hc
  have e2 : (l : Om l) ^ c.valuation * x =
      algebraMap ℤ_[l] (Om l) (↑u⁻¹ : ℤ_[l]) * (algebraMap ℤ_[l] (Om l) c * x) := by
    rw [← mul_assoc, ← map_mul]
    congr 1
    conv_rhs => rw [e, Units.inv_mul_cancel_left]
    simp
  rw [e2]
  exact mul_mem (Subalgebra.algebraMap_mem _ _) h

theorem norm_pow_sub_pow_le {m : ℕ} (hm : 0 < m) {k : ℕ} (hk : k ≠ 0) {a b : Om l}
    (ha : a ∈ rootRing l m) (hb : b ∈ rootRing l m) (h : ‖a - b‖ ≤ (l : ℝ)⁻¹) :
    ‖a ^ (l ^ k) - b ^ (l ^ k)‖ ≤ (l : ℝ)⁻¹ * ‖a - b‖ := by
  have hp : l.Prime := Fact.out
  have hd := sub_mem ha hb
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp (⟨b, hb⟩ : rootRing l m) ⟨a - b, hd⟩ k
  have hr' := congrArg Subtype.val hr
  simp only [MulMemClass.coe_mul, AddMemClass.coe_add, SubmonoidClass.coe_pow,
    SubringClass.coe_natCast, add_sub_cancel] at hr'
  have e : a ^ (l ^ k) - b ^ (l ^ k) = (a - b) ^ (l ^ k) + l * (a - b) * (b * r) := by
    rw [hr']; ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · obtain ⟨j, hj⟩ : ∃ j, l ^ k = j + 2 :=
      ⟨l ^ k - 2, by have := Nat.one_lt_pow hk hp.one_lt; omega⟩
    have h1 := norm_le_one hm hd
    have h2 : ‖a - b‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg _) h1
    rw [hj, norm_pow, pow_add, sq]
    calc _ ≤ 1 * ((l : ℝ)⁻¹ * ‖a - b‖) := by gcongr
      _ = _ := one_mul _
  · rw [norm_mul, norm_mul, norm_l]
    have h1 := norm_le_one hm (mul_mem hb r.2)
    calc _ ≤ (l : ℝ)⁻¹ * ‖a - b‖ * 1 := by gcongr
      _ = _ := mul_one _

def part (F : IntermediateField ℚ_[l] (Om l)) (m : ℕ) : Submodule ℤ_[l] (Om l) :=
  (rootRing l m).toSubmodule ⊓ F.toSubalgebra.toSubmodule.restrictScalars ℤ_[l]

theorem mem_part {F : IntermediateField ℚ_[l] (Om l)} {m : ℕ} {x : Om l} :
    x ∈ part F m ↔ x ∈ rootRing l m ∧ x ∈ F := Iff.rfl

theorem fg_part (F : IntermediateField ℚ_[l] (Om l)) {m : ℕ} (hm : 0 < m) : (part F m).FG :=
  (fg_rootRing hm).of_le inf_le_left

theorem exists_teich (F : IntermediateField ℚ_[l] (Om l)) {m : ℕ} (hm : 0 < m) (hl : ¬ l ∣ m)
    {x : Om l} (hx : x ∈ part F m) :
    ∃ w ∈ part F m, w ^ (l ^ m.totient) = w ∧ ‖x - w‖ < 1 := by
  have hp : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hp.one_lt
  have hli : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have : ContinuousSMul ℤ_[l] (Om l) := by
    refine continuousSMul_of_algebraMap ℤ_[l] (Om l) ?_
    exact (AddMonoidHomClass.isometry_of_norm _ norm_algebraMap_int).continuous
  have hc : IsCompact ((part F m : Set (Om l)) ∩ Metric.closedBall x (l : ℝ)⁻¹) :=
    (Submodule.isCompact_of_fg (fg_part F hm)).inter_right Metric.isClosed_closedBall
  have hstep : ∀ y ∈ rootRing l m, ‖y ^ (l ^ m.totient) - y‖ ≤ (l : ℝ)⁻¹ := by
    intro y hy
    obtain ⟨z, hz, ez⟩ := pow_sub_mem hl hy
    rw [ez, add_sub_cancel_left, norm_mul, norm_l]
    have h1 := norm_le_one hm hz
    calc _ ≤ (l : ℝ)⁻¹ * 1 := by gcongr
      _ = _ := mul_one _
  obtain ⟨w, ⟨hw, hwx⟩, hmin⟩ := hc.exists_isMinOn
    (f := fun y : Om l => ‖y ^ (l ^ m.totient) - y‖)
    ⟨x, hx, Metric.mem_closedBall_self (by positivity)⟩ (by fun_prop)
  rw [Metric.mem_closedBall, dist_eq_norm] at hwx
  have hw' := mem_part.mp hw
  refine ⟨w, hw, ?_, by rw [norm_sub_rev]; exact hwx.trans_lt hli⟩
  have hmem : w ^ (l ^ m.totient) ∈ (part F m : Set (Om l)) ∩ Metric.closedBall x (l : ℝ)⁻¹ := by
    refine ⟨mem_part.mpr ⟨pow_mem hw'.1 _, pow_mem hw'.2 _⟩, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm,
      show w ^ (l ^ m.totient) - x = (w ^ (l ^ m.totient) - w) + (w - x) by ring]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hstep w hw'.1) hwx)
  have h1 : ‖w ^ (l ^ m.totient) - w‖ ≤ ‖(w ^ (l ^ m.totient)) ^ (l ^ m.totient) - w ^ (l ^ m.totient)‖ :=
    hmin hmem
  have h2 := norm_pow_sub_pow_le hm (Nat.totient_pos.mpr hm).ne' (pow_mem hw'.1 (l ^ m.totient))
    hw'.1 (hstep w hw'.1)
  have h3 := norm_nonneg (w ^ (l ^ m.totient) - w)
  have h4 : ‖w ^ (l ^ m.totient) - w‖ = 0 := by nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp h4)

theorem part_le_span (F : IntermediateField ℚ_[l] (Om l)) {m : ℕ} (hm : 0 < m) (hl : ¬ l ∣ m) :
    part F m ≤ Submodule.span ℤ_[l]
      {w : Om l | w ∈ F ∧ ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ w ^ m = 1} := by
  have hp : l.Prime := Fact.out
  have hl0 : (l : Om l) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal ℤ_[l])
    (fg_part F hm) (IsLocalRing.maximalIdeal_le_jacobson _) ?_
  intro x hx
  obtain ⟨w, hw, ew, hxw⟩ := exists_teich F hm hl hx
  have hd := mem_part.mp (sub_mem hx hw)
  obtain ⟨z, hz, ez⟩ := exists_eq_mul hm hl hd.1 hxw
  have hzF : z ∈ F := by
    have : z = (x - w) / l := by rw [ez]; field_simp
    rw [this]
    exact div_mem hd.2 (natCast_mem F l)
  have e : x = w + (l : ℤ_[l]) • z := by
    rw [Algebra.smul_def, map_natCast, ← ez]; ring
  rw [e]
  refine Submodule.add_mem_sup ?_ (Submodule.smul_mem_smul ?_ (mem_part.mpr ⟨hz, hzF⟩))
  · by_cases h0 : w = 0
    · rw [h0]; exact zero_mem _
    · have hq : 1 < l ^ m.totient := Nat.one_lt_pow (Nat.totient_pos.mpr hm).ne' hp.one_lt
      refine Submodule.subset_span ⟨(mem_part.mp hw).2, l ^ m.totient - 1, by omega, ?_, ?_⟩
      · intro hd
        have h1 : l ∣ l ^ m.totient := dvd_pow_self l (Nat.totient_pos.mpr hm).ne'
        have h2 := Nat.dvd_sub h1 hd
        rw [show l ^ m.totient - (l ^ m.totient - 1) = 1 by omega] at h2
        exact hp.not_dvd_one h2
      · apply mul_right_cancel₀ h0
        rw [← pow_succ, Nat.sub_add_cancel hq.le, ew, one_mul]
  · rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _

theorem exists_sum_rootsOfUnity : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (c : Om l), c ∈ K0 K → ‖c‖ ≤ 1 → ∃ (n : ℕ) (z : Fin n → ℤ_[l]) (ω : Fin n → Om l), (∀ i, ω i ∈ K0 K ∧ ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ ω i ^ m = 1) ∧ c = ∑ i, algebraMap ℚ_[l] (Om l) (z i : ℚ_[l]) * ω i := by
  intro l _ K c hc h1
  obtain ⟨m, hm, hl, h⟩ := exists_mem_rootRing (x := c) (show c ∈ K.1 ⊓ MaximalUnramifiedExtension l from hc).2 h1
  obtain ⟨n, z, g, e⟩ := Submodule.mem_span_set'.mp (part_le_span (K0 K) hm hl (mem_part.mpr ⟨h, hc⟩))
  refine ⟨n, z, fun i => g i, fun i => (g i).2, ?_⟩
  rw [← e]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Om l)]
  rfl

end GlobalTheory.UnramSpan
