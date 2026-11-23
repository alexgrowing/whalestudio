import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

noncomputable section

namespace GlobalTheory.UnramValue

variable {l : ℕ} [Fact l.Prime]

def rootRing (l : ℕ) [Fact l.Prime] (m : ℕ) : Subalgebra ℤ_[l] (Om l) :=
  Algebra.adjoin ℤ_[l] {x : Om l | x ^ m = 1}

theorem norm_algebraMap_int (a : ℤ_[l]) : ‖algebraMap ℤ_[l] (Om l) a‖ = ‖a‖ := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Om l)]
  exact PadicAlgCl.norm_extends l _

theorem norm_l : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
  have h := norm_algebraMap_int (l := l) (l : ℤ_[l])
  rwa [map_natCast, PadicInt.norm_p] at h

theorem rootRing_mono {m m' : ℕ} (h : m ∣ m') : rootRing l m ≤ rootRing l m' := by
  unfold rootRing
  apply Algebra.adjoin_mono
  intro x hx
  have hx' : x ^ m = 1 := hx
  obtain ⟨k, rfl⟩ := h
  show x ^ (m * k) = 1
  rw [pow_mul, hx', one_pow]

theorem norm_le_one {m : ℕ} (hm : 0 < m) {y : Om l} (hy : y ∈ rootRing l m) : ‖y‖ ≤ 1 := by
  unfold rootRing at hy
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    have hx' : x ^ m = 1 := hx
    have h1 : ‖x‖ ^ m = 1 := by rw [← norm_pow, hx', norm_one]
    exact le_of_eq ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').mp h1)
  | algebraMap r => rw [norm_algebraMap_int]; exact PadicInt.norm_le_one r
  | add x y _ _ hx hy => exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  | mul x y _ _ hx hy => rw [norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hy

private lemma rootRing_eq_span_roots_of_unity (m : ℕ) :
    (rootRing l m : Set (Om l)) = Submodule.span ℤ_[l] {x : Om l | x ^ m = 1} := by
  have h := Algebra.adjoin_eq_span_of_subset (R := ℤ_[l]) (s := {x : Om l | x ^ m = 1}) (by
    intro x hx
    apply Submodule.subset_span
    induction hx using Submonoid.closure_induction with
    | mem y hy => exact hy
    | one => exact one_pow m
    | mul y z _ _ hy hz =>
      have hy' : y ^ m = 1 := hy
      have hz' : z ^ m = 1 := hz
      show (y * z) ^ m = 1
      rw [mul_pow, hy', hz', one_mul])
  rw [← h]
  rfl

theorem isClosed_rootRing {m : ℕ} (hm : 0 < m) : IsClosed (rootRing l m : Set (Om l)) := by
  classical
  set T : Finset (Om l) := (Polynomial.nthRoots m (1 : Om l)).toFinset with hT
  have hS : {x : Om l | x ^ m = 1} = Set.range (fun i : T => (i : Om l)) := by
    ext x
    simp [T, Polynomial.mem_nthRoots hm]
  have hc : Continuous (algebraMap ℤ_[l] (Om l)) :=
    (AddMonoidHomClass.isometry_of_norm (algebraMap ℤ_[l] (Om l)) norm_algebraMap_int).continuous
  have hf : Continuous (fun c : T → ℤ_[l] => ∑ i, c i • (i : Om l)) := by
    refine continuous_finsetSum _ (fun i _ => ?_)
    simp only [Algebra.smul_def]
    exact (hc.comp (continuous_apply i)).mul continuous_const
  have heq : (rootRing l m : Set (Om l)) =
      Set.range (fun c : T → ℤ_[l] => ∑ i, c i • (i : Om l)) := by
    rw [rootRing_eq_span_roots_of_unity, hS]
    ext x
    simp only [SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun, Set.mem_range]
  rw [heq]
  exact (isCompact_range hf).isClosed

private lemma exists_pow_prime_pow_eq_add_prime_mul (k : ℕ) (a : ℤ_[l]) : ∃ c : ℤ_[l], a ^ (l ^ k) = a + l * c := by
  have h : a ^ (l ^ k) - a ∈ Ideal.span {(l : ℤ_[l])} := by
    rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow,
      ZMod.pow_card_pow, sub_self]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h
  exact ⟨c, by linear_combination -hc⟩

private lemma pow_prime_pow_totient_eq_self_of_pow_eq_one {m : ℕ} (hl : ¬ l ∣ m) {x : Om l} (hx : x ^ m = 1) :
    x ^ (l ^ m.totient) = x := by
  have hcop : Nat.Coprime l m := (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hl
  have hmod : l ^ m.totient % m = 1 % m := Nat.ModEq.pow_totient hcop
  have key : ∀ n, x ^ n = x ^ (n % m) := fun n => by
    conv_lhs => rw [← Nat.mod_add_div n m, pow_add, pow_mul, hx, one_pow, mul_one]
  rw [key, hmod, ← key, pow_one]

theorem pow_sub_mem {m : ℕ} (hl : ¬ l ∣ m) {y : Om l} (hy : y ∈ rootRing l m) :
    ∃ z ∈ rootRing l m, y ^ (l ^ m.totient) = y + l * z := by
  have hp : l.Prime := Fact.out
  suffices H : ∃ z : rootRing l m,
      (⟨y, hy⟩ : rootRing l m) ^ (l ^ m.totient) = ⟨y, hy⟩ + (l : rootRing l m) * z by
    obtain ⟨z, hz⟩ := H
    refine ⟨z, z.2, ?_⟩
    have := congrArg Subtype.val hz
    simpa using this
  refine Algebra.adjoin_induction
    (p := fun y hy => ∃ z : rootRing l m,
      (⟨y, hy⟩ : rootRing l m) ^ (l ^ m.totient) = ⟨y, hy⟩ + (l : rootRing l m) * z)
    ?_ ?_ ?_ ?_ hy
  · intro x hx
    refine ⟨0, Subtype.ext ?_⟩
    simp [pow_prime_pow_totient_eq_self_of_pow_eq_one hl hx]
  · intro r
    obtain ⟨c, hc⟩ := exists_pow_prime_pow_eq_add_prime_mul (l := l) m.totient r
    refine ⟨algebraMap ℤ_[l] (rootRing l m) c, ?_⟩
    show (algebraMap ℤ_[l] (rootRing l m) r) ^ (l ^ m.totient) =
      algebraMap ℤ_[l] (rootRing l m) r + (l : rootRing l m) * algebraMap ℤ_[l] (rootRing l m) c
    rw [← map_pow, hc, map_add, map_mul, map_natCast]
  · rintro x y hx hy ⟨z1, h1⟩ ⟨z2, h2⟩
    obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp (⟨x, hx⟩ : rootRing l m) ⟨y, hy⟩ m.totient
    refine ⟨z1 + z2 + ⟨x, hx⟩ * ⟨y, hy⟩ * r, ?_⟩
    show ((⟨x, hx⟩ : rootRing l m) + ⟨y, hy⟩) ^ (l ^ m.totient) = (⟨x, hx⟩ + ⟨y, hy⟩) + _
    rw [hr, h1, h2]
    ring
  · rintro x y hx hy ⟨z1, h1⟩ ⟨z2, h2⟩
    refine ⟨⟨x, hx⟩ * z2 + z1 * ⟨y, hy⟩ + (l : rootRing l m) * z1 * z2, ?_⟩
    show ((⟨x, hx⟩ : rootRing l m) * ⟨y, hy⟩) ^ (l ^ m.totient) = (⟨x, hx⟩ * ⟨y, hy⟩) + _
    rw [mul_pow, h1, h2]
    ring

theorem exists_eq_mul {m : ℕ} (hm : 0 < m) (hl : ¬ l ∣ m) {y : Om l} (hy : y ∈ rootRing l m)
    (h1 : ‖y‖ < 1) : ∃ z ∈ rootRing l m, y = l * z := by
  have hp : l.Prime := Fact.out
  have hN1 : 1 < l ^ m.totient := Nat.one_lt_pow (Nat.totient_pos.2 hm).ne' hp.one_lt
  have hl0 : (l : Om l) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have step : ∀ j : ℕ, ∃ w ∈ rootRing l m, y ^ ((l ^ m.totient) ^ j) = y + l * w := by
    intro j
    induction j with
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | succ j ih =>
      obtain ⟨w, hw, hwe⟩ := ih
      obtain ⟨z, hz, hze⟩ := pow_sub_mem hl (pow_mem hy ((l ^ m.totient) ^ j))
      refine ⟨w + z, add_mem hw hz, ?_⟩
      rw [pow_succ, pow_mul, hze, hwe]
      ring
  have hmem : ∀ j : ℕ, (l : Om l)⁻¹ * (y - y ^ ((l ^ m.totient) ^ j)) ∈ rootRing l m := by
    intro j
    obtain ⟨w, hw, hwe⟩ := step j
    have e : (l : Om l)⁻¹ * (y - y ^ ((l ^ m.totient) ^ j)) = -w := by
      rw [hwe, sub_add_cancel_left, mul_neg, inv_mul_cancel_left₀ hl0]
    rw [e]
    exact neg_mem hw
  have ht : Filter.Tendsto (fun j : ℕ => (l : Om l)⁻¹ * (y - y ^ ((l ^ m.totient) ^ j)))
      Filter.atTop (nhds ((l : Om l)⁻¹ * (y - 0))) := by
    have h0 : Filter.Tendsto (fun j : ℕ => y ^ ((l ^ m.totient) ^ j)) Filter.atTop (nhds 0) :=
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one h1).comp
        (tendsto_pow_atTop_atTop_of_one_lt hN1)
    exact (tendsto_const_nhds.sub h0).const_mul _
  have hz := (isClosed_rootRing hm).mem_of_tendsto ht (Filter.Eventually.of_forall hmem)
  rw [sub_zero] at hz
  exact ⟨(l : Om l)⁻¹ * y, hz, (mul_inv_cancel_left₀ hl0 y).symm⟩

theorem norm_rootRing {m : ℕ} (hm : 0 < m) (hl : ¬ l ∣ m) {y : Om l} (hy : y ∈ rootRing l m)
    (h0 : y ≠ 0) : ∃ n : ℤ, ‖y‖ = (l : ℝ) ^ n := by
  have hp : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hp.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have key : ∀ k : ℕ, ∀ y ∈ rootRing l m, y ≠ 0 → (l : ℝ) ^ (-(k : ℤ)) ≤ ‖y‖ →
      ∃ n : ℤ, ‖y‖ = (l : ℝ) ^ n := by
    intro k
    induction k with
    | zero =>
      intro y hy _ hle
      refine ⟨0, ?_⟩
      simp only [Nat.cast_zero, neg_zero, zpow_zero] at hle ⊢
      exact le_antisymm (norm_le_one hm hy) hle
    | succ k ih =>
      intro y hy hy0 hle
      rcases (norm_le_one hm hy).lt_or_eq with hlt | heq
      · obtain ⟨z, hz, rfl⟩ := exists_eq_mul hm hl hy hlt
        have hz0 : z ≠ 0 := by rintro rfl; simp at hy0
        rw [norm_mul, norm_l] at hle ⊢
        rw [show (-((k + 1 : ℕ) : ℤ)) = -(k : ℤ) - 1 by push_cast; ring,
          zpow_sub_one₀ hl0.ne'] at hle
        have hk : (l : ℝ) ^ (-(k : ℤ)) ≤ ‖z‖ :=
          le_of_mul_le_mul_left (by rwa [mul_comm] at hle) (inv_pos.2 hl0)
        obtain ⟨n, hn⟩ := ih z hz hz0 hk
        exact ⟨n - 1, by rw [hn, zpow_sub_one₀ hl0.ne', mul_comm]⟩
      · exact ⟨0, by simp [heq]⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (l : ℝ) ^ (-(k : ℤ)) ≤ ‖y‖ := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 h0) (inv_lt_one_of_one_lt₀ hl1)
    exact ⟨k, by rw [zpow_neg, zpow_natCast, ← inv_pow]; exact hk.le⟩
  exact key k y hy h0 hk

theorem exists_mul_mem {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) :
    ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ ∃ c : ℤ_[l], c ≠ 0 ∧ algebraMap ℤ_[l] (Om l) c * x ∈ rootRing l m := by
  have hp : l.Prime := Fact.out
  unfold MaximalUnramifiedExtension at hx
  rw [← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
    (fun y _ => Algebra.IsAlgebraic.isAlgebraic y)] at hx
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨m, hm, hlm, hym⟩ := hy
    refine ⟨m, hm, hlm, 1, one_ne_zero, ?_⟩
    rw [map_one, one_mul]
    exact Algebra.subset_adjoin hym
  | algebraMap q =>
    refine ⟨1, one_pos, hp.not_dvd_one, ?_⟩
    by_cases hq : ‖q‖ ≤ 1
    · refine ⟨1, one_ne_zero, ?_⟩
      rw [map_one, one_mul]
      obtain ⟨a, ha⟩ : ∃ a : ℤ_[l], (a : ℚ_[l]) = q := ⟨⟨q, hq⟩, rfl⟩
      have e : algebraMap ℚ_[l] (Om l) q = algebraMap ℤ_[l] (Om l) a := by
        rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Om l), ← ha]
        rfl
      rw [e]
      exact Subalgebra.algebraMap_mem _ _
    · have hq0 : q ≠ 0 := by rintro rfl; simp at hq
      have hinv : ‖q⁻¹‖ ≤ 1 := by
        rw [norm_inv]
        exact inv_le_one_of_one_le₀ (le_of_not_ge hq)
      obtain ⟨a, ha⟩ : ∃ a : ℤ_[l], (a : ℚ_[l]) = q⁻¹ := ⟨⟨q⁻¹, hinv⟩, rfl⟩
      refine ⟨a, ?_, ?_⟩
      · rintro rfl
        apply hq0
        rw [PadicInt.coe_zero] at ha
        exact inv_eq_zero.1 ha.symm
      · have e : algebraMap ℤ_[l] ℚ_[l] a * q = 1 := by
          rw [show algebraMap ℤ_[l] ℚ_[l] a = (a : ℚ_[l]) from rfl, ha, inv_mul_cancel₀ hq0]
        rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Om l), ← map_mul, e, map_one]
        exact one_mem _
  | add x y _ _ hx hy =>
    obtain ⟨m1, hm1, hl1, c1, hc1, h1⟩ := hx
    obtain ⟨m2, hm2, hl2, c2, hc2, h2⟩ := hy
    refine ⟨m1 * m2, Nat.mul_pos hm1 hm2, fun h => (hp.dvd_mul.1 h).elim hl1 hl2, c1 * c2,
      mul_ne_zero hc1 hc2, ?_⟩
    have e : algebraMap ℤ_[l] (Om l) (c1 * c2) * (x + y) =
        algebraMap ℤ_[l] (Om l) c2 * (algebraMap ℤ_[l] (Om l) c1 * x) +
          algebraMap ℤ_[l] (Om l) c1 * (algebraMap ℤ_[l] (Om l) c2 * y) := by
      rw [map_mul]
      ring
    rw [e]
    exact add_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (rootRing_mono (dvd_mul_right m1 m2) h1))
      (mul_mem (Subalgebra.algebraMap_mem _ _) (rootRing_mono (dvd_mul_left m2 m1) h2))
  | mul x y _ _ hx hy =>
    obtain ⟨m1, hm1, hl1, c1, hc1, h1⟩ := hx
    obtain ⟨m2, hm2, hl2, c2, hc2, h2⟩ := hy
    refine ⟨m1 * m2, Nat.mul_pos hm1 hm2, fun h => (hp.dvd_mul.1 h).elim hl1 hl2, c1 * c2,
      mul_ne_zero hc1 hc2, ?_⟩
    have e : algebraMap ℤ_[l] (Om l) (c1 * c2) * (x * y) =
        (algebraMap ℤ_[l] (Om l) c1 * x) * (algebraMap ℤ_[l] (Om l) c2 * y) := by
      rw [map_mul]
      ring
    rw [e]
    exact mul_mem (rootRing_mono (dvd_mul_right m1 m2) h1) (rootRing_mono (dvd_mul_left m2 m1) h2)

theorem norm_of_mem_Kur {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) (h0 : x ≠ 0) :
    ∃ n : ℤ, ‖x‖ = (l : ℝ) ^ n := by
  have hp : l.Prime := Fact.out
  obtain ⟨m, hm, hlm, c, hc, hmem⟩ := exists_mul_mem hx
  have hcx : algebraMap ℤ_[l] (Om l) c * x ≠ 0 := by
    refine mul_ne_zero ?_ h0
    rw [← norm_ne_zero_iff, norm_algebraMap_int]
    exact norm_ne_zero_iff.2 hc
  obtain ⟨n, hn⟩ := norm_rootRing hm hlm hmem hcx
  rw [norm_mul, norm_algebraMap_int] at hn
  have hc' : (c : ℚ_[l]) ≠ 0 := fun h => hc (PadicInt.ext (h.trans PadicInt.coe_zero.symm))
  have hcv : ‖c‖ = (l : ℝ) ^ (-(c : ℚ_[l]).valuation) := by
    rw [PadicInt.norm_def]
    exact Padic.norm_eq_zpow_neg_valuation hc'
  have hl0 : (l : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [hcv] at hn
  refine ⟨n + (c : ℚ_[l]).valuation, ?_⟩
  calc ‖x‖ = (l : ℝ) ^ ((c : ℚ_[l]).valuation) * ((l : ℝ) ^ (-(c : ℚ_[l]).valuation) * ‖x‖) := by
        rw [← mul_assoc, ← zpow_add₀ hl0, add_neg_cancel, zpow_zero, one_mul]
    _ = (l : ℝ) ^ (n + (c : ℚ_[l]).valuation) := by rw [hn, zpow_add₀ hl0, mul_comm]

theorem norm_of_mem_unramified_subfield : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (x : Om l),
    x ∈ K0 K → x ≠ 0 → ∃ n : ℤ, ‖x‖ = (l : ℝ) ^ n := by
  intro l _ K x hx h0
  unfold K0 at hx
  exact norm_of_mem_Kur hx.2 h0

end GlobalTheory.UnramValue
