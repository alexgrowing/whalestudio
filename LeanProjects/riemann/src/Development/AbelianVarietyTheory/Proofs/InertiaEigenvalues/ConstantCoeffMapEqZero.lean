import Mathlib
import GroundTheory.LocalFields.FormalGroups.LubinTateGroup

namespace GlobalTheory.LTLog

open MvPowerSeries GroundTheory.LocalField.FormalGroup

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {π : A}
  (K : Type*) [Field K] [Algebra A K] [FaithfulSMul A K]

theorem existsUnique_eigen (hπ : Irreducible π) {f : PowerSeries A} (hf : IsLubinTateSeries π f)
    {σ : Type*} [Finite σ] {ℓ : MvPowerSeries σ K} (hℓ : constantCoeff ℓ = 0) :
    ∃! φ : MvPowerSeries σ K, (2 : ℕ∞) ≤ order (φ - ℓ) ∧
      PowerSeries.subst φ (PowerSeries.C (algebraMap A K π) * PowerSeries.X) =
        subst (substEach (PowerSeries.map (algebraMap A K) f)) φ := by
  have h0 : algebraMap A K π ≠ 0 := by simpa using hπ.ne_zero
  refine existsUnique_of_dvd_defect (π := algebraMap A K π) (by simp) (by simp) ?_ ?_
    (fun x hx => (mul_eq_zero.1 hx).resolve_left h0) (fun n hn => ?_)
    (fun _ _ => (IsUnit.mk0 _ h0).dvd) hℓ
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hf.constantCoeff_eq_zero, map_zero]
  · rw [PowerSeries.coeff_map, hf.coeff_one]
  · simpa using (isUnit_one_sub_pow hπ hn).map (algebraMap A K)

noncomputable def log (hπ : Irreducible π) {f : PowerSeries A} (hf : IsLubinTateSeries π f) :
    PowerSeries K :=
  (existsUnique_eigen K hπ hf (σ := Unit) (ℓ := (PowerSeries.X : PowerSeries K))
    PowerSeries.constantCoeff_X).exists.choose

theorem coeff_eq_of_order {R σ : Type*} [CommRing R] {φ ψ : MvPowerSeries σ R}
    (h : (2 : ℕ∞) ≤ order (φ - ψ)) {e : σ →₀ ℕ} (he : e.degree ≤ 1) : coeff e φ = coeff e ψ := by
  have he2 : (e.degree : ℕ∞) < 2 := by
    have : e.degree < 2 := by omega
    exact_mod_cast this
  have := coeff_of_lt_order (lt_of_lt_of_le he2 h)
  rwa [map_sub, sub_eq_zero] at this

variable (hπ : Irreducible π) {f g : PowerSeries A} (hf : IsLubinTateSeries π f)
  (hg : IsLubinTateSeries π g)

theorem log_spec : (2 : ℕ∞) ≤ order ((log K hπ hf - PowerSeries.X : PowerSeries K) :
      MvPowerSeries Unit K) ∧
    PowerSeries.subst (log K hπ hf) (PowerSeries.C (algebraMap A K π) * PowerSeries.X) =
      subst (substEach (PowerSeries.map (algebraMap A K) f)) (log K hπ hf) :=
  (existsUnique_eigen K hπ hf (σ := Unit) (ℓ := (PowerSeries.X : PowerSeries K))
    PowerSeries.constantCoeff_X).exists.choose_spec

theorem constantCoeff_log : PowerSeries.constantCoeff (log K hπ hf) = 0 := by
  have := coeff_eq_of_order (log_spec K hπ hf).1 (e := 0) (by simp)
  rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply] at this
  exact this.trans PowerSeries.constantCoeff_X

theorem coeff_one_log : PowerSeries.coeff 1 (log K hπ hf) = 1 := by
  have := coeff_eq_of_order (log_spec K hπ hf).1 (e := Finsupp.single () 1) (by simp)
  exact this.trans PowerSeries.coeff_one_X

theorem isLift_log : IsLubinTateLift (PowerSeries.C (algebraMap A K π) * PowerSeries.X)
    (PowerSeries.map (algebraMap A K) f) (PowerSeries.X : PowerSeries K) (log K hπ hf) :=
  ⟨constantCoeff_log K hπ hf, (log_spec K hπ hf).1, (log_spec K hπ hf).2⟩

theorem log_subst_self :
    PowerSeries.subst (PowerSeries.map (algebraMap A K) f) (log K hπ hf) =
      PowerSeries.C (algebraMap A K π) * log K hπ hf := by
  have h := (log_spec K hπ hf).2
  rw [subst_substEach_unit, powerSeries_subst_C_mul_X
    (PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_log K hπ hf))] at h
  exact h.symm

omit [IsDomain A] [IsDiscreteValuationRing A] [FaithfulSMul A K] in
theorem constantCoeff_map_eq_zero {u : PowerSeries A} (hu : PowerSeries.constantCoeff u = 0) :
    PowerSeries.constantCoeff (PowerSeries.map (algebraMap A K) u) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hu, map_zero]

omit [IsDomain A] [IsDiscreteValuationRing A] [FaithfulSMul A K] in

theorem isLift_map {σ : Type*} [Finite σ] {u v : PowerSeries A}
    (hv : PowerSeries.constantCoeff v = 0) {ℓ φ : MvPowerSeries σ A}
    (h : IsLubinTateLift u v ℓ φ) :
    IsLubinTateLift (PowerSeries.map (algebraMap A K) u) (PowerSeries.map (algebraMap A K) v)
      (map (algebraMap A K) ℓ) (map (algebraMap A K) φ) := by
  obtain ⟨h0, h2, he⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h0,
      map_zero]
  · rw [← map_sub]
    have h3 : ((2 : ℕ) : ℕ∞) ≤ order (map (algebraMap A K) (φ - ℓ)) :=
      nat_le_order fun d hd => by
        rw [coeff_map, coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h2), map_zero]
    exact_mod_cast h3
  · have := congrArg (map (algebraMap A K)) he
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero h0),
      map_subst (hasSubst_substEach hv)] at this
    rw [this]
    congr 1
    funext i
    rw [substEach_apply, substEach_apply, PowerSeries.map_subst (PowerSeries.HasSubst.X i), map_X]

section
variable [Finite (IsLocalRing.ResidueField A)]

theorem log_subst_lubinTateHom (a : A) :
    PowerSeries.subst (PowerSeries.map (algebraMap A K) (lubinTateHom hπ hf hg a).toPowerSeries)
        (log K hπ hf) = PowerSeries.C (algebraMap A K a) * log K hπ hg := by
  have hf0 := constantCoeff_map_eq_zero K hf.constantCoeff_eq_zero
  have hg0 := constantCoeff_map_eq_zero K hg.constantCoeff_eq_zero
  have h1 := (isLift_log K hπ hf).comp hf0 hg0 (fun _ =>
    isLift_map K hg.constantCoeff_eq_zero (isLubinTateLift_lubinTateHom hπ hf hg a))
  have hℓ : constantCoeff (σ := Unit)
      (PowerSeries.C (algebraMap A K a) * PowerSeries.X : PowerSeries K) = 0 := by
    change PowerSeries.constantCoeff _ = 0
    simp
  refine (existsUnique_eigen K hπ hg (σ := Unit) hℓ).unique ⟨?_, h1.2.2⟩ ⟨?_, ?_⟩
  · have h2 := h1.2.1
    rw [← PowerSeries.subst_def, ← PowerSeries.subst_def, PowerSeries.subst_X] at h2
    · have e : map (algebraMap A K) (PowerSeries.C a * PowerSeries.X : PowerSeries A) =
          (PowerSeries.C (algebraMap A K a) * PowerSeries.X : PowerSeries K) := by
        change PowerSeries.map _ _ = _
        simp
      rw [e] at h2
      exact h2
    · refine PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_map_eq_zero K ?_)
      simp
  · refine two_le_order_sub_C_mul_X ?_ ?_
    · simp [constantCoeff_log]
    · simp [coeff_one_log]
  · have hs := PowerSeries.HasSubst.of_constantCoeff_zero' hg0
    rw [subst_substEach_unit, powerSeries_subst_C_mul_X, PowerSeries.subst_mul hs,
      log_subst_self, PowerSeries.subst_C]
    · change PowerSeries.C _ * _ = PowerSeries.C _ * _
      exact mul_left_comm _ _ _
    · refine PowerSeries.HasSubst.of_constantCoeff_zero' ?_
      simp [constantCoeff_log]

theorem log_subst_formalGroup :
    PowerSeries.subst (map (algebraMap A K) (lubinTateFormalGroup hπ hf).toPowerSeries)
        (log K hπ hf) =
      PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) K) (log K hπ hf) +
        PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) K) (log K hπ hf) := by
  have hf0 := constantCoeff_map_eq_zero K hf.constantCoeff_eq_zero
  have h1 := (isLift_log K hπ hf).comp hf0 hf0 (fun _ =>
    isLift_map K hf.constantCoeff_eq_zero
      (isLubinTateLift_lubinTateLift hπ hf hf (![1, 1] : Fin 2 → A)))
  have hX : ∀ i : Fin 2, IsLubinTateLift (PowerSeries.C (algebraMap A K π) * PowerSeries.X)
      (PowerSeries.map (algebraMap A K) f) (X i)
      (PowerSeries.subst (X i : MvPowerSeries (Fin 2) K) (log K hπ hf)) := by
    intro i
    have := (isLift_log K hπ hf).comp hf0 hf0 (fun _ => isLubinTateLift_X hf0 i)
    rwa [← PowerSeries.subst_def, ← PowerSeries.subst_def,
      PowerSeries.subst_X (PowerSeries.HasSubst.X i)] at this
  have hℓ : constantCoeff (X 0 + X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  refine (existsUnique_eigen K hπ hf hℓ).unique ⟨?_, h1.2.2⟩ ⟨?_, ?_⟩
  · have h2 := h1.2.1
    have e : map (algebraMap A K) (sum₂ (![1, 1] : Fin 2 → A)) =
        (X 0 + X 1 : MvPowerSeries (Fin 2) K) := by
      rw [linearForm_fin_two]
      simp
    rw [e, ← PowerSeries.subst_def, ← PowerSeries.subst_def,
      PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero hℓ)] at h2
    exact h2
  · rw [add_sub_add_comm]
    exact le_trans (le_min (hX 0).2.1 (hX 1).2.1) min_order_le_add
  · have e := fun i => (hX i).2.2
    have e0 := e 0
    have e1 := e 1
    rw [powerSeries_subst_C_mul_X (PowerSeries.HasSubst.of_constantCoeff_zero (hX _).1)] at e0 e1
    rw [subst_add (hasSubst_substEach hf0), ← e0, ← e1, powerSeries_subst_C_mul_X
      (PowerSeries.HasSubst.of_constantCoeff_zero (by rw [map_add, (hX 0).1, (hX 1).1, add_zero])),
      mul_add]

include hf in
omit [Finite (IsLocalRing.ResidueField A)] in

theorem dvd_coeff_pow (m k : ℕ) (hk : k ≠ Nat.card (IsLocalRing.ResidueField A) * m) :
    π ∣ PowerSeries.coeff k (f ^ m) := by
  have h1 : PowerSeries.C π ∣ f - PowerSeries.X ^ Nat.card (IsLocalRing.ResidueField A) := by
    choose c hc using hf.dvd_coeff_sub
    refine ⟨PowerSeries.mk c, ?_⟩
    ext n
    rw [hc, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
  obtain ⟨u, hu⟩ := h1.trans (sub_dvd_pow_sub_pow _ _ m)
  have := congrArg (PowerSeries.coeff k) hu
  rw [map_sub, ← pow_mul, PowerSeries.coeff_X_pow, if_neg hk, sub_zero,
    PowerSeries.coeff_C_mul] at this
  exact ⟨_, this⟩

omit [IsDomain A] [IsDiscreteValuationRing A] [Finite (IsLocalRing.ResidueField A)] in
theorem coeff_pow_of_lt {u : PowerSeries A} (hu : PowerSeries.constantCoeff u = 0) {m k : ℕ}
    (h : k < m) : PowerSeries.coeff k (u ^ m) = 0 := by
  obtain ⟨v, rfl⟩ := PowerSeries.X_dvd_iff.2 hu
  rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

omit [IsDomain A] [IsDiscreteValuationRing A] [Finite (IsLocalRing.ResidueField A)] in
theorem coeff_pow_self {u : PowerSeries A} (hu : PowerSeries.constantCoeff u = 0) (m : ℕ) :
    PowerSeries.coeff m (u ^ m) = PowerSeries.coeff 1 u ^ m := by
  obtain ⟨v, rfl⟩ := PowerSeries.X_dvd_iff.2 hu
  rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    PowerSeries.coeff_succ_X_mul]
  simp

omit [Finite (IsLocalRing.ResidueField A)] in

theorem coeff_log_rec (k : ℕ) :
    (algebraMap A K π - algebraMap A K π ^ k) * PowerSeries.coeff k (log K hπ hf) =
      ∑ m ∈ Finset.range k, PowerSeries.coeff m (log K hπ hf) *
        algebraMap A K (PowerSeries.coeff k (f ^ m)) := by
  have hf0 := constantCoeff_map_eq_zero K hf.constantCoeff_eq_zero
  have h := congrArg (PowerSeries.coeff k) (log_subst_self K hπ hf)
  rw [PowerSeries.coeff_C_mul,
    PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' hf0),
    finsum_eq_sum_of_support_subset (s := Finset.range (k + 1)), Finset.sum_range_succ,
    coeff_pow_self hf0, PowerSeries.coeff_map, hf.coeff_one] at h
  · simp only [smul_eq_mul, ← map_pow, PowerSeries.coeff_map] at h
    rw [← map_pow]
    linear_combination -h
  · intro m hm
    rw [Function.mem_support] at hm
    by_contra hc
    simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hc
    exact hm (by rw [coeff_pow_of_lt hf0 (by omega), smul_zero])

theorem pow_log_mul_coeff_mem (k : ℕ) :
    ∃ b : A, algebraMap A K π ^ Nat.log (Nat.card (IsLocalRing.ResidueField A)) k *
      PowerSeries.coeff k (log K hπ hf) = algebraMap A K b := by
  set q := Nat.card (IsLocalRing.ResidueField A) with hq
  have hq1 : 1 < q := Finite.one_lt_card
  have h0 : algebraMap A K π ≠ 0 := by simpa using hπ.ne_zero
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · exact ⟨0, by simp [constantCoeff_log]⟩
    · exact ⟨1, by simp [coeff_one_log]⟩
  have hterm : ∀ m ∈ Finset.range k, ∃ b : A,
      algebraMap A K π ^ Nat.log q k * (PowerSeries.coeff m (log K hπ hf) *
        algebraMap A K (PowerSeries.coeff k (f ^ m))) = algebraMap A K π * algebraMap A K b := by
    intro m hm
    have hm' := Finset.mem_range.1 hm
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · exact ⟨0, by simp [constantCoeff_log]⟩
    obtain ⟨b, hb⟩ := ih m hm'
    rcases (Nat.log_mono_right (b := q) hm'.le).eq_or_lt with he | hl
    · obtain ⟨c, hc⟩ := dvd_coeff_pow hf m k (by
        rintro rfl
        rw [← hq, mul_comm, Nat.log_mul_base hq1 hm0.ne'] at he
        omega)
      refine ⟨b * c, ?_⟩
      rw [← he, hc, ← mul_assoc, hb, map_mul, map_mul]
      ring
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hl
      refine ⟨π ^ d * b * PowerSeries.coeff k (f ^ m), ?_⟩
      rw [hd, map_mul, map_mul, map_pow (algebraMap A K) π d, ← hb]
      ring
  choose! c hc using hterm
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨u, hu⟩ := (isUnit_one_sub_pow hπ (n := j) (by omega)).exists_left_inv
  have hu' := congrArg (algebraMap A K) hu
  simp only [map_mul, map_sub, map_one, map_pow] at hu'
  have hr := congrArg (algebraMap A K π ^ Nat.log q (j + 1) * ·) (coeff_log_rec K hπ hf (j + 1))
  simp only [Finset.mul_sum] at hr
  rw [Finset.sum_congr rfl hc, ← Finset.mul_sum, ← map_sum] at hr
  refine ⟨u * ∑ m ∈ Finset.range (j + 1), c m, mul_left_cancel₀ h0 ?_⟩
  rw [map_mul]
  linear_combination algebraMap A K u * hr - (algebraMap A K π *
    algebraMap A K π ^ Nat.log q (j + 1) * PowerSeries.coeff (j + 1) (log K hπ hf)) * hu'

theorem main :
    PowerSeries.constantCoeff (log K hπ hf) = 0 ∧ PowerSeries.coeff 1 (log K hπ hf) = 1 ∧
    PowerSeries.subst (map (algebraMap A K) (lubinTateFormalGroup hπ hf).toPowerSeries)
        (log K hπ hf) =
      PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) K) (log K hπ hf) +
        PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) K) (log K hπ hf) ∧
    (∀ a : A, PowerSeries.subst
        (PowerSeries.map (algebraMap A K) (lubinTateHom hπ hf hf a).toPowerSeries) (log K hπ hf) =
      PowerSeries.C (algebraMap A K a) * log K hπ hf) ∧
    PowerSeries.subst (PowerSeries.map (algebraMap A K) f) (log K hπ hf) =
      PowerSeries.C (algebraMap A K π) * log K hπ hf ∧
    ∀ k : ℕ, ∃ b : A, algebraMap A K π ^ Nat.log (Nat.card (IsLocalRing.ResidueField A)) k *
      PowerSeries.coeff k (log K hπ hf) = algebraMap A K b :=
  ⟨constantCoeff_log K hπ hf, coeff_one_log K hπ hf, log_subst_formalGroup K hπ hf,
    log_subst_lubinTateHom K hπ hf hf, log_subst_self K hπ hf, pow_log_mul_coeff_mem K hπ hf⟩

end

end GlobalTheory.LTLog
