import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaDMRankOne
import GroundTheory.PAdicHodge.SemilinearResidue
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace DMTeich

open TeichLift Finset Matrix

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

variable (T) in

theorem isUnit_of_red_ne_zero {x : Γ} (hx : T.red x ≠ 0) : IsUnit x := by
  have h1 : T.coeff (T.teich (T.red x)⁻¹ * x) 0 = 1 := by
    rw [T.coeff_teich_mul, T.coeff_zero, inv_mul_cancel₀ hx]
  exact isUnit_of_mul_isUnit_right (T.isUnit_of_coeff_zero_eq_one h1)

theorem red_ne_zero_of_isUnit {x : Γ} (hx : IsUnit x) : T.red x ≠ 0 :=
  (hx.map T.red).ne_zero

theorem nontrivial_Γ (T : TeichLift p L Γ) : Nontrivial Γ :=
  ⟨⟨0, 1, fun h => by have := congrArg T.red h; simp at this⟩⟩

variable (T) in

theorem isField_B : IsField T.B where
  exists_pair_ne := by have := T.nontrivial_B; exact ⟨0, 1, zero_ne_one⟩
  mul_comm := mul_comm
  mul_inv_cancel := by
    intro b hb
    obtain ⟨N, x, hx⟩ := IsLocalization.Away.surj T.π b
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hx
      exact hb (T.eq_zero_of_mul_pow hx)
    obtain ⟨m, x', hxx', hx'0, -⟩ := T.exists_eq_π_pow_mul hx0
    obtain ⟨y, hy⟩ := (isUnit_of_red_ne_zero T hx'0).exists_right_inv
    refine ⟨algebraMap Γ T.B (T.π ^ N * y) * IsLocalization.Away.invSelf T.π ^ m, ?_⟩
    have hinv : algebraMap Γ T.B T.π * IsLocalization.Away.invSelf T.π = 1 :=
      IsLocalization.Away.mul_invSelf T.π
    calc b * (algebraMap Γ T.B (T.π ^ N * y) * IsLocalization.Away.invSelf T.π ^ m)
        = (b * algebraMap Γ T.B T.π ^ N) * algebraMap Γ T.B y *
            IsLocalization.Away.invSelf T.π ^ m := by rw [map_mul, map_pow]; ring
      _ = algebraMap Γ T.B (x' * y) *
            (algebraMap Γ T.B T.π * IsLocalization.Away.invSelf T.π) ^ m := by
          simp only [hx, hxx', map_mul, map_pow]; ring
      _ = 1 := by rw [hy, map_one, hinv, one_pow, one_mul]

noncomputable instance instFieldB : Field T.B := (isField_B T).toField

example : (instFieldB : Field T.B).toCommRing = (inferInstance : CommRing T.B) := rfl

structure FixedUnif (F : T.TeichFrob) where

  z : Γ
  isUnit_alt₂ : IsUnit z
  φ_fix : F.φ (T.π * z) = T.π * z
  a_pos : 0 < F.a

theorem exists_fixedUnif [IsAlgClosed L] (F : T.TeichFrob) (ha : 0 < F.a) : Nonempty (FixedUnif F) := by
  obtain ⟨v, hv, huv, hv1⟩ := F.exists_inv_u
  have hv0 : T.red v ≠ 0 := norm_ne_zero_iff.1 (by rw [hv1]; exact one_ne_zero)
  have hρ0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hρ1 : (1 / 2 : ℝ) < 1 := by norm_num
  obtain ⟨y, hy0, hy, -⟩ := F.exists_φ_eq_mul ha hv0 hρ0 hρ1 (T.convergesAt_of_mem_int hv hρ0 hρ1)
    zero_le_one (by rw [T.gaussNorm_eq_one_of_mem_int hv hv1 hρ0 hρ1, one_pow])
  refine ⟨⟨y, isUnit_of_red_ne_zero T hy0, ?_, ha⟩⟩
  rw [map_mul, F.φ_π, hy]
  calc T.π * F.u * (v * y) = T.π * (F.u * v) * y := by ring
    _ = T.π * y := by rw [huv, mul_one]

namespace FixedUnif

variable {F : T.TeichFrob} (U : FixedUnif F)

def ϖ0 : Γ := T.π * U.z

def ϖ : T.B := algebraMap Γ T.B U.ϖ0

theorem φ_ϖ0 : F.φ U.ϖ0 = U.ϖ0 := U.φ_fix

theorem span_ϖ0_pow (n : ℕ) : Ideal.span {U.ϖ0 ^ n} = Ideal.span {T.π ^ n} := by
  rw [ϖ0, mul_pow]
  exact Ideal.span_singleton_mul_right_unit (U.isUnit_alt₂.pow n) _

theorem red_ϖ0 : T.red U.ϖ0 = 0 := by simp [ϖ0, T.red_π]

theorem red_eq_zero_iff {x : Γ} : T.red x = 0 ↔ ∃ y, x = U.ϖ0 * y := by
  rw [T.red_eq_zero_iff]
  obtain ⟨w, hw⟩ := U.isUnit_alt₂.exists_right_inv
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨w * y, by rw [ϖ0]; linear_combination (-(T.π * y)) * hw⟩
  · rintro ⟨y, rfl⟩
    exact ⟨U.z * y, by rw [ϖ0]; ring⟩

theorem ϖ0_mem_nonZeroDivisors : U.ϖ0 ∈ nonZeroDivisors Γ :=
  mul_mem T.π_mem_nonZeroDivisors U.isUnit_alt₂.mem_nonZeroDivisors

theorem ϖ0_ne_zero : U.ϖ0 ≠ 0 := by
  have := nontrivial_Γ T
  exact nonZeroDivisors.ne_zero U.ϖ0_mem_nonZeroDivisors

theorem ϖ_ne_zero : U.ϖ ≠ 0 := fun h =>
  U.ϖ0_ne_zero (T.algebraMap_injective (by rw [map_zero]; exact h))

theorem algebraMap_ϖ0 : algebraMap Γ T.B U.ϖ0 = U.ϖ := rfl

theorem frob_ϖ : F.toB U.ϖ = U.ϖ := by rw [ϖ, TeichFrob.toB_algebraMap, U.φ_ϖ0]

theorem ϖ0_pow_mul_cancel {n : ℕ} {x y : Γ} (h : U.ϖ0 ^ n * x = U.ϖ0 ^ n * y) : x = y := by
  have := pow_mem U.ϖ0_mem_nonZeroDivisors n
  rw [mem_nonZeroDivisors_iff_right] at this
  exact sub_eq_zero.1 (by
    have h2 := this (x - y)
    rw [mul_comm] at h2
    exact h2 (by rw [mul_sub, h, sub_self]))

end FixedUnif

variable {F : T.TeichFrob} (U : FixedUnif F)

open FixedUnif

theorem sMod_iff (x y : Γ) (n : ℕ) :
    x ≡ y [SMOD ((Ideal.span {T.π}) ^ n • ⊤ : Submodule Γ Γ)] ↔
      x - y ∈ Ideal.span {U.ϖ0 ^ n} := by
  simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.sub_mem, U.span_ϖ0_pow]

theorem exists_limit (a : ℕ → Γ) (h : ∀ n, a (n + 1) - a n ∈ Ideal.span {U.ϖ0 ^ n}) :
    ∃ y : Γ, ∀ n, y - a n ∈ Ideal.span {U.ϖ0 ^ n} := by
  have := T.isAdicComplete
  have hmono : ∀ m n, m ≤ n → a n - a m ∈ Ideal.span {U.ϖ0 ^ m} := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have h1 : a (n + 1) - a n ∈ Ideal.span {U.ϖ0 ^ m} :=
        Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hmn) (h n)
      have := Ideal.add_mem _ ih h1
      convert this using 1
      abel
  obtain ⟨y, hy⟩ := IsPrecomplete.prec' (I := Ideal.span {T.π}) a (fun {m n} hmn => by
    rw [sMod_iff U, ← neg_sub]
    exact neg_mem (hmono m n hmn))
  refine ⟨y, fun n => ?_⟩
  have := (sMod_iff U _ _ _).mp (hy n)
  rw [← neg_sub]
  exact neg_mem this

theorem eq_zero_of_forall_mem (x : Γ) (h : ∀ n, x ∈ Ideal.span {U.ϖ0 ^ n}) : x = 0 := by
  have := T.isAdicComplete
  exact IsHausdorff.haus' (I := Ideal.span {T.π}) x (fun n => by
    rw [sMod_iff U, sub_zero]
    exact h n)

theorem exists_eq_pow_mul_unit {x : Γ} (hx : x ≠ 0) : ∃ (m : ℕ) (u : Γˣ), x = U.ϖ0 ^ m * u := by
  obtain ⟨m, x', hxx', hx'0, -⟩ := T.exists_eq_π_pow_mul hx
  obtain ⟨w, hw⟩ := U.isUnit_alt₂.exists_right_inv
  have hwu : IsUnit w := ⟨⟨w, U.z, by rw [mul_comm]; exact hw, hw⟩, rfl⟩
  refine ⟨m, (hwu.pow m).unit * (isUnit_of_red_ne_zero T hx'0).unit, ?_⟩
  rw [Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, hxx', ϖ0]
  calc T.π ^ m * x' = T.π ^ m * (U.z * w) ^ m * x' := by rw [hw, one_pow, mul_one]
    _ = (T.π * U.z) ^ m * (w ^ m * x') := by ring

def IsInt (n : ℤ) (a : T.B) : Prop :=
  ∃ w : Γ, a = U.ϖ ^ n * algebraMap Γ T.B w

variable {U}

theorem isInt_zero (n : ℤ) : IsInt U n 0 := ⟨0, by simp⟩

theorem isInt_algebraMap (w : Γ) : IsInt U 0 (algebraMap Γ T.B w) := ⟨w, by simp⟩

theorem isInt_one : IsInt U 0 1 := ⟨1, by simp⟩

variable (U) in
theorem isInt_pow (n : ℤ) : IsInt U n (U.ϖ ^ n) := ⟨1, by simp⟩

theorem IsInt.add {n : ℤ} {a b : T.B} (ha : IsInt U n a) (hb : IsInt U n b) :
    IsInt U n (a + b) := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨x + y, by rw [map_add, mul_add]⟩

theorem IsInt.neg {n : ℤ} {a : T.B} (ha : IsInt U n a) : IsInt U n (-a) := by
  obtain ⟨x, rfl⟩ := ha
  exact ⟨-x, by rw [map_neg, mul_neg]⟩

theorem IsInt.sub {n : ℤ} {a b : T.B} (ha : IsInt U n a) (hb : IsInt U n b) :
    IsInt U n (a - b) := by
  rw [sub_eq_add_neg]
  exact ha.add hb.neg

theorem IsInt.mul {n m : ℤ} {a b : T.B} (ha : IsInt U n a) (hb : IsInt U m b) :
    IsInt U (n + m) (a * b) := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨x * y, by rw [zpow_add₀ U.ϖ_ne_zero, map_mul]; ring⟩

theorem IsInt.mono {n m : ℤ} {a : T.B} (h : m ≤ n) (ha : IsInt U n a) : IsInt U m a := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨t, ht⟩ : ∃ t : ℕ, n = m + t := ⟨(n - m).toNat, by omega⟩
  refine ⟨U.ϖ0 ^ t * x, ?_⟩
  rw [ht, zpow_add₀ U.ϖ_ne_zero, map_mul, map_pow, algebraMap_ϖ0, zpow_natCast]
  ring

theorem IsInt.pow_mul {n : ℤ} {a : T.B} (ha : IsInt U n a) (t : ℤ) :
    IsInt U (t + n) (U.ϖ ^ t * a) :=
  (isInt_pow U t).mul ha

theorem IsInt.of_pow_mul {n t : ℤ} {a : T.B} (ha : IsInt U n (U.ϖ ^ t * a)) :
    IsInt U (n - t) a := by
  have := ha.pow_mul (-t)
  rwa [← mul_assoc, ← zpow_add₀ U.ϖ_ne_zero, neg_add_cancel, zpow_zero, one_mul,
    neg_add_eq_sub] at this

theorem IsInt.frob {n : ℤ} {a : T.B} (ha : IsInt U n a) : IsInt U n (F.toB a) := by
  obtain ⟨x, rfl⟩ := ha
  exact ⟨F.φ x, by rw [map_mul, map_zpow₀, U.frob_ϖ, TeichFrob.toB_algebraMap]⟩

theorem IsInt.frob_iterate {n : ℤ} {a : T.B} (ha : IsInt U n a) (e : ℕ) :
    IsInt U n ((⇑F.toB)^[e] a) := by
  induction e with
  | zero => exact ha
  | succ e ih => rw [Function.iterate_succ_apply']; exact ih.frob

theorem IsInt.sum {n : ℤ} {ι : Type*} (s : Finset ι) (f : ι → T.B)
    (h : ∀ i ∈ s, IsInt U n (f i)) : IsInt U n (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isInt_zero n
  | insert a s has ih =>
    rw [Finset.sum_insert has]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

variable (U) in
theorem exists_unit_form (a : T.B) (ha : a ≠ 0) :
    ∃ (n : ℤ) (u : Γˣ), a = U.ϖ ^ n * algebraMap Γ T.B u := by
  obtain ⟨N, x, hx⟩ := IsLocalization.Away.surj T.π a
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact ha (T.eq_zero_of_mul_pow hx)
  obtain ⟨m, u, hxu⟩ := exists_eq_pow_mul_unit U hx0
  obtain ⟨w, hw⟩ := U.isUnit_alt₂.exists_right_inv
  have hπ : algebraMap Γ T.B T.π = U.ϖ * algebraMap Γ T.B w := by
    rw [← algebraMap_ϖ0, ← map_mul, ϖ0, mul_assoc, hw, mul_one]
  have hzw : algebraMap Γ T.B w * algebraMap Γ T.B U.z = 1 := by rw [← map_mul, mul_comm, hw, map_one]
  refine ⟨m - N, u * (U.isUnit_alt₂.unit) ^ N, ?_⟩
  rw [hπ, hxu, map_mul, map_pow, algebraMap_ϖ0, mul_pow] at hx
  have hϖN : U.ϖ ^ N ≠ 0 := pow_ne_zero _ U.ϖ_ne_zero
  have key : a * U.ϖ ^ N = U.ϖ ^ m * algebraMap Γ T.B u * algebraMap Γ T.B U.z ^ N := by
    calc a * U.ϖ ^ N = a * U.ϖ ^ N * (algebraMap Γ T.B w * algebraMap Γ T.B U.z) ^ N := by
          rw [hzw, one_pow, mul_one]
      _ = (a * (U.ϖ ^ N * algebraMap Γ T.B w ^ N)) * algebraMap Γ T.B U.z ^ N := by ring
      _ = _ := by rw [hx]
  have ha' : a = U.ϖ ^ m * algebraMap Γ T.B u * algebraMap Γ T.B U.z ^ N * (U.ϖ ^ N)⁻¹ := by
    rw [← key, mul_inv_cancel_right₀ hϖN]
  rw [ha', zpow_sub₀ U.ϖ_ne_zero, zpow_natCast, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val,
    IsUnit.unit_spec, map_mul, map_pow, div_eq_mul_inv]
  ring

theorem unit_red_ne_zero (u : Γˣ) : T.red (u : Γ) ≠ 0 := red_ne_zero_of_isUnit u.isUnit

theorem unit_form_lt_false {n m : ℤ} (h : n < m) (u u' : Γˣ)
    (he : U.ϖ ^ n * algebraMap Γ T.B u = U.ϖ ^ m * algebraMap Γ T.B u') : False := by
  obtain ⟨t, ht⟩ : ∃ t : ℕ, m = n + t := ⟨(m - n).toNat, by omega⟩
  have ht0 : 0 < t := by omega
  rw [ht, zpow_add₀ U.ϖ_ne_zero, mul_assoc] at he
  have he' := mul_left_cancel₀ (zpow_ne_zero n U.ϖ_ne_zero) he
  rw [zpow_natCast, ← algebraMap_ϖ0, ← map_pow, ← map_mul] at he'
  have := T.algebraMap_injective he'
  have h0 := unit_red_ne_zero (T := T) u
  rw [this, map_mul, map_pow, U.red_ϖ0, zero_pow ht0.ne', zero_mul] at h0
  exact h0 rfl

theorem unit_form_unique {n m : ℤ} (u u' : Γˣ)
    (he : U.ϖ ^ n * algebraMap Γ T.B u = U.ϖ ^ m * algebraMap Γ T.B u') : n = m := by
  rcases lt_trichotomy n m with h | h | h
  · exact (unit_form_lt_false h u u' he).elim
  · exact h
  · exact (unit_form_lt_false h u' u he.symm).elim

variable (U) in
open Classical in

noncomputable def ord (a : T.B) : ℤ :=
  if h : a = 0 then 0 else Classical.choose (exists_unit_form U a h)

theorem ord_spec {a : T.B} (ha : a ≠ 0) :
    ∃ u : Γˣ, a = U.ϖ ^ ord U a * algebraMap Γ T.B u := by
  rw [ord, dif_neg ha]
  exact Classical.choose_spec (exists_unit_form U a ha)

theorem ord_eq {a : T.B} {n : ℤ} {u : Γˣ}
    (h : a = U.ϖ ^ n * algebraMap Γ T.B u) : ord U a = n := by
  have := nontrivial_Γ T
  have ha : a ≠ 0 := by
    rw [h]
    refine mul_ne_zero (zpow_ne_zero _ U.ϖ_ne_zero) ?_
    intro h0
    have := T.algebraMap_injective (h0.trans (map_zero _).symm)
    exact u.ne_zero this
  obtain ⟨u', hu'⟩ := ord_spec ha
  exact unit_form_unique u' u (hu'.symm.trans h)

theorem ord_eq_of_red {a : T.B} {n : ℤ} {w : Γ} (hw : T.red w ≠ 0)
    (h : a = U.ϖ ^ n * algebraMap Γ T.B w) : ord U a = n := by
  obtain ⟨u, rfl⟩ := isUnit_of_red_ne_zero T hw
  exact ord_eq h

theorem ord_mul {a b : T.B} (ha : a ≠ 0) (hb : b ≠ 0) :
    ord U (a * b) = ord U a + ord U b := by
  obtain ⟨u, hu⟩ := ord_spec (U := U) ha
  obtain ⟨u', hu'⟩ := ord_spec (U := U) hb
  refine ord_eq (u := u * u') ?_
  rw [zpow_add₀ U.ϖ_ne_zero, Units.val_mul, map_mul]
  conv_lhs => rw [hu, hu']
  ring

theorem ord_frob {a : T.B} (ha : a ≠ 0) : ord U (F.toB a) = ord U a := by
  obtain ⟨u, hu⟩ := ord_spec (U := U) ha
  refine ord_eq (u := Units.map (F.φ : Γ →+* Γ).toMonoidHom u) ?_
  conv_lhs => rw [hu]
  rw [map_mul, map_zpow₀, U.frob_ϖ, TeichFrob.toB_algebraMap]
  rfl

theorem ord_pow_mul {a : T.B} (ha : a ≠ 0) (t : ℤ) :
    ord U (U.ϖ ^ t * a) = t + ord U a := by
  obtain ⟨u, hu⟩ := ord_spec (U := U) ha
  refine ord_eq (u := u) ?_
  conv_lhs => rw [hu]
  rw [zpow_add₀ U.ϖ_ne_zero]
  ring

theorem ord_one : ord U (1 : T.B) = 0 :=
  ord_eq (u := 1) (by simp)

theorem ord_pow (t : ℤ) : ord U (U.ϖ ^ t) = t := by
  simpa [ord_one] using ord_pow_mul (U := U) one_ne_zero t

theorem isInt_ord (a : T.B) : IsInt U (ord U a) a := by
  by_cases ha : a = 0
  · rw [ha]; exact isInt_zero _
  · obtain ⟨u, hu⟩ := ord_spec (U := U) ha
    exact ⟨u, hu⟩

theorem isInt_iff {a : T.B} (ha : a ≠ 0) {n : ℤ} : IsInt U n a ↔ n ≤ ord U a := by
  constructor
  · rintro ⟨w, hw⟩
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw; exact ha hw
    obtain ⟨t, u, rfl⟩ := exists_eq_pow_mul_unit U hw0
    have : ord U a = n + t := by
      refine ord_eq (u := u) ?_
      rw [hw, map_mul, map_pow, algebraMap_ϖ0, zpow_add₀ U.ϖ_ne_zero, zpow_natCast]
      ring
    omega
  · intro h
    exact (isInt_ord a).mono h

variable (U) in
open Classical in

noncomputable def res (a : T.B) : L :=
  if h : IsInt U 0 a then T.red (Classical.choose h) else 0

theorem res_algebraMap (w : Γ) : res U (algebraMap Γ T.B w) = T.red w := by
  have h := isInt_algebraMap (U := U) w
  rw [res, dif_pos h]
  have h1 := Classical.choose_spec h
  have h2 : algebraMap Γ T.B w = algebraMap Γ T.B (Classical.choose h) := by
    simpa using h1
  exact congrArg T.red (T.algebraMap_injective h2).symm

theorem res_of_eq {a : T.B} {w : Γ} (h : a = algebraMap Γ T.B w) :
    res U a = T.red w := by rw [h, res_algebraMap]

theorem IsInt.exists_eq {a : T.B} (h : IsInt U 0 a) :
    ∃ w : Γ, a = algebraMap Γ T.B w := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w, by simpa using hw⟩

theorem res_add {a b : T.B} (ha : IsInt U 0 a) (hb : IsInt U 0 b) :
    res U (a + b) = res U a + res U b := by
  obtain ⟨x, rfl⟩ := ha.exists_eq
  obtain ⟨y, rfl⟩ := hb.exists_eq
  rw [← map_add, res_algebraMap, res_algebraMap, res_algebraMap, map_add]

theorem res_mul {a b : T.B} (ha : IsInt U 0 a) (hb : IsInt U 0 b) :
    res U (a * b) = res U a * res U b := by
  obtain ⟨x, rfl⟩ := ha.exists_eq
  obtain ⟨y, rfl⟩ := hb.exists_eq
  rw [← map_mul, res_algebraMap, res_algebraMap, res_algebraMap, map_mul]

theorem res_frob {a : T.B} (ha : IsInt U 0 a) : res U (F.toB a) = res U a ^ p ^ F.a := by
  obtain ⟨x, rfl⟩ := ha.exists_eq
  rw [TeichFrob.toB_algebraMap, res_algebraMap, res_algebraMap, F.red_φ]

theorem res_zero : res U (0 : T.B) = 0 := by
  simpa using res_algebraMap (U := U) 0

theorem res_one : res U (1 : T.B) = 1 := by
  simpa using res_algebraMap (U := U) 1

theorem res_eq_zero_iff {a : T.B} (ha : IsInt U 0 a) : res U a = 0 ↔ IsInt U 1 a := by
  obtain ⟨x, rfl⟩ := ha.exists_eq
  rw [res_algebraMap, U.red_eq_zero_iff]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, by rw [map_mul, algebraMap_ϖ0, zpow_one]⟩
  · rintro ⟨y, hy⟩
    rw [zpow_one, ← algebraMap_ϖ0, ← map_mul] at hy
    exact ⟨y, T.algebraMap_injective hy⟩

theorem res_ne_zero_iff {a : T.B} (ha : IsInt U 0 a) (ha0 : a ≠ 0) :
    res U a ≠ 0 ↔ ord U a = 0 := by
  rw [Ne, res_eq_zero_iff ha, isInt_iff ha0]
  have := (isInt_iff ha0).mp ha
  omega

theorem res_eq_zero_of_isInt_one {a : T.B} (ha : IsInt U 1 a) : res U a = 0 :=
  (res_eq_zero_iff (ha.mono zero_le_one)).mpr ha

section Matrix

variable {ι : Type*}

variable (U) in

theorem surjective_of_mod (G : (ι → Γ) →+ (ι → Γ))
    (hG : ∀ x, G (U.ϖ0 • x) = U.ϖ0 • G x)
    (hmod : ∀ z, ∃ x y, z = G x + U.ϖ0 • y) : Function.Surjective G := by
  choose X Y hXY using hmod
  have hGpow : ∀ n x, G (U.ϖ0 ^ n • x) = U.ϖ0 ^ n • G x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => intro x; rw [pow_succ', mul_smul, hG, ih, mul_smul]
  intro z
  let zs : ℕ → (ι → Γ) := fun n => Nat.rec z (fun _ w => Y w) n
  let s : ℕ → (ι → Γ) := fun n => ∑ j ∈ range n, U.ϖ0 ^ j • X (zs j)
  have hA : ∀ n, z - G (s n) = U.ϖ0 ^ n • zs n := by
    intro n
    induction n with
    | zero => simp [s, zs]
    | succ n ih =>
      have e1 : s (n + 1) = s n + U.ϖ0 ^ n • X (zs n) := Finset.sum_range_succ _ _
      have e2 : zs (n + 1) = Y (zs n) := rfl
      have h' : zs n - G (X (zs n)) = U.ϖ0 • Y (zs n) := by
        rw [sub_eq_iff_eq_add']
        exact hXY (zs n)
      rw [e1, map_add, hGpow, ← sub_sub, ih, ← smul_sub, h', smul_smul, ← pow_succ, e2]
  have hstep : ∀ i n, s (n + 1) i - s n i ∈ Ideal.span {U.ϖ0 ^ n} := by
    intro i n
    have e1 : s (n + 1) = s n + U.ϖ0 ^ n • X (zs n) := Finset.sum_range_succ _ _
    rw [e1, Pi.add_apply, add_sub_cancel_left, Pi.smul_apply, smul_eq_mul]
    exact Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)
  choose y hy using fun i => exists_limit U (fun n => s n i) (hstep i)
  choose u hu using fun n i => Ideal.mem_span_singleton'.mp (hy i n)
  refine ⟨y, ?_⟩
  have hys : ∀ n, y - s n = U.ϖ0 ^ n • (fun i => u n i) := by
    intro n
    funext i
    simp [← hu n i, mul_comm]
  funext i
  symm
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_mem U
  intro n
  have : z - G y = U.ϖ0 ^ n • (zs n - G (fun i => u n i)) := by
    rw [show y = s n + (y - s n) by abel, map_add, ← sub_sub, hA, hys, hGpow, smul_sub]
  rw [← Pi.sub_apply, this, Pi.smul_apply, smul_eq_mul]
  exact Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)

variable [Fintype ι]

noncomputable def matOp (A : Matrix ι ι Γ) (τ : Γ →+* Γ) : (ι → Γ) →+ (ι → Γ) where
  toFun x := A *ᵥ (fun i => τ (x i))
  map_zero' := by
    simp only [Pi.zero_apply, map_zero]
    exact Matrix.mulVec_zero A
  map_add' x y := by
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp

theorem matOp_apply (A : Matrix ι ι Γ) (τ : Γ →+* Γ) (x : ι → Γ) :
    matOp A τ x = A *ᵥ (fun i => τ (x i)) := rfl

theorem matOp_smul_of_fix (A : Matrix ι ι Γ) {τ : Γ →+* Γ} {c : Γ} (hc : τ c = c) (x : ι → Γ) :
    matOp A τ (c • x) = c • matOp A τ x := by
  rw [matOp_apply, matOp_apply, ← Matrix.mulVec_smul]
  congr 1
  funext i
  simp [hc]

variable (T) in

def redV (x : ι → Γ) : ι → L := fun i => T.red (x i)

variable {e : ℕ}

variable (T) in

noncomputable def resOp (A : Matrix ι ι Γ) (e : ℕ) : (ι → L) →+ (ι → L) where
  toFun x := A.map T.red *ᵥ (fun i => x i ^ p ^ e)
  map_zero' := by
    rw [← Matrix.mulVec_zero (A.map T.red)]
    congr 1
    funext i
    simp [hp.out.ne_zero]
  map_add' x y := by
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp [add_pow_char_pow]

theorem resOp_apply (A : Matrix ι ι Γ) (x : ι → L) :
    resOp T A e x = A.map T.red *ᵥ (fun i => x i ^ p ^ e) := rfl

theorem resOp_smul (A : Matrix ι ι Γ) (c : L) (x : ι → L) :
    resOp T A e (c • x) = c ^ p ^ e • resOp T A e x := by
  rw [resOp_apply, resOp_apply, ← Matrix.mulVec_smul]
  congr 1
  funext i
  simp [mul_pow]

theorem red_matOp (A : Matrix ι ι Γ) {τ : Γ →+* Γ}
    (hτ : ∀ y, T.red (τ y) = T.red y ^ p ^ e) (x : ι → Γ) :
    redV T (matOp A τ x) = resOp T A e (redV T x) := by
  funext i
  simp only [redV, matOp_apply, resOp_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum,
    map_mul, hτ]

theorem red_iterate_matOp (A : Matrix ι ι Γ) {τ : Γ →+* Γ}
    (hτ : ∀ y, T.red (τ y) = T.red y ^ p ^ e) (x : ι → Γ) (N : ℕ) :
    redV T ((⇑(matOp A τ))^[N] x) = (⇑(resOp T A e))^[N] (redV T x) := by
  induction N with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', red_matOp A hτ, ih]

omit [Fintype ι] in
theorem redV_sub (x y : ι → Γ) : redV T (x - y) = redV T x - redV T y := by
  funext i
  simp [redV]

omit [Fintype ι] in
theorem redV_ϖ0_smul (x : ι → Γ) : redV T (U.ϖ0 • x) = 0 := by
  funext i
  simp [redV, U.red_ϖ0]

omit [Fintype ι] in
variable (U) in
theorem exists_eq_ϖ0_smul_of_red (x : ι → Γ) (h : redV T x = 0) : ∃ y, x = U.ϖ0 • y := by
  have : ∀ i, ∃ y, x i = U.ϖ0 * y := fun i => U.red_eq_zero_iff.1 (congrFun h i)
  choose y hy using this
  exact ⟨y, funext fun i => by simp [hy i]⟩

omit [Fintype ι] in
theorem exists_lift (x : ι → L) : ∃ y : ι → Γ, redV T y = x :=
  ⟨fun i => (T.red_surjective (x i)).choose, funext fun i => (T.red_surjective (x i)).choose_spec⟩

variable [IsAlgClosed L]

variable (U) in

theorem matOp_sub_surjective (he : 0 < e) (A : Matrix ι ι Γ) {τ : Γ →+* Γ}
    (hτ : ∀ y, T.red (τ y) = T.red y ^ p ^ e) (hτϖ : τ U.ϖ0 = U.ϖ0) (z : ι → Γ) :
    ∃ x, matOp A τ x - x = z := by
  obtain ⟨x, hx⟩ := surjective_of_mod U (matOp A τ - AddMonoidHom.id _)
    (fun x => by simp [matOp_smul_of_fix A hτϖ, smul_sub]) (fun z => by
      obtain ⟨xb, hxb⟩ := SemilinearResidue.exists_sub_eq (p := p) he
        (resOp_smul (T := T) (e := e) A) (redV T z)
      obtain ⟨x, rfl⟩ := exists_lift (T := T) xb
      obtain ⟨y, hy⟩ := exists_eq_ϖ0_smul_of_red U (z - (matOp A τ x - x)) (by
        rw [redV_sub, redV_sub, red_matOp A hτ, hxb, sub_self])
      exact ⟨x, y, by simp [← hy]⟩) z
  exact ⟨x, by simpa using hx⟩

variable (U) in

theorem exists_fixed (he : 0 < e) (A : Matrix ι ι Γ) {τ : Γ →+* Γ}
    (hτ : ∀ y, T.red (τ y) = T.red y ^ p ^ e) (hτϖ : τ U.ϖ0 = U.ϖ0) (x₀ : ι → Γ)
    (hx₀ : ∀ N, redV T ((⇑(matOp A τ))^[N] x₀) ≠ 0) :
    ∃ y, matOp A τ y = y ∧ redV T y ≠ 0 := by
  obtain ⟨yb, hyb0, hyb⟩ := SemilinearResidue.exists_fixed_ne_zero (p := p) he
    (resOp_smul (T := T) (e := e) A) (redV T x₀)
    (fun N => by rw [← red_iterate_matOp A hτ]; exact hx₀ N)
  obtain ⟨y₀, rfl⟩ := exists_lift (T := T) yb
  obtain ⟨w, hw⟩ := exists_eq_ϖ0_smul_of_red U (matOp A τ y₀ - y₀) (by
    rw [redV_sub, red_matOp A hτ, hyb, sub_self])
  obtain ⟨x, hx⟩ := matOp_sub_surjective U he A hτ hτϖ w
  refine ⟨y₀ - U.ϖ0 • x, ?_, ?_⟩
  · rw [map_sub, matOp_smul_of_fix A hτϖ, sub_eq_sub_iff_sub_eq_sub, hw, ← smul_sub, hx]
  · rw [redV_sub, redV_ϖ0_smul, sub_zero]
    exact hyb0

end Matrix

section Lattice

variable {H : Type*} [AddCommGroup H] [Module T.B H]

theorem frob_iterate_algebraMap (e : ℕ) (w : Γ) :
    (⇑F.toB)^[e] (algebraMap Γ T.B w) = algebraMap Γ T.B (((F.φ : Γ →+* Γ) ^ e) w) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Function.iterate_succ_apply', ih, TeichFrob.toB_algebraMap, RingHom.coe_pow,
      RingHom.coe_pow, Function.iterate_succ_apply']
    rfl

theorem red_frob_pow (e : ℕ) (w : Γ) :
    T.red (((F.φ : Γ →+* Γ) ^ e) w) = T.red w ^ p ^ (F.a * e) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [RingHom.coe_pow, Function.iterate_succ_apply', ← RingHom.coe_pow, RingEquiv.coe_toRingHom,
      F.red_φ, ih, ← pow_mul, ← pow_add, mul_add, mul_one, add_comm]

theorem frob_pow_ϖ0 (e : ℕ) : ((F.φ : Γ →+* Γ) ^ e) U.ϖ0 = U.ϖ0 := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [RingHom.coe_pow, Function.iterate_succ_apply', ← RingHom.coe_pow, ih,
      RingEquiv.coe_toRingHom, U.φ_ϖ0]

variable (T) in

noncomputable def ofCoord {n : ℕ} (b : Fin n → H) (x : Fin n → Γ) : H :=
  ∑ i, algebraMap Γ T.B (x i) • b i

theorem ofCoord_eq_zero {n : ℕ} {b : Fin n → H} (hb : LinearIndependent T.B b)
    {x : Fin n → Γ} (h : ofCoord T b x = 0) : x = 0 := by
  funext i
  have := Fintype.linearIndependent_iff.mp hb (fun i => algebraMap Γ T.B (x i)) h i
  exact T.algebraMap_injective (this.trans (map_zero _).symm)

theorem map_ofCoord (e : ℕ) (g : H →+ H)
    (hg : ∀ (a : T.B) (x : H), g (a • x) = (⇑F.toB)^[e] a • g x)
    {n : ℕ} (b : Fin n → H) (A : Matrix (Fin n) (Fin n) Γ)
    (hA : ∀ j, g (b j) = ∑ i, algebraMap Γ T.B (A i j) • b i) (x : Fin n → Γ) :
    g (ofCoord T b x) = ofCoord T b (matOp A ((F.φ : Γ →+* Γ) ^ e) x) := by
  simp only [ofCoord, map_sum, hg, frob_iterate_algebraMap, hA, Finset.smul_sum, smul_smul,
    matOp_apply, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [mul_comm]

theorem map_iterate_ofCoord (e : ℕ) (g : H →+ H)
    (hg : ∀ (a : T.B) (x : H), g (a • x) = (⇑F.toB)^[e] a • g x)
    {n : ℕ} (b : Fin n → H) (A : Matrix (Fin n) (Fin n) Γ)
    (hA : ∀ j, g (b j) = ∑ i, algebraMap Γ T.B (A i j) • b i) (x : Fin n → Γ) (N : ℕ) :
    (⇑g)^[N] (ofCoord T b x) =
      ofCoord T b ((⇑(matOp A ((F.φ : Γ →+* Γ) ^ e)))^[N] x) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_ofCoord e g hg b A hA]

theorem exists_fixed_of_lattice [IsAlgClosed L] (U : FixedUnif F) (e : ℕ) (he : 0 < e) (g : H →+ H)
    (hg : ∀ (a : T.B) (x : H), g (a • x) = (⇑F.toB)^[e] a • g x)
    {n : ℕ} (b : Fin n → H) (hb : LinearIndependent T.B b)
    (A : Matrix (Fin n) (Fin n) Γ)
    (hA : ∀ j, g (b j) = ∑ i, algebraMap Γ T.B (A i j) • b i)
    (x₀ : Fin n → Γ)
    (hx₀ : ∀ N, redV T ((⇑(matOp A ((F.φ : Γ →+* Γ) ^ e)))^[N] x₀) ≠ 0) :
    ∃ y : Fin n → Γ, redV T y ≠ 0 ∧ ofCoord T b y ≠ 0 ∧
      g (ofCoord T b y) = ofCoord T b y := by
  obtain ⟨y, hy, hy0⟩ := exists_fixed U (Nat.mul_pos U.a_pos he) A (red_frob_pow e)
    (frob_pow_ϖ0 (U := U) e) x₀ hx₀
  refine ⟨y, hy0, fun h => hy0 ?_, by rw [map_ofCoord e g hg b A hA, hy]⟩
  rw [ofCoord_eq_zero hb h]
  funext i
  simp [redV]

end Lattice

end DMTeich

end GroundTheory.PAdicHodge
