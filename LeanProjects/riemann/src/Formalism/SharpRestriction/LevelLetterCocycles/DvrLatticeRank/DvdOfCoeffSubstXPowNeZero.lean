import Mathlib

namespace DualFramesAlt.EigenUniformiser

open PowerSeries

variable {O : Type*} [CommRing O]

private theorem powerSeries_algHom_C_eq (α : PowerSeries O →ₐ[O] PowerSeries O) (c : O) : α (C c) = C c := by
  have h : (C c : PowerSeries O) = algebraMap O (PowerSeries O) c := by
    rw [Algebra.algebraMap_eq_smul_one, smul_eq_C_mul, mul_one]
  rw [h, AlgHom.commutes]

private theorem X_pow_dvd_algHom_sub_of_X_eq (α β : PowerSeries O →ₐ[O] PowerSeries O) (hX : α X = β X)
    (h0 : constantCoeff (α X) = 0) (n : ℕ) (f : PowerSeries O) :
    (X : PowerSeries O) ^ n ∣ α f - β f := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    obtain ⟨g, c, hf⟩ : ∃ (g : PowerSeries O) (c : O), f = X * g + C c :=
      ⟨_, _, eq_X_mul_shift_add_const f⟩
    subst hf
    have key : α (X * g + C c) - β (X * g + C c) = α X * (α g - β g) := by
      rw [map_add, map_add, map_mul, map_mul, powerSeries_algHom_C_eq α, powerSeries_algHom_C_eq β, ← hX]; ring
    rw [key, pow_succ']
    exact mul_dvd_mul (X_dvd_iff.mpr h0) (ih g)

private theorem algHom_apply_eq_of_X_eq (α β : PowerSeries O →ₐ[O] PowerSeries O) (hX : α X = β X)
    (h0 : constantCoeff (α X) = 0) (f : PowerSeries O) : α f = β f := by
  rw [← sub_eq_zero]
  ext n
  have h := (X_pow_dvd_iff.mp (X_pow_dvd_algHom_sub_of_X_eq α β hX h0 (n + 1) f)) n (Nat.lt_succ_self n)
  rw [h, map_zero]

private theorem subst_X_apply_eq_self (f : PowerSeries O) : PowerSeries.subst (X : PowerSeries O) f = f := by
  have hX : HasSubst (X : PowerSeries O) := HasSubst.of_constantCoeff_zero' constantCoeff_X
  let β : PowerSeries O →ₐ[O] PowerSeries O := substAlgHom (R := O) hX
  have hβ : ∀ g : PowerSeries O, β g = PowerSeries.subst (X : PowerSeries O) g :=
    fun g => congrFun (coe_substAlgHom (R := O) hX) g
  have h1 : β X = (AlgHom.id O (PowerSeries O)) X := by
    rw [hβ, subst_X (R := O) hX, AlgHom.id_apply]
  have h0 : constantCoeff (β X) = 0 := by rw [hβ, subst_X (R := O) hX, constantCoeff_X]
  rw [← hβ, algHom_apply_eq_of_X_eq β (AlgHom.id O (PowerSeries O)) h1 h0 f, AlgHom.id_apply]

theorem algHom_subst (φ : PowerSeries O →ₐ[O] PowerSeries O)
    (hφ : constantCoeff (φ X) = 0) {p : PowerSeries O} (hp : constantCoeff p = 0)
    (g : PowerSeries O) :
    φ (PowerSeries.subst p g) = PowerSeries.subst (φ p) g := by
  have h0 : constantCoeff (φ p) = 0 := by
    obtain ⟨q, hq⟩ := X_dvd_iff.mpr hp
    rw [hq, map_mul, map_mul, hφ, zero_mul]
  have hps : HasSubst p := HasSubst.of_constantCoeff_zero' hp
  have hb : HasSubst (φ p) := HasSubst.of_constantCoeff_zero' h0
  let α : PowerSeries O →ₐ[O] PowerSeries O := φ.comp (substAlgHom (R := O) hps)
  let β : PowerSeries O →ₐ[O] PowerSeries O := substAlgHom (R := O) hb
  have hα : ∀ f : PowerSeries O, α f = φ (PowerSeries.subst p f) :=
    fun f => congrArg φ (congrFun (coe_substAlgHom (R := O) hps) f)
  have hβ : ∀ f : PowerSeries O, β f = PowerSeries.subst (φ p) f :=
    fun f => congrFun (coe_substAlgHom (R := O) hb) f
  have hX : α X = β X := by rw [hα, hβ, subst_X (R := O) hps, subst_X (R := O) hb]
  have h0' : constantCoeff (α X) = 0 := by rw [hα, subst_X (R := O) hps]; exact h0
  rw [← hα, ← hβ]
  exact algHom_apply_eq_of_X_eq α β hX h0' g

section Coordinate

variable {p : PowerSeries O} (hp0 : constantCoeff p = 0) (hp1 : IsUnit (coeff 1 p))
include hp0 hp1

theorem subst_subst_substInv (f : PowerSeries O) :
    PowerSeries.subst p (PowerSeries.subst (substInvOfIsUnit p hp1) f) = f := by
  have hp : HasSubst p := HasSubst.of_constantCoeff_zero' hp0
  have hq : HasSubst (substInvOfIsUnit p hp1) :=
    HasSubst.of_constantCoeff_zero' (constantCoeff_substInvOfIsUnit p hp1)
  have key : PowerSeries.subst p (substInvOfIsUnit p hp1) = (X : PowerSeries O) :=
    subst_substInvOfIsUnit_left p hp0 hp1
  rw [subst_comp_subst_apply (R := O) hq hp, key, subst_X_apply_eq_self]

theorem subst_substInv_subst (f : PowerSeries O) :
    PowerSeries.subst (substInvOfIsUnit p hp1) (PowerSeries.subst p f) = f := by
  have hp : HasSubst p := HasSubst.of_constantCoeff_zero' hp0
  have hq : HasSubst (substInvOfIsUnit p hp1) :=
    HasSubst.of_constantCoeff_zero' (constantCoeff_substInvOfIsUnit p hp1)
  have key : PowerSeries.subst (substInvOfIsUnit p hp1) p = (X : PowerSeries O) :=
    subst_substInvOfIsUnit_right p hp0 hp1
  rw [subst_comp_subst_apply (R := O) hp hq, key, subst_X_apply_eq_self]

theorem subst_surjective (f : PowerSeries O) : ∃ g : PowerSeries O, f = PowerSeries.subst p g :=
  ⟨PowerSeries.subst (substInvOfIsUnit p hp1) f, (subst_subst_substInv hp0 hp1 f).symm⟩

theorem subst_injective {g h : PowerSeries O}
    (e : PowerSeries.subst p g = PowerSeries.subst p h) : g = h :=
  calc g = PowerSeries.subst (substInvOfIsUnit p hp1) (PowerSeries.subst p g) :=
        (subst_substInv_subst hp0 hp1 g).symm
    _ = PowerSeries.subst (substInvOfIsUnit p hp1) (PowerSeries.subst p h) := by rw [e]
    _ = h := subst_substInv_subst hp0 hp1 h

end Coordinate

private theorem algHom_eq_C_constantCoeff_add_X_mul (α : PowerSeries O →ₐ[O] PowerSeries O) (f : PowerSeries O) :
    α f = C (constantCoeff f) + α X * α (mk fun n => coeff (n + 1) f) := by
  conv_lhs => rw [eq_X_mul_shift_add_const f]
  rw [map_add, map_mul, powerSeries_algHom_C_eq, add_comm]

theorem subst_eq_C_add {a : PowerSeries O} (ha : constantCoeff a = 0) (f : PowerSeries O) :
    PowerSeries.subst a f = C (constantCoeff f) +
      a * PowerSeries.subst a (mk fun n => coeff (n + 1) f) := by
  have ha' : HasSubst a := HasSubst.of_constantCoeff_zero' ha
  let α : PowerSeries O →ₐ[O] PowerSeries O := substAlgHom (R := O) ha'
  have hα : ∀ g : PowerSeries O, α g = PowerSeries.subst a g :=
    fun g => congrFun (coe_substAlgHom (R := O) ha') g
  rw [← hα, ← hα, algHom_eq_C_constantCoeff_add_X_mul α f, hα X, subst_X (R := O) ha']

private theorem coeff_subst_X_pow_eq_ite_dvd {s : ℕ} (hs : s ≠ 0) (h : PowerSeries O) (k : ℕ) :
    coeff k (PowerSeries.subst (X ^ s : PowerSeries O) h) = if s ∣ k then coeff (k / s) h else 0 := by
  rw [coeff_subst' (R := O) (HasSubst.X_pow (R := O) hs)]
  by_cases hk : s ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [finsum_eq_single _ m]
    · try beta_reduce
      rw [if_pos (dvd_mul_right s m), Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hs), ← pow_mul]
      simp [coeff_X_pow]
    · intro d hd
      try beta_reduce
      rw [← pow_mul, coeff_X_pow, if_neg, smul_zero]
      intro h'
      exact hd (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hs) h').symm
  · rw [if_neg hk, finsum_eq_single _ 0]
    · try beta_reduce
      rw [pow_zero, coeff_one, if_neg, smul_zero]
      rintro rfl
      exact hk (dvd_zero s)
    · intro d _
      try beta_reduce
      rw [← pow_mul, coeff_X_pow, if_neg, smul_zero]
      rintro rfl
      exact hk (dvd_mul_right s d)

theorem subst_X_pow_of_dvd {s : ℕ} (hs : s ≠ 0) (g : PowerSeries O)
    (hg : ∀ k, coeff k g ≠ 0 → s ∣ k) :
    g = PowerSeries.subst (X ^ s : PowerSeries O) (mk fun m => coeff (m * s) g) := by
  ext k
  rw [coeff_subst_X_pow_eq_ite_dvd hs]
  by_cases h : s ∣ k
  · rw [if_pos h]
    obtain ⟨m, rfl⟩ := h
    rw [coeff_mk, Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hs), Nat.mul_comm s m]
  · rw [if_neg h]
    by_contra hne
    exact h (hg k hne)

theorem dvd_of_coeff_subst_X_pow_ne_zero {s : ℕ} (hs : s ≠ 0) (h : PowerSeries O) (k : ℕ)
    (hk : coeff k (PowerSeries.subst (X ^ s : PowerSeries O) h) ≠ 0) : s ∣ k := by
  rw [coeff_subst_X_pow_eq_ite_dvd hs] at hk
  by_contra hn
  exact hk (if_neg hn)

theorem coeff_sum_X_pow_mul_subst {s : ℕ} (hs : s ≠ 0) (a : Fin s → PowerSeries O)
    (j : Fin s) (m : ℕ) :
    coeff (s * m + j) (∑ i : Fin s, X ^ (i : ℕ) * PowerSeries.subst (X ^ s : PowerSeries O) (a i)) =
      coeff m (a j) := by
  rw [map_sum, Finset.sum_eq_single j]
  · try beta_reduce
    rw [coeff_X_pow_mul', if_pos (Nat.le_add_left _ _), Nat.add_sub_cancel, coeff_subst_X_pow_eq_ite_dvd hs,
      if_pos (dvd_mul_right s m), Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hs)]
  · intro i _ hij
    try beta_reduce
    rw [coeff_X_pow_mul']
    by_cases hle : (i : ℕ) ≤ s * m + j
    · rw [if_pos hle, coeff_subst_X_pow_eq_ite_dvd hs, if_neg]
      rintro ⟨t, ht⟩
      apply hij
      have h1 : (j : ℕ) + s * m = i + s * t := by omega
      have h2 : ((j : ℕ) + s * m) % s = ((i : ℕ) + s * t) % s := by rw [h1]
      rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.isLt,
        Nat.mod_eq_of_lt i.isLt] at h2
      exact Fin.ext h2.symm
    · rw [if_neg hle]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem existsUnique_sum_X_pow_mul_subst {s : ℕ} (hs : s ≠ 0) (g : PowerSeries O) :
    ∃! a : Fin s → PowerSeries O,
      g = ∑ i : Fin s, X ^ (i : ℕ) * PowerSeries.subst (X ^ s : PowerSeries O) (a i) := by
  refine ⟨fun i => mk fun m => coeff (s * m + i) g, ?_, ?_⟩
  · try beta_reduce
    ext k
    have hk : k = s * (k / s) + ((⟨k % s, Nat.mod_lt k (Nat.pos_of_ne_zero hs)⟩ : Fin s) : ℕ) :=
      (Nat.div_add_mod k s).symm
    rw [hk, coeff_sum_X_pow_mul_subst hs, coeff_mk]
  · intro b hb
    try beta_reduce at hb
    funext j
    ext m
    try beta_reduce
    rw [← coeff_sum_X_pow_mul_subst hs b j m, ← hb, coeff_mk]

end DualFramesAlt.EigenUniformiser
