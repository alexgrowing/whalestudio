import Formalism.WeaklyAdmissibleFiltrations.CocyclesFunctorial

noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

open LaurentPolynomial

def lpScaleF (c : ℚˣ) : Multiplicative ℤ →* LaurentPolynomial ℚ where
  toFun m := ((c ^ m.toAdd : ℚˣ) : ℚ) • T m.toAdd
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul, zpow_add, Units.val_mul, T_add, smul_mul_smul_comm]

@[simp] lemma lpScaleF_apply (c : ℚˣ) (m : Multiplicative ℤ) :
    lpScaleF c m = ((c ^ m.toAdd : ℚˣ) : ℚ) • T m.toAdd := rfl

def lpScale (c : ℚˣ) : LaurentPolynomial ℚ →ₐ[ℚ] LaurentPolynomial ℚ :=
  AddMonoidAlgebra.lift ℚ (LaurentPolynomial ℚ) ℤ (lpScaleF c)

lemma lpScale_coeff (c : ℚˣ) (f : LaurentPolynomial ℚ) (m : ℤ) :
    (lpScale c f).coeff m = ((c ^ m : ℚˣ) : ℚ) * f.coeff m := by
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      Finsupp.add_apply, hp, hq, mul_add]
  | C_mul_T n a =>
    have h1 : lpScale c (T n) = ((c ^ n : ℚˣ) : ℚ) • T n := by
      unfold lpScale T
      rw [AddMonoidAlgebra.lift_single, one_smul, lpScaleF_apply]
      rfl
    have h2 : (C a * T n : LaurentPolynomial ℚ) = a • T n := by
      rw [C_eq_algebraMap, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    rw [h2, map_smul, h1, smul_smul, AddMonoidAlgebra.coeff_smul_apply,
      AddMonoidAlgebra.coeff_smul_apply, T_apply, smul_eq_mul, smul_eq_mul]
    by_cases h : n = m
    · subst h
      simp only [if_true]
      ring
    · simp [h]

def lpScaleE (c : ℚˣ) : LaurentPolynomial ℚ ≃ₐ[ℚ] LaurentPolynomial ℚ :=
  AlgEquiv.ofAlgHom (lpScale c) (lpScale c⁻¹)
    (AlgHom.ext fun f => LaurentPolynomial.ext fun m => by
      simp [lpScale_coeff, ← mul_assoc]
      rw [mul_inv_cancel₀ (zpow_ne_zero _ c.ne_zero), one_mul])
    (AlgHom.ext fun f => LaurentPolynomial.ext fun m => by
      simp [lpScale_coeff, ← mul_assoc]
      rw [inv_mul_cancel₀ (zpow_ne_zero _ c.ne_zero), one_mul])

lemma lpScaleE_coeff (c : ℚˣ) (f : LaurentPolynomial ℚ) (m : ℤ) :
    (lpScaleE c f).coeff m = ((c ^ m : ℚˣ) : ℚ) * f.coeff m := by
  show (lpScale c f).coeff m = _
  rw [lpScale_coeff]

def lpScaleHom : ℚˣ →* (LaurentPolynomial ℚ ≃ₐ[ℚ] LaurentPolynomial ℚ) where
  toFun := lpScaleE
  map_one' := AlgEquiv.ext fun f => LaurentPolynomial.ext fun m => by simp [lpScaleE_coeff]
  map_mul' c d := AlgEquiv.ext fun f => LaurentPolynomial.ext fun m => by
    simp [lpScaleE_coeff, AlgEquiv.mul_apply, mul_zpow, mul_assoc]

@[simp] lemma lpScaleHom_apply (c : ℚˣ) : lpScaleHom c = lpScaleE c := rfl

def lpTwo : ℚˣ := Units.mk0 2 (by norm_num)

@[simp] lemma lpTwo_val : (lpTwo : ℚ) = 2 := rfl

@[simp] lemma lpTwo_zpow (m : ℤ) : ((lpTwo ^ m : ℚˣ) : ℚ) = (2 : ℚ) ^ m := by
  rw [Units.val_zpow_eq_zpow_val, lpTwo_val]

lemma lpTwo_fix (f : LaurentPolynomial ℚ) (h : lpScaleE lpTwo f = f) :
    algebraMap ℚ (LaurentPolynomial ℚ) (f.coeff 0) = f := by
  refine LaurentPolynomial.ext fun a => ?_
  rw [← C_eq_algebraMap, C_apply]
  by_cases ha : a = 0
  · rw [if_pos ha, ha]
  · rw [if_neg ha]
    have h' := congrArg (fun g : LaurentPolynomial ℚ => g.coeff a) h
    simp only [lpScaleE_coeff, lpTwo_zpow] at h'
    have h2 : (2 : ℚ) ^ a ≠ 1 := fun h1 => ha ((zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)).mp h1)
    have h3 : ((2 : ℚ) ^ a - 1) * f.coeff a = 0 := by rw [sub_mul, h', one_mul, sub_self]
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd (sub_eq_zero.mp h4) h2
    · exact h4.symm

def lpFil (a : ℤ) : Submodule ℚ (LaurentPolynomial ℚ) where
  carrier := {f | ∀ m < a, f.coeff m = 0}
  add_mem' {x y} hx hy m hm := by simp [AddMonoidAlgebra.coeff_add, hx m hm, hy m hm]
  zero_mem' m _ := by simp
  smul_mem' c x hx m hm := by simp [hx m hm]

lemma lpFil_mul (a b : ℤ) (x y : LaurentPolynomial ℚ) (hx : x ∈ lpFil a) (hy : y ∈ lpFil b) :
    x * y ∈ lpFil (a + b) := by
  classical
  intro m hm
  rw [AddMonoidAlgebra.coeff_mul]
  simp only [Finsupp.sum]
  refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
  rw [if_neg]
  intro hij
  have hi' : ¬ i < a := fun h => (Finsupp.mem_support_iff.mp hi) (hx i h)
  have hj' : ¬ j < b := fun h => (Finsupp.mem_support_iff.mp hj) (hy j h)
  omega

theorem existsPeriodRingData_holds : ExPD := by
  let χ : Multiplicative ℤ →* ℚˣ := zpowersHom ℚˣ lpTwo
  let act : Multiplicative ℤ →* (LaurentPolynomial ℚ ≃ₐ[ℚ] LaurentPolynomial ℚ) := lpScaleHom.comp χ
  have hact : ∀ g (f : LaurentPolynomial ℚ) m, (act g f).coeff m = ((χ g ^ m : ℚˣ) : ℚ) * f.coeff m := by
    intro g f m
    exact lpScaleE_coeff (χ g) f m
  have hone : act (Multiplicative.ofAdd 1) = lpScaleE lpTwo := by
    show lpScaleE (χ (Multiplicative.ofAdd 1)) = lpScaleE lpTwo
    simp [χ]
  have hfix : ∀ f : LaurentPolynomial ℚ, (∀ g, act g f = f) → ∃ c : ℚ, algebraMap ℚ _ c = f := by
    intro f hf
    refine ⟨f.coeff 0, lpTwo_fix f ?_⟩
    have := hf (Multiplicative.ofAdd 1)
    rwa [hone] at this
  exact ⟨{
    p := 2
    hp := Nat.prime_two
    finK₀ := inferInstance
    finK := inferInstance
    σ := AlgHom.id ℚ ℚ
    σ_bij := ⟨fun _ _ h => h, fun b => ⟨b, rfl⟩⟩
    actB := act
    invB := hfix
    φ := (lpScaleE lpTwo).toAlgHom
    φ_inj := (lpScaleE lpTwo).injective
    φ_K₀ := fun c => (lpScaleE lpTwo).toAlgHom.commutes c
    φ_comm := fun g b => LaurentPolynomial.ext fun m => by
      change (lpScaleE lpTwo (act g b)).coeff m = (act g (lpScaleE lpTwo b)).coeff m
      rw [lpScaleE_coeff, hact, hact, lpScaleE_coeff]
      ring
    actdR := act
    invdR := hfix
    ι := AlgHom.id ℚ _
    ι_inj := fun _ _ h => h
    ι_comm := fun _ _ => rfl
    Fil := lpFil
    Fil_anti := fun a f hf m hm => hf m (by omega)
    one_mem := fun m hm => by rw [← T_zero, T_apply, if_neg (by omega)]
    Fil_mul := lpFil_mul
    Fil_exh := fun x => by
      refine ⟨-(∑ i ∈ x.coeff.support, |i|), fun m hm => ?_⟩
      by_contra hne
      have hm' : m ∈ x.coeff.support := Finsupp.mem_support_iff.mpr hne
      have h1 := Finset.single_le_sum (f := fun i : ℤ => |i|) (fun i _ => abs_nonneg i) hm'
      have h2 := neg_abs_le m
      linarith
    Fil_sep := fun x hx => LaurentPolynomial.ext fun m => by
      rw [hx (m + 1) m (by omega)]
      rfl
    Fil_G := fun g a x hx m hm => by rw [hact, hx m hm, mul_zero]
    χ := χ
    t := T 1
    t_unit := isUnit_T 1
    t_act := fun g => LaurentPolynomial.ext fun m => by
      rw [hact, AddMonoidAlgebra.coeff_smul_apply, T_apply, smul_eq_mul]
      by_cases h : (1 : ℤ) = m
      · subst h
        simp
      · simp [h]
    t_φ := LaurentPolynomial.ext fun m => by
      change (lpScaleE lpTwo (T 1)).coeff m = _
      rw [lpScaleE_coeff, AddMonoidAlgebra.coeff_smul_apply, T_apply, smul_eq_mul, lpTwo_zpow]
      by_cases h : (1 : ℤ) = m
      · subst h
        norm_num
      · simp [h]
    mem_filtration_one := fun m hm => by rw [AlgHom.id_apply, T_apply, if_neg (by omega)]
    not_mem_filtration_two := fun h => by
      have h1 := h 1 (by norm_num)
      rw [AlgHom.id_apply, T_apply, if_pos rfl] at h1
      exact one_ne_zero h1
    fund := fun b hb _ => ⟨b.coeff 0, lpTwo_fix b hb⟩ }⟩

end Formalism.WeaklyAdmissibleFiltrations
