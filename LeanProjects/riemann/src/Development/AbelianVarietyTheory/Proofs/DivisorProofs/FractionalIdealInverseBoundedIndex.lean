import Mathlib

open scoped nonZeroDivisors

namespace GlobalTheory

theorem exists_den_of_fg {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] (I : Submodule A K) (hI : I.FG) :
    ∃ d : A, d ≠ 0 ∧ ∀ y ∈ I, ∃ a : A, algebraMap A K a = algebraMap A K d * y := by
  obtain ⟨s, rfl⟩ := hI
  obtain ⟨⟨d, hd⟩, h⟩ := IsLocalization.exist_integer_multiples_of_finset A⁰ s
  refine ⟨d, nonZeroDivisors.ne_zero hd, fun y hy => ?_⟩
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha⟩ := h x hx
    exact ⟨a, by rw [ha]; exact Algebra.smul_def d x⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, ha, hb, mul_add]⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c * a, by rw [map_mul, ha, Algebra.smul_def]; ring⟩

theorem exists_principal_mul_integral_ideal_contains_int :
    ∀ (A K : Type) [CommRing A] [IsDomain A] [CharZero A] [Module.Finite ℤ A]
    [Field K] [Algebra A K] [IsFractionRing A K],
    ∃ M : ℤ, M ≠ 0 ∧ ∀ I J : Submodule A K, I * J = 1 →
      ∃ x : K, x ≠ 0 ∧ Submodule.span A {x} * I ≤ 1 ∧ (M : K) ∈ Submodule.span A {x} * I := by
  intro A K _ _ _ _ _ _ _
  haveI : Module.Free ℤ A := Module.free_of_finite_type_torsion_free'
  classical
  let bS := Module.Free.chooseBasis ℤ A
  have adm : (AbsoluteValue.abs : AbsoluteValue ℤ ℤ).IsAdmissible := AbsoluteValue.absIsAdmissible
  have hM0 : (∏ m ∈ ClassGroup.finsetApprox bS adm, m) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro m hm h
    subst h
    exact ClassGroup.finsetApprox.zero_notMem bS adm hm
  refine ⟨∏ m ∈ ClassGroup.finsetApprox bS adm, m, hM0, ?_⟩
  intro I J hIJ
  set M := ∏ m ∈ ClassGroup.finsetApprox bS adm, m with hMdef
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hMK : (M : K) ≠ 0 := by
    rw [← map_intCast (algebraMap A K)]
    exact (map_ne_zero_iff _ hinj).2 (Int.cast_ne_zero.2 hM0)
  have hFG : I.FG := Submodule.fg_unit (Units.mkOfMulEqOne I J hIJ)
  obtain ⟨d, hd0, hd⟩ := exists_den_of_fg I hFG
  have hdK : algebraMap A K d ≠ 0 := (map_ne_zero_iff _ hinj).2 hd0
  let f : A →ₗ[A] K := (LinearMap.mulLeft A (algebraMap A K d)⁻¹) ∘ₗ Algebra.linearMap A K
  let I₀ : Ideal A := I.comap f
  have hmem : ∀ a, a ∈ I₀ ↔ (algebraMap A K d)⁻¹ * algebraMap A K a ∈ I := fun a => Iff.rfl
  have hIbot : I ≠ ⊥ := by
    intro h
    rw [h, Submodule.bot_mul] at hIJ
    have : (1 : K) ∈ (1 : Submodule A K) := Submodule.mem_one.2 ⟨1, map_one _⟩
    rw [← hIJ, Submodule.mem_bot] at this
    exact one_ne_zero this
  obtain ⟨y, hyI, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hIbot
  obtain ⟨a0, ha0⟩ := hd y hyI
  have hI₀ : I₀ ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    refine ⟨a0, (hmem a0).2 ?_, ?_⟩
    · rw [ha0, ← mul_assoc, inv_mul_cancel₀ hdK, one_mul]; exact hyI
    · rintro rfl
      rw [map_zero] at ha0
      exact mul_ne_zero hdK hy0 ha0.symm
  obtain ⟨b, hbI, hb0, hbmin⟩ :=
    ClassGroup.exists_min AbsoluteValue.abs ⟨I₀, mem_nonZeroDivisors_of_ne_zero hI₀⟩
  have key : ∀ a ∈ I₀, ∃ c : A, (M : A) * a = b * c := by
    intro a ha
    obtain ⟨q, r, hr, hlt⟩ := ClassGroup.exists_mem_finset_approx' bS adm a hb0
    have hsub : r • a - q * b ∈ I₀ := by
      rw [zsmul_eq_mul]
      exact I₀.sub_mem (I₀.mul_mem_left _ ha) (I₀.mul_mem_left q hbI)
    have hz := hbmin _ hsub hlt
    rw [sub_eq_zero, zsmul_eq_mul] at hz
    obtain ⟨k, hk⟩ : r ∣ M := Finset.dvd_prod_of_mem _ hr
    refine ⟨k * q, ?_⟩
    rw [hk, Int.cast_mul]
    linear_combination (k : A) * hz
  have hbK : algebraMap A K b ≠ 0 := (map_ne_zero_iff _ hinj).2 hb0
  refine ⟨(M : K) * algebraMap A K d / algebraMap A K b,
    div_ne_zero (mul_ne_zero hMK hdK) hbK, ?_, ?_⟩
  · refine Submodule.mul_le.2 fun u hu z hz => ?_
    obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.1 hu
    obtain ⟨a, ha⟩ := hd z hz
    have haI : a ∈ I₀ := (hmem a).2 (by rw [ha, ← mul_assoc, inv_mul_cancel₀ hdK, one_mul]; exact hz)
    obtain ⟨c, hc⟩ := key a haI
    have hcK : (M : K) * algebraMap A K a = algebraMap A K b * algebraMap A K c := by
      have := congrArg (algebraMap A K) hc
      rwa [map_mul, map_mul, map_intCast] at this
    refine Submodule.mem_one.2 ⟨α * c, ?_⟩
    rw [Algebra.smul_def, map_mul]
    field_simp
    linear_combination (-(algebraMap A K α)) * hcK + algebraMap A K α * (M : K) * ha
  · have hbI' : (algebraMap A K d)⁻¹ * algebraMap A K b ∈ I := (hmem b).1 hbI
    convert Submodule.mul_mem_mul (Submodule.mem_span_singleton_self
      ((M : K) * algebraMap A K d / algebraMap A K b)) hbI' using 1
    field_simp

end GlobalTheory
