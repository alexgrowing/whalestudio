import Mathlib
set_option autoImplicit false

namespace GlobalTheory

theorem points_separate_localization_away (R K C : Type) [CommRing R] [Field K] [Algebra R K]
    [CommRing C] [Algebra R C] (h : ∀ a : C, (∀ ψ : C →ₐ[R] K, ψ a = 0) → a = 0)
    (e : C) (y : Localization.Away e)
    (hy : ∀ χ : Localization.Away e →ₐ[R] K, χ y = 0) : y = 0 := by
  obtain ⟨n, x, hx⟩ := IsLocalization.Away.surj e y
  have hxe : x * e = 0 := by
    apply h
    intro ψ
    rw [map_mul]
    by_cases he : ψ e = 0
    · rw [he, mul_zero]
    · have hu : IsUnit ((ψ : C →+* K) e) := Ne.isUnit he
      let f : Localization.Away e →+* K := IsLocalization.Away.lift e hu
      have hf : ∀ c : C, f (algebraMap C (Localization.Away e) c) = ψ c := fun c =>
        IsLocalization.Away.lift_eq e hu c
      let χ : Localization.Away e →ₐ[R] K :=
        { f with
          commutes' := fun r => by
            change f (algebraMap R (Localization.Away e) r) = _
            rw [IsScalarTower.algebraMap_apply R C (Localization.Away e), hf, AlgHom.commutes] }
      have h0 : f y = 0 := hy χ
      have : ψ x = 0 := by
        rw [← hf x, ← hx, map_mul, h0, zero_mul]
      rw [this, zero_mul]
  have hue : IsUnit (algebraMap C (Localization.Away e) e) :=
    IsLocalization.Away.algebraMap_isUnit e
  have h1 : y * algebraMap C (Localization.Away e) e ^ (n + 1) = 0 := by
    rw [pow_succ, ← mul_assoc, hx, ← map_mul, hxe, map_zero]
  exact (hue.pow (n + 1)).mul_left_eq_zero.mp h1

end GlobalTheory
