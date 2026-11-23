import Mathlib
open NumberField

namespace GlobalTheory

theorem ringOfIntegers_ringHom_injective {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (σ : 𝓞 E →+* 𝓞 K) : Function.Injective σ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  rw [eq_bot_iff]
  intro n hn
  rw [Ideal.mem_comap, RingHom.mem_ker] at hn
  simpa using hn

theorem sum_log_norm_embeddings {K : Type} [Field K] [NumberField K] (y : K) :
    ∑ s : K →+* ℂ, Real.log ‖s y‖ = Real.log |((Algebra.norm ℚ y : ℚ) : ℝ)| := by
  by_cases hy : y = 0
  · subst hy
    simp
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ y
  have h2 : ∏ s : K →+* ℂ, s y = ∏ s : K →ₐ[ℚ] ℂ, s y :=
    Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun s => rfl)
  rw [← Real.log_prod (fun s _ => by simpa using hy), ← norm_prod, h2, ← h]
  congr 1
  rw [eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]

theorem mean_log_norm_embeddings_ringHom :
    ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (σ : 𝓞 E →+* 𝓞 K) (x : 𝓞 E),
  (∑ s : K →+* ℂ, Real.log ‖s (σ x : K)‖) / Module.finrank ℚ K =
    Real.log |((Algebra.norm ℚ (x : E) : ℚ) : ℝ)| / Module.finrank ℚ E := by
  intro E K _ _ _ _ σ x
  have hinj : Function.Injective ((algebraMap (𝓞 K) K).comp σ) :=
    (RingOfIntegers.coe_injective).comp (ringOfIntegers_ringHom_injective σ)
  let τ : E →+* K := IsFractionRing.lift hinj
  have hτ : τ (x : E) = (σ x : K) := IsFractionRing.lift_algebraMap hinj x
  letI : Algebra E K := τ.toAlgebra
  haveI : IsScalarTower ℚ E K := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : Module.Finite E K := Module.Finite.of_restrictScalars_finite ℚ E K
  have hx : (σ x : K) = algebraMap E K (x : E) := hτ.symm
  rw [sum_log_norm_embeddings, hx, ← Algebra.norm_norm (S := E), Algebra.norm_algebraMap, map_pow,
    ← Module.finrank_mul_finrank ℚ E K]
  have h1 : (Module.finrank ℚ E : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have h2 : (Module.finrank E K : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  push_cast
  rw [abs_pow, Real.log_pow]
  field_simp

end GlobalTheory
