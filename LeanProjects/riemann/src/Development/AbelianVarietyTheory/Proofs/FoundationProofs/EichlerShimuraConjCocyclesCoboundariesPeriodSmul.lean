import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem polySlash_map_conj (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    (slP w g p).map (starRingEnd ℂ) = slP w g (p.map (starRingEnd ℂ)) := by
  simp only [slP, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.toSpanSingleton_apply, lcoeff_apply, Polynomial.map_sum, Polynomial.map_smul,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
    map_intCast, coeff_map, Polynomial.map_intCast, Polynomial.map_natCast]

theorem eichler_smul (w : ℕ) (c : ℂ) (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    eichler w (c • f) τ = c • eichler w f τ := by
  simp only [eichler, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_eq_C_mul, ← mul_assoc, ← C_mul]
  congr 2
  have : ∀ t : ℝ, ((c • f) ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
        (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ (w - j) * ((τ : ℂ) - Complex.I) =
      c * ((f ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
        (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ (w - j) * ((τ : ℂ) - Complex.I)) := by
    intro t; simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]; ring
  simp_rw [this, intervalIntegral.integral_const_mul]
  ring

end GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.HeckeFamilyMatrices

theorem polynomialMapCoeffConj_mem_eichlerShimuraCocycles (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (z : Γ → ℂ[X]) (hz : z ∈ Z1 Γ w) : cj z ∈ Z1 Γ w := by
  obtain ⟨h1, h2⟩ := hz
  refine ⟨fun γ => ?_, fun γ δ => ?_⟩
  · have := h1 γ
    rw [mem_degreeLT] at this ⊢
    exact lt_of_le_of_lt (degree_map_le) this
  · simp only [cj, h2, Polynomial.map_add, polySlash_map_conj]

theorem polynomialMapCoeffConj_mem_eichlerShimuraCoboundaries (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (z : Γ → ℂ[X]) (hz : z ∈ B1 Γ w) : cj z ∈ B1 Γ w := by
  obtain ⟨⟨p, hp⟩, rfl⟩ := hz
  have hp' : p.map (starRingEnd ℂ) ∈ degreeLT ℂ (w + 1) := by
    rw [mem_degreeLT] at hp ⊢
    exact lt_of_le_of_lt (degree_map_le) hp
  refine ⟨⟨p.map (starRingEnd ℂ), hp'⟩, ?_⟩
  funext γ
  simp only [cj, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.pi_apply,
    LinearMap.sub_apply, LinearMap.id_apply, Polynomial.map_sub, polySlash_map_conj]

theorem per_smul (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (f : ℍ → ℂ) (c : ℂ) :
    per Γ w (c • f) = c • per Γ w f := by
  funext γ
  simp only [per, Pi.smul_apply, eichler_smul, map_smul]

theorem cj_mem_Z1_cj_mem_B1_per_smul : ∀ (Γ : Subgroup SL(2, ℤ)) (w : ℕ), (∀ z ∈ Z1 Γ w, cj z ∈ Z1 Γ w) ∧
    (∀ z ∈ B1 Γ w, cj z ∈ B1 Γ w) ∧ ∀ (f : ℍ → ℂ) (c : ℂ), per Γ w (c • f) = c • per Γ w f :=
  fun Γ w => ⟨polynomialMapCoeffConj_mem_eichlerShimuraCocycles Γ w, polynomialMapCoeffConj_mem_eichlerShimuraCoboundaries Γ w, per_smul Γ w⟩

end GlobalTheory.HeckeFamilyMatrices
