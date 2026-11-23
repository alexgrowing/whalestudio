import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.UnitProdAlg

variable {F : Type} [Field F] [NumberField F]

theorem mulSupport_finite {a : ℝ≥0} {c : HeightOneSpectrum (𝓞 F) → ℝ≥0} (h : IsUnitProd a c) :
    (Function.mulSupport c).Finite := by
  have := h.1
  rw [Filter.eventually_cofinite] at this
  exact this

theorem map_hom (f : ℝ≥0 →* ℝ≥0) {a : ℝ≥0} {c : HeightOneSpectrum (𝓞 F) → ℝ≥0}
    (h : IsUnitProd a c) : IsUnitProd (f a) (fun v => f (c v)) := by
  have hfin := mulSupport_finite h
  refine ⟨h.1.mono fun v hv => by simp [hv], ?_⟩
  have hsub : Function.mulSupport (fun v => f (c v)) ⊆ (hfin.toFinset : Set _) := by
    intro v hv
    simp only [Function.mem_mulSupport] at hv
    simp only [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h1
    exact hv (by simp [h1])
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub, ← map_prod, ← map_mul,
    ← finprod_eq_prod_of_mulSupport_subset c (by simp), h.2, map_one]

def sqrtHom : ℝ≥0 →* ℝ≥0 where
  toFun := NNReal.sqrt
  map_one' := NNReal.sqrt_one
  map_mul' := NNReal.sqrt_mul

theorem mul {a b : ℝ≥0} {c e : HeightOneSpectrum (𝓞 F) → ℝ≥0}
    (h : IsUnitProd a c) (k : IsUnitProd b e) : IsUnitProd (a * b) (fun v => c v * e v) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [h.1, k.1] with v h1 h2
    simp [h1, h2]
  · rw [finprod_mul_distrib (mulSupport_finite h) (mulSupport_finite k), mul_mul_mul_comm,
      h.2, k.2, one_mul]

theorem ne_zero {a : ℝ≥0} {c : HeightOneSpectrum (𝓞 F) → ℝ≥0} (h : IsUnitProd a c) : a ≠ 0 := by
  rintro rfl
  simpa using h.2

theorem family_ne_zero {a : ℝ≥0} {c : HeightOneSpectrum (𝓞 F) → ℝ≥0} (h : IsUnitProd a c)
    (v : HeightOneSpectrum (𝓞 F)) : c v ≠ 0 := by
  intro hv
  have h2 := h.2
  rw [finprod_eq_zero c v hv (mulSupport_finite h)] at h2
  simp at h2

theorem inv {a : ℝ≥0} {c : HeightOneSpectrum (𝓞 F) → ℝ≥0} (h : IsUnitProd a c) :
    IsUnitProd a⁻¹ (fun v => (c v)⁻¹) :=
  map_hom (invMonoidWithZeroHom (G₀ := ℝ≥0) : ℝ≥0 →* ℝ≥0) h

theorem main : ∀ (F : Type) [Field F] [NumberField F] (a b : ℝ≥0)
    (c e : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd a c → IsUnitProd b e →
    a ≠ 0 ∧ (∀ v, c v ≠ 0) ∧ IsUnitProd (a * b) (fun v => c v * e v) ∧
    IsUnitProd a⁻¹ (fun v => (c v)⁻¹) ∧ IsUnitProd (a / b) (fun v => c v / e v) ∧
    IsUnitProd (NNReal.sqrt a) (fun v => NNReal.sqrt (c v)) ∧
    (∀ n : ℕ, IsUnitProd (a ^ n) (fun v => c v ^ n)) ∧
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S →
      (∀ v, v ∉ S → c v = 1) ∧ a * ∏ v ∈ S, c v = 1 := by
  intro F _ _ a b c e h k
  refine ⟨ne_zero h, family_ne_zero h, mul h k, inv h, ?_, map_hom sqrtHom h,
    fun n => map_hom (powMonoidHom n) h, (mulSupport_finite h).toFinset, fun S hS => ?_⟩
  · simpa only [div_eq_mul_inv] using mul h (inv k)
  · have hsub : Function.mulSupport c ⊆ (S : Set _) := by
      intro v hv
      exact hS ((mulSupport_finite h).mem_toFinset.2 hv)
    refine ⟨fun v hv => ?_, ?_⟩
    · by_contra hne
      exact hv (hsub hne)
    · rw [← finprod_eq_prod_of_mulSupport_subset c hsub]
      exact h.2

end GlobalTheory.CompanionTheory.SW.UnitProdAlg
