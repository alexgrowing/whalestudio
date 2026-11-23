import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.GramMat
open NumberField TensorProduct GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.Lines Matrix
open scoped ComplexOrder nonZeroDivisors

namespace GlobalTheory.CompanionTheory.Ar.Lines.Lift

open ComplexAt

noncomputable section

variable {L : Type} [Field L] [NumberField L] {K : Type} [Field K] [NumberField K] [Algebra L K]
  {E : Type} [AddCommGroup E] [Module (𝓞 L) E]

theorem coord_one_tmul (τ : K →+* ℂ) (b : 𝓞 K) (e : E) :
    baseChangeCoord τ ((1 : ComplexAt τ) ⊗ₜ[𝓞 K] (b ⊗ₜ[𝓞 L] e)) =
      τ (b : K) • ((1 : ComplexAt (τ.comp (algebraMap L K))) ⊗ₜ[𝓞 L] e) := by
  rw [baseChangeCoord_tmul, TensorProduct.smul_tmul']
  congr 1

theorem coord_smul (τ : K →+* ℂ) (b : 𝓞 K) (X : 𝓞 K ⊗[𝓞 L] E) :
    baseChangeCoord τ ((1 : ComplexAt τ) ⊗ₜ[𝓞 K] (b • X)) =
      τ (b : K) • baseChangeCoord τ ((1 : ComplexAt τ) ⊗ₜ[𝓞 K] X) := by
  induction X using TensorProduct.induction_on with
  | zero => simp
  | tmul c e =>
    rw [TensorProduct.smul_tmul', coord_one_tmul, coord_one_tmul, smul_eq_mul, smul_smul]
    simp
  | add X Y hX hY => rw [smul_add, tmul_add, map_add, hX, hY, tmul_add, map_add, smul_add]

theorem one_tmul_smul (σ : L →+* ℂ) (a : 𝓞 L) (e : E) :
    (1 : ComplexAt σ) ⊗ₜ[𝓞 L] (a • e) = σ (a : L) • ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e) := by
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_def, complex_smul_def]

theorem exists_lift (F : Submodule (𝓞 L) E) {i : ℕ} (f : Fin i → F) (c : F →ₗ[𝓞 L] (Fin i → L))
    (hc : ∀ x, ∃ (D : 𝓞 L) (a : Fin i → 𝓞 L), D ≠ 0 ∧ D • x = ∑ j, a j • f j ∧
      ∀ j, (D : L) * c x j = a j)
    (x : Fin i → K)
    (hx : x ∈ Submodule.span (𝓞 K) ((fun (w : Fin i → L) j => algebraMap L K (w j)) ''
      (LinearMap.range c : Submodule (𝓞 L) (Fin i → L)))) :
    ∃ X : 𝓞 K ⊗[𝓞 L] E, ∀ τ : K →+* ℂ,
      baseChangeCoord τ ((1 : ComplexAt τ) ⊗ₜ[𝓞 K] X) =
        ∑ j, τ (x j) • ((1 : ComplexAt (τ.comp (algebraMap L K))) ⊗ₜ[𝓞 L] (f j : E)) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, ⟨y, rfl⟩, rfl⟩ := hx
    obtain ⟨D, a, hD, hDy, ha⟩ := hc y
    refine ⟨(1 : 𝓞 K) ⊗ₜ[𝓞 L] (y : E), fun τ => ?_⟩
    rw [coord_one_tmul]
    have hD' : ((D : 𝓞 L) : L) ≠ 0 := by exact_mod_cast hD
    have hσ : (τ.comp (algebraMap L K)) (D : L) ≠ 0 := (map_ne_zero _).2 hD'
    have h1 : D • (y : E) = ∑ j, a j • (f j : E) := by
      have := congrArg Subtype.val hDy
      simpa using this
    have H : (τ.comp (algebraMap L K)) (D : L) •
        ((1 : ComplexAt (τ.comp (algebraMap L K))) ⊗ₜ[𝓞 L] (y : E)) =
        (τ.comp (algebraMap L K)) (D : L) •
          ∑ j, τ (algebraMap L K (c y j)) •
            ((1 : ComplexAt (τ.comp (algebraMap L K))) ⊗ₜ[𝓞 L] (f j : E)) := by
      rw [← one_tmul_smul, h1, tmul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [one_tmul_smul, smul_smul, ← ha j, map_mul]
      rfl
    have H2 := congrArg (fun v => ((τ.comp (algebraMap L K)) (D : L))⁻¹ • v) H
    simp only [inv_smul_smul₀ hσ] at H2
    simpa using H2
  | zero => exact ⟨0, fun τ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨X, hX⟩ := hx
    obtain ⟨Y, hY⟩ := hy
    refine ⟨X + Y, fun τ => ?_⟩
    rw [tmul_add, map_add, hX, hY, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.add_apply, map_add, add_smul]
  | smul b x _ hx =>
    obtain ⟨X, hX⟩ := hx
    refine ⟨b • X, fun τ => ?_⟩
    rw [coord_smul, hX, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, Pi.smul_apply, Algebra.smul_def, map_mul]

theorem lift_length : ∀ (L : Type) [Field L] [NumberField L] (B : HermitianBundle.{0} L) (F : Submodule (𝓞 L) B.carrier) (i : ℕ) (f : Fin i → F) (c : F →ₗ[𝓞 L] (Fin i → L)), (∀ x, ∃ (D : 𝓞 L) (a : Fin i → 𝓞 L), D ≠ 0 ∧ D • x = ∑ j, a j • f j ∧ ∀ j, (D : L) * c x j = a j) → ∀ (K : Type) [Field K] [NumberField K] [Algebra L K] (x : Fin i → K), x ∈ Submodule.span (𝓞 K) ((fun (w : Fin i → L) j => algebraMap L K (w j)) '' (LinearMap.range c : Submodule (𝓞 L) (Fin i → L))) → ∃ X : (B.baseChange K).carrier, ∀ τ : K →+* ℂ, ((B.baseChange K).metric.form τ).inner ((1 : ComplexAt τ) ⊗ₜ[𝓞 K] X) ((1 : ComplexAt τ) ⊗ₜ[𝓞 K] X) = star (fun j => τ (x j)) ⬝ᵥ (gramMat B (τ.comp (algebraMap L K)) (fun j => (f j : B.carrier)) *ᵥ fun j => τ (x j)) := by
  intro L _ _ B F i f c hc K _ _ _ x hx
  obtain ⟨X, hX⟩ := exists_lift F f c hc x hx
  refine ⟨X, fun τ => ?_⟩
  change inner ℂ (FibreSpace.equiv B.metric (τ.comp (algebraMap L K))
      (baseChangeCoord τ ((1 : ComplexAt τ) ⊗ₜ[𝓞 K] X)))
    (FibreSpace.equiv B.metric (τ.comp (algebraMap L K))
      (baseChangeCoord τ ((1 : ComplexAt τ) ⊗ₜ[𝓞 K] X))) = _
  rw [hX τ]
  simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [starRingEnd_apply]
  have e : gramMat B (τ.comp (algebraMap L K)) (fun j => (f j : B.carrier)) a b =
      inner ℂ (FibreSpace.equiv B.metric (τ.comp (algebraMap L K))
          ((1 : ComplexAt (τ.comp (algebraMap L K))) ⊗ₜ[𝓞 L] (f a : B.carrier)))
        (FibreSpace.equiv B.metric (τ.comp (algebraMap L K))
          ((1 : ComplexAt (τ.comp (algebraMap L K))) ⊗ₜ[𝓞 L] (f b : B.carrier))) := rfl
  rw [e]
  ring

end

end GlobalTheory.CompanionTheory.Ar.Lines.Lift
