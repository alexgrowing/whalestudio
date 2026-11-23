import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsOrbitProd

open NumberField IsDedekindDomain ValuativeRel
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.FunExt

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.FunExt.ConjLift

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [Field Ω] [Algebra K Ω] [Algebra L Ω]

theorem mem_Dec_of_iff {F : Type} [Field F] [NumberField F] [Algebra F Ω] {A : ValuationSubring Ω} {σ : G F Ω}
    (hσ : ∀ x, σ x ∈ A ↔ x ∈ A) : σ ∈ Dec (F := F) A := by
  rw [mem_Dec]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← hσ]
  show (σ * σ⁻¹) x ∈ A ↔ x ∈ A
  rw [mul_inv_cancel]; rfl

variable (s : L ≃ₐ[K] L) (g : G K Ω) (hgs : ∀ x : L, g (algebraMap L Ω x) = algebraMap L Ω (s x))
include hgs

def conjL (τ : G L Ω) : G L Ω :=
  AlgEquiv.ofRingEquiv (f := g.toRingEquiv.trans (τ.toRingEquiv.trans g.symm.toRingEquiv)) fun x => by
    show g.symm (τ (g (algebraMap L Ω x))) = algebraMap L Ω x
    rw [hgs, AlgEquiv.commutes, AlgEquiv.symm_apply_eq, hgs]

omit [NumberField K] [NumberField L] in
@[simp] theorem conjL_apply (τ : G L Ω) (z : Ω) : conjL s g hgs τ z = g⁻¹ (τ (g z)) := rfl

variable {A : ValuationSubring Ω}

theorem conjL_mem_Weil (hgA : g ∈ Dec (F := K) A) {u : HeightOneSpectrum (𝓞 L)} (h' : IsPlaceOver A u)
    {τ : G L Ω} (hτ : τ ∈ Weil h') : conjL s g hgs τ ∈ Weil h' := by
  obtain ⟨a, b, hD, hab⟩ := hτ
  have hgi : g⁻¹ ∈ Dec (F := K) A := (Dec (F := K) A).inv_mem hgA
  refine ⟨a, b, mem_Dec_of_iff fun x => ?_, fun x hx => ?_⟩
  · rw [conjL_apply, apply_mem_iff_of_mem_Dec hgi, apply_mem_iff_of_mem_Dec hD, apply_mem_iff_of_mem_Dec hgA]
  · have hy : A.valuation (g x) ≤ 1 := val_apply_le_one hgA hx
    have h1 := hab (g x) hy
    rw [← valuation_apply_lt_one_iff hgi] at h1
    have e : (g⁻¹ : G K Ω) ((τ (g x)) ^ (normV u ^ b) - (g x) ^ (normV u ^ a)) =
        (conjL s g hgs τ x) ^ (normV u ^ b) - x ^ (normV u ^ a) := by
      rw [map_sub, map_pow, map_pow, conjL_apply]
      congr 2
      show (g⁻¹ * g) x = x
      rw [inv_mul_cancel]; rfl
    rwa [e] at h1

def conjW (hgA : g ∈ Dec (F := K) A) {u : HeightOneSpectrum (𝓞 L)} (h' : IsPlaceOver A u) (τ : Weil h') : Weil h' :=
  ⟨conjL s g hgs τ, conjL_mem_Weil s g hgs hgA h' τ.2⟩

@[simp] theorem coe_conjW (hgA : g ∈ Dec (F := K) A) {u : HeightOneSpectrum (𝓞 L)} (h' : IsPlaceOver A u) (τ : Weil h')
    (z : Ω) : (conjW s g hgs hgA h' τ : G L Ω) z = g⁻¹ ((τ : G L Ω) (g z)) := rfl

omit hgs

end GlobalTheory.FunExt.ConjLift
