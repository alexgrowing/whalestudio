import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SurjectiveOfLocallySurjective
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsPowMulPowEqOfIsZeroCechH

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CechDR GlobalTheory.HodgeCoh
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PD

section Hmap

variable {k : Type} [Field k] {M M' : Type} [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M']

def Cx.hmap (K : Cx k M) (L : Cx k M') (f : M →ₗ[k] M') (hf : IsMap K L f) (n : ℤ) : K.H n →ₗ[k] L.H n :=
  Submodule.mapQ _ _ ((f.restrict (p := K.Z n) (q := L.Z n) fun a ha => by
      refine ⟨(hf n a ha.1).1, ?_⟩
      change L.D (f a) = 0
      rw [← (hf n a ha.1).2]
      have : K.D a = 0 := ha.2
      rw [this, map_zero]))
    (by
      rintro ⟨a, ha⟩ hb
      obtain ⟨c, hc, e⟩ := hb
      refine ⟨f c, ?_, ?_⟩
      · have h1 := (hf (n - 1) c hc).1
        exact h1
      · change L.D (f c) = f a
        rw [← (hf (n - 1) c hc).2, e]; rfl)

end Hmap

section Pull

variable {k : Type} [Field k] {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {E E' : Type} [AddCommGroup E] [Module k E]
  [AddCommGroup E'] [Module k E']

def sortSign (τ : κ → ι) (s : Finset κ) : ℤ := ∏ a ∈ s, ∏ b ∈ s, if a < b ∧ τ b < τ a then -1 else 1

open Classical in

def pullC (τ : κ → ι) (φ : E →ₗ[k] E') : (Finset ι → E) →ₗ[k] (Finset κ → E') where
  toFun c s := if Set.InjOn τ s then sortSign τ s • φ (c (s.image τ)) else 0
  map_add' a b := by
    funext s
    by_cases h : Set.InjOn τ s <;> simp [h, smul_add]
  map_smul' r a := by
    funext s
    by_cases h : Set.InjOn τ s <;> simp [h, smul_comm (sortSign τ s) r]

end Pull

section Rat

variable (k : Type) [Field k] {K K' : Type} [Field K] [Field K'] [Algebra k K] [Algebra k K']

def IsDRMap (ψ : K →ₐ[k] K') (φ : DR k K →ₗ[k] DR k K') : Prop :=
  ∀ (q : ℕ) (b : K) (v : Fin q → K), φ (b • ExteriorAlgebra.ιMulti K q fun j => D k K (v j)) =
    ψ b • ExteriorAlgebra.ιMulti K' q fun j => D k K' (ψ (v j))

end Rat

end GlobalTheory.PD
