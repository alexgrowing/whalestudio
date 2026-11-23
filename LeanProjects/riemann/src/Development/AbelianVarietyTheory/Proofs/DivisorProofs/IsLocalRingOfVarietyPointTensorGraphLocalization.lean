import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalization
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.DiagLoc

theorem isLocModel_loc : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ']
  [Algebra ℂ L] [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L]
  [IsFractionRing (K ⊗[ℂ] κ') L] (σ : K →ₐ[ℂ] κ'),
  Algebra.EssFiniteType ℂ K → Algebra.EssFiniteType ℂ κ' →
  IsLocModel (algebraMap ℂ L) (GlobalTheory.DiagLoc.loc L σ) := by
  intro K κ' L _ _ _ _ _ _ _ _ _ σ hK hκ
  have hc : ∀ a : ℂ, algebraMap ℂ L a ∈ loc L σ := fun a => by
    rw [IsScalarTower.algebraMap_apply ℂ (K ⊗[ℂ] κ') L]
    exact (toLoc L σ (algebraMap ℂ (K ⊗[ℂ] κ') a)).2
  refine
    { const_mem := hc
      isLocalRing := inferInstance
      essFiniteType := ?_
      frac := ?_ }
  · have e : (algebraMap ℂ L).codRestrict (loc L σ) hc =
        (toLoc L σ).comp (algebraMap ℂ (K ⊗[ℂ] κ')) := by
      ext a
      simp only [RingHom.codRestrict_apply, RingHom.comp_apply, coe_toLoc]
      exact IsScalarTower.algebraMap_apply ℂ (K ⊗[ℂ] κ') L a
    rw [e]
    haveI : Algebra.EssFiniteType K (K ⊗[ℂ] κ') := Algebra.EssFiniteType.baseChange ℂ κ' K
    haveI : Algebra.EssFiniteType ℂ (K ⊗[ℂ] κ') := Algebra.EssFiniteType.comp ℂ K (K ⊗[ℂ] κ')
    have h1 : (algebraMap ℂ (K ⊗[ℂ] κ')).EssFiniteType := RingHom.essFiniteType_algebraMap.2 this
    haveI : Algebra.EssFiniteType (K ⊗[ℂ] κ') (loc L σ) :=
      Algebra.EssFiniteType.of_isLocalization (loc L σ) (ker σ).primeCompl
    have h2 : (toLoc L σ).EssFiniteType := by
      rw [← algebraMap_loc]; exact RingHom.essFiniteType_algebraMap.2 this
    exact RingHom.EssFiniteType.comp h1 h2
  · intro f
    obtain ⟨a, b, hb, e⟩ := IsFractionRing.div_surjective (A := K ⊗[ℂ] κ') f
    have hb0 : algebraMap (K ⊗[ℂ] κ') L b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    refine ⟨_, (toLoc L σ a).2, _, (toLoc L σ b).2, hb0, ?_⟩
    rw [coe_toLoc, coe_toLoc, ← e, div_mul_cancel₀ _ hb0]

end GlobalTheory.DiagLoc
