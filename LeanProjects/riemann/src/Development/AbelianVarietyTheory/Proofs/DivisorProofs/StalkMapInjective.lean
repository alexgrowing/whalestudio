import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotSteepOnOfGermZero

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HSApp.ValCrit

open IsLocalRing

theorem exists_valuation (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] :
    ∃ μ : Valuation R (WithZero (Multiplicative ℤ)),
      (∀ a, μ a ≤ 1) ∧ (∀ a ∈ maximalIdeal R, μ a < 1) ∧ ∀ a, μ a = 0 → a = 0 := by
  classical
  by_cases hf : IsField R
  · refine ⟨1, fun a => ?_, fun a ha => ?_, fun a ha => ?_⟩
    · by_cases h : a = 0
      · simp [h]
      · rw [Valuation.one_apply_of_ne_zero h]
    · have : a = 0 := by
        rw [isField_iff_maximalIdeal_eq.1 hf] at ha
        exact ha
      simp [this]
    · by_contra h
      rw [Valuation.one_apply_of_ne_zero h] at ha
      exact one_ne_zero ha
  · obtain ⟨V, hV, hd⟩ := exists_discreteValuationSubring_dominating R (FractionRing R) (FractionRing R) hf
    obtain ⟨h1, h2⟩ := (localSubring_range_le_valuationSubring_iff_isLocalHom _ _).1 hd
    let ρ : R →+* V := (algebraMap R (FractionRing R)).codRestrict V h1
    have hρ : Function.Injective ρ := fun a b hab =>
      IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val hab)
    let v : IsDedekindDomain.HeightOneSpectrum V :=
      ⟨maximalIdeal V, inferInstance, IsDiscreteValuationRing.not_a_field V⟩
    refine ⟨v.intValuation.comap ρ, fun a => v.intValuation_le_one _, fun a ha => ?_, fun a ha => ?_⟩
    · refine (v.intValuation_lt_one_iff_mem _).2 ?_
      exact (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit ρ a hu)
    · by_contra h
      exact v.intValuation_ne_zero _ (fun e => h (hρ (e.trans (map_zero ρ).symm))) ha

variable {k : Type} [Field k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {U : Y.Opens} {D : ℕ}

theorem isIntegral_X [IsIntegral Y] (M : Modif p U D) [Nonempty M.X] : IsIntegral M.X := by
  haveI : Smooth M.str := SmoothOfRelativeDimension.smooth D M.str
  haveI : IsReduced M.X := isReduced_of_smooth M.str
  obtain ⟨x, hx⟩ := M.dense.nonempty
  haveI : Nonempty (M.σ ⁻¹ᵁ U) := ⟨⟨x, hx⟩⟩
  haveI : Nonempty U := ⟨⟨M.σ x, hx⟩⟩
  haveI := M.iso
  haveI : IsIntegral (M.σ ⁻¹ᵁ U : Scheme) := isIntegral_of_isOpenImmersion (M.σ ∣_ U)
  have h1 : IsIrreducible ((M.σ ⁻¹ᵁ U : M.X.Opens) : Set M.X) := by
    have := (IrreducibleSpace.isIrreducible_univ (M.σ ⁻¹ᵁ U : Scheme)).image (⇑(M.σ ⁻¹ᵁ U).ι)
      (M.σ ⁻¹ᵁ U).ι.continuous.continuousOn
    rwa [Set.image_univ, Scheme.Opens.range_ι] at this
  have h2 := h1.closure
  rw [M.dense.closure_eq] at h2
  haveI : IrreducibleSpace M.X := (irreducibleSpace_def _).2 h2
  exact isIntegral_of_irreducibleSpace_of_isReduced M.X

end GlobalTheory.HSApp.ValCrit

namespace GlobalTheory.HSApp

end GlobalTheory.HSApp
