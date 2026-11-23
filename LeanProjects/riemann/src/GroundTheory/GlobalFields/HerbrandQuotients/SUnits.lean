import Mathlib
import GroundTheory.GlobalFields.SUnits
import GroundTheory.GlobalFields.HerbrandQuotients.Lattice
import GroundTheory.GlobalFields.HerbrandQuotients.SUnitsExact
import GroundTheory.GlobalFields.HerbrandQuotients.SUnitsPerm
import GroundTheory.GlobalFields.HerbrandQuotients.SUnitsRep
import GroundTheory.GlobalFields.HerbrandQuotients.UnitsHerbrandValue

namespace GroundTheory.Global

open NumberField IsDedekindDomain MulAction Module

noncomputable section

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

variable (S : Set (HeightOneSpectrum (𝓞 L))) [Finite S]

omit [IsGalois K L] in

theorem hasHerbrandQuotient_sUnitRep (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S)
    {σ : L ≃ₐ[K] L} (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    GroundTheory.GroupCoh.HasHerbrandQuotient (cycSubOne (sUnitRep S hS) σ) (cycNorm (sUnitRep S hS)) :=
  hasHerbrandQuotient_cycSubOne_of_finite _ hσ

omit [IsGalois K L] in

theorem finite_quotient_range_valuationVector :
    Finite ((S → ℤ) ⧸ (SUnit.valuationVector (K := L) S).toAddMonoidHom.range) := by
  have hn : (-(classNumber L : ℤ)) ≠ 0 := by
    simpa using classNumber_ne_zero L
  refine finite_quotient_of_smul_mem _ hn fun y => ⟨SUnit.placeUnitsMap S y, ?_⟩
  change (SUnit.valuationVector S ∘ₗ SUnit.placeUnitsMap S) y = _
  rw [SUnit.valuationVector_comp_placeUnitsMap]
  rfl

omit [IsGalois K L] [Finite S] in

theorem exact_ofUnits_valuationVector :
    Function.Exact (SUnit.ofUnits (K := L) S).toAdditive
      (SUnit.valuationVector (K := L) S).toAddMonoidHom := by
  intro y
  have h := SetLike.ext_iff.1 (SUnit.ker_valuationVector (K := L) S) y
  rw [LinearMap.mem_ker, LinearMap.mem_range] at h
  exact h

open scoped Classical in

theorem cycHerbrand_sUnitRep (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S)
    {σ : L ≃ₐ[K] L} (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    cycHerbrand (sUnitRep S hS) σ =
      (∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : ∃ w ∈ S, w.asIdeal.LiesOver v.asIdeal),
          ((v.asIdeal.ramificationIdxIn (𝓞 L) * v.asIdeal.inertiaDegIn (𝓞 L) : ℕ) : ℚ)) *
        (∏ v : InfinitePlace K, (if v.IsUnramifiedIn L then 1 else 2 : ℚ)) / finrank K L := by
  let := stableMulAction S hS
  have : Fintype (orbitRel.Quotient (L ≃ₐ[K] L) S) := Fintype.ofFinite _
  have : Finite ((S → ℤ) ⧸ (SUnit.valuationVector (K := L) S).toAddMonoidHom.range) :=
    finite_quotient_range_valuationVector S
  have h1 := cycHerbrand_eq_mul_of_exact (unitsRep K L) (sUnitRep S hS)
    (funPermRep ℤ (L ≃ₐ[K] L) S) σ
    (i := (SUnit.ofUnits (K := L) S).toAdditive)
    (p := (SUnit.valuationVector (K := L) S).toAddMonoidHom)
    (fun a b h => SUnit.ofUnits_injective S (congrArg Additive.toMul h))
    (exact_ofUnits_valuationVector S) (fun g a => ofUnits_unitsRep S hS g a)
    (fun g b => valuationVector_sUnitRep S hS g b)
    (hasHerbrandQuotient_cycSubOne_of_finite _ hσ) (hasHerbrandQuotient_cycSubOne_of_finite _ hσ)
  rw [h1, cycHerbrand_unitsRep hσ, cycHerbrand_funPermRep hσ,
    prod_card_stabilizer_finitePlace S hS]
  ring

end

end GroundTheory.Global
