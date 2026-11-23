import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueLiftOfDensePart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem isFinite_graphClosure_fst_of_isFinite {S X X' Y : Scheme.{0}} (π : X ⟶ X') (s' : X' ⟶ S)
    (p : Y ⟶ S) (f : X ⟶ Y) (h : π ≫ s' = f ≫ p) [IsFinite π] [IsSeparated p]
    [LocallyOfFiniteType p] : IsFinite (graphClosure.fst s' p π f h) := by
  have e := graphClosure.incl_fst s' p π f h
  have : IsFinite (graphClosure.incl s' p π f h ≫ graphClosure.fst s' p π f h) := by
    rw [e]; infer_instance
  have : IsFinite (graphClosure.incl s' p π f h) :=
    IsFinite.of_comp _ (graphClosure.fst s' p π f h)
  have : Surjective (graphClosure.incl s' p π f h) :=
    surjective_of_isDominant_of_isClosed_range _
      (graphClosure.incl s' p π f h).isClosedMap.isClosed_range
  have : UniversallyClosed (graphClosure.fst s' p π f h) :=
    .of_comp_surjective (graphClosure.incl s' p π f h) _
  have : IsProper (graphClosure.fst s' p π f h) := {}
  have : LocallyQuasiFinite (graphClosure.fst s' p π f h) := by
    refine .of_finite_preimage_singleton _ fun s ↦ ?_
    refine (((graphClosure.incl s' p π f h ≫ graphClosure.fst s' p π f h).finite_preimage_singleton
      s).image (graphClosure.incl s' p π f h)).subset fun x hx ↦ ?_
    obtain ⟨y, rfl⟩ := (graphClosure.incl s' p π f h).surjective x
    exact ⟨y, by simpa only [Set.mem_preimage, Scheme.Hom.comp_apply] using hx, rfl⟩
  exact .of_isProper_of_locallyQuasiFinite _

theorem exists_desc_of_isFinite_of_densePart : ∀ (S X X' U U' Y : Scheme.{0}) [IsLocallyNoetherian X'] (π : X ⟶ X') (j : U ⟶ X) (j' : U' ⟶ X') (r : U ⟶ U') (s' : X' ⟶ S) (p : Y ⟶ S) (f : X ⟶ Y) (f₀ : U' ⟶ Y), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' → IsReduced X → IsFinite π → Surjective π → Surjective r → IsDominant j → QuasiCompact j → IsPreimmersion j' → Flat j' → IsDominant j' → QuasiCompact j' → IsSeparated p → LocallyOfFiniteType p → j ≫ π = r ≫ j' → j ≫ f = r ≫ f₀ → f ≫ p = π ≫ s' → f₀ ≫ p = j' ≫ s' → ∃ f' : X' ⟶ Y, j' ≫ f' = f₀ ∧ π ≫ f' = f := by
  intro S X X' U U' Y _ π j j' r s' p f f₀ hX' _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄
  have := GlobalTheory.IsNormalScheme.of_pred hX'
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks j'
  have : GlobalTheory.IsNormalScheme U' := GlobalTheory.IsNormalScheme.of_isIso_stalkMap j'
  have := IsSchemeTheoreticallyDominant.of_isDominant r
  have := isFinite_graphClosure_fst_of_isFinite π s' p f h₃.symm
  let g := graphClosure.lift s' p π f h₃.symm j' f₀ h₄.symm r j h₁.symm h₂.symm
  have hg₁ : g ≫ graphClosure.fst s' p π f h₃.symm = j' := graphClosure.lift_fst ..
  have hg₂ : g ≫ graphClosure.snd s' p π f h₃.symm = f₀ := graphClosure.lift_snd ..
  obtain ⟨σ, ⟨hσ₁, hσ₂⟩, -⟩ := existsUnique_lift_of_densePart X' U' X' _ j' hX' ‹_› ‹_› ‹_› ‹_›
    (graphClosure.fst s' p π f h₃.symm) (𝟙 X') g inferInstance (by rw [hg₁, Category.comp_id])
  have h₅ : j' ≫ σ ≫ graphClosure.snd s' p π f h₃.symm = f₀ := by rw [reassoc_of% hσ₁, hg₂]
  refine ⟨σ ≫ graphClosure.snd s' p π f h₃.symm, h₅,
    ext_of_isDominant_of_isSeparated p ?_ j ?_⟩
  · rw [Category.assoc, Category.assoc, ← graphClosure.condition, reassoc_of% hσ₂, h₃]
  · rw [reassoc_of% h₁, h₅, h₂]

end GlobalTheory
