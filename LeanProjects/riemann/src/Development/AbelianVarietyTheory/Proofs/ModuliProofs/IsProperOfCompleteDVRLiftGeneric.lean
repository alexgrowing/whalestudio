import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.ValuativeGeneric

theorem exists_lift_of_surjectiveOnStalks {X Z : Scheme.{0}} (j : X ⟶ Z) [SurjectiveOnStalks j]
    (K : Type) [Field K] (t : Spec (.of K) ⟶ Z) (x : X)
    (hx : t (IsLocalRing.closedPoint K) = j x) :
    ∃ u : Spec (.of K) ⟶ X, u ≫ j = t ∧ ∀ p, u p = x := by
  obtain ⟨⟨z, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K Z).symm.surjective t
  obtain rfl : z = j x := (Scheme.fromSpecResidueField_apply z
    (Spec.map φ (IsLocalRing.closedPoint K))).symm.trans hx
  have : IsIso (j.residueFieldMap x) := by
    refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨(j.residueFieldMap x).hom.injective, ?_⟩
    intro a
    obtain ⟨b, rfl⟩ := X.residue_surjective x a
    obtain ⟨c, rfl⟩ := j.stalkMap_surjective x b
    refine ⟨Z.residue _ c, ?_⟩
    rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap]
    rfl
  refine ⟨Spec.map (inv (j.residueFieldMap x) ≫ φ) ≫ X.fromSpecResidueField x, ?_, fun p => by simp⟩
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    ← Spec.map_comp_assoc, IsIso.hom_inv_id_assoc]
  rfl

theorem isClosedImmersion_of_lift {X Z : Scheme.{0}} [IsLocallyNoetherian Z] [Z.IsSeparated]
    (j : X ⟶ Z) [IsPreimmersion j] [QuasiCompact j]
    (h : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
      [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [Algebra V K] [IsFractionRing V K]
      (x : Sp K ⟶ X) (y : Sp V ⟶ Z), Set.range x ⊆ genericPoints X →
      x ≫ j = spMap (algebraMap V K) ≫ y → ∃ x' : Sp V ⟶ X, spMap (algebraMap V K) ≫ x' = x) :
    IsClosedImmersion j := by
  refine .of_isPreimmersion j (IsClosedMap.isClosed_range ?_)
  rw [isClosedMap_iff_specializingMap]
  refine j.isEmbedding.isInducing.specializingMap ?_
  rintro _ z hz ⟨x, rfl⟩
  obtain ⟨x₀, hx₀, hs⟩ := exists_mem_genericPoints_specializes x
  have hs' : j x₀ ⤳ z := (hs.map j.continuous).trans hz
  by_cases hne : j x₀ = z
  · exact ⟨x₀, hne⟩
  obtain ⟨O, _, _, _, g, hg₀, hg₁⟩ := exists_complete_discreteValuationRing_of_specializes hs' hne
  have hinj : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective _ _
  have hpt : (spMap (algebraMap O (FractionRing O)) ≫ g)
      (IsLocalRing.closedPoint (FractionRing O)) = j x₀ := by
    refine Eq.trans (congrArg g (PrimeSpectrum.ext ?_)) hg₀
    change Ideal.comap (algebraMap O (FractionRing O)) (IsLocalRing.maximalIdeal _) = ⊥
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact Ideal.comap_bot_of_injective _ hinj
  obtain ⟨u, hu, hux⟩ := exists_lift_of_surjectiveOnStalks j (FractionRing O) _ x₀ hpt
  obtain ⟨x', hx'⟩ := h O (FractionRing O) u g (by rintro _ ⟨p, rfl⟩; rw [hux]; exact hx₀) hu
  have : IsDominant (spMap (algebraMap O (FractionRing O))) := by
    refine ⟨?_⟩
    refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_
    exact ((RingHom.injective_iff_ker_eq_bot _).mp hinj).le.trans bot_le
  have e : x' ≫ j = g :=
    ext_of_isDominant (spMap (algebraMap O (FractionRing O))) (by rw [← Category.assoc, hx', hu])
  exact ⟨x' (IsLocalRing.closedPoint O), by rw [← hg₁, ← e]; rfl⟩

theorem isProper_of_lift_generic : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X Y : Scheme.{0}) [IsLocallyNoetherian Y] (f : X ⟶ Y) (s : Y ⟶ Sp R), IsSeparated s → IsQProjOver (f ≫ s) → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [Algebra V K] [IsFractionRing V K] (x : Sp K ⟶ X) (y : Sp V ⟶ Y), Set.range x ⊆ genericPoints X → x ≫ f = spMap (algebraMap V K) ≫ y → ∃ x' : Sp V ⟶ X, spMap (algebraMap V K) ≫ x' = x) → IsProper f := by
  intro R _ _ X Y _ f s hs ⟨N, i, hi, hq, e⟩ h
  have := isProper_str R N
  let j : X ⟶ pullback s (PSpace.str R N) := pullback.lift f i e.symm
  have hj₁ : j ≫ pullback.fst _ _ = f := pullback.lift_fst _ _ _
  have hj₂ : j ≫ pullback.snd _ _ = i := pullback.lift_snd _ _ _
  have : IsImmersion (j ≫ pullback.snd _ _) := hj₂ ▸ hi
  have : QuasiCompact (j ≫ pullback.snd _ _) := hj₂ ▸ hq
  have : IsImmersion j := IsImmersion.of_comp j (pullback.snd _ _)
  have : QuasiCompact j := QuasiCompact.of_comp j (pullback.snd _ _)
  have : IsLocallyNoetherian (pullback s (PSpace.str R N)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst _ _)
  have : (pullback s (PSpace.str R N)).IsSeparated := by
    refine ⟨?_⟩
    rw [← terminal.comp_from (pullback.fst s (PSpace.str R N) ≫ s)]
    infer_instance
  have : IsClosedImmersion j := isClosedImmersion_of_lift j fun V K _ _ _ _ _ _ _ x y hx hy =>
    h V K x (y ≫ pullback.fst _ _) hx (by rw [← hj₁, ← Category.assoc, hy, Category.assoc])
  rw [← hj₁]
  infer_instance

end GlobalTheory.ValuativeGeneric
