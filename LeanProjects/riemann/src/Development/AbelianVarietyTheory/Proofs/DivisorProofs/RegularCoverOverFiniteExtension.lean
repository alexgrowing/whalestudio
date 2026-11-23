import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularCoverOfAlteration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverFunctionFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointMorphismFactorization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

namespace GlobalTheory.RegCoverExt

theorem SpecMap_fnMap_fromSpecStalk {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (j : Y ⟶ X)
    (h : j (genericPoint Y) ⤳ genericPoint X) :
    Spec.map (CommRingCat.ofHom (TrueGeo.SmallSec.fnMap j h)) ≫ X.fromSpecStalk (genericPoint X) =
      Y.fromSpecStalk (genericPoint Y) ≫ j := by
  change Spec.map (X.presheaf.stalkSpecializes h ≫ j.stalkMap _) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

theorem exists_isArithVar_extension (X : Scheme.{0}) (s : X ⟶ Sp ℤ) [IsIntegral X] (D : ℕ) (h : IsArithVar s D)
    (F : Type) [Field F] [Algebra X.functionField F] [FiniteDimensional X.functionField F] :
    ∃ (Z : Scheme.{0}) (_ : IsIntegral Z) (ν : Z ⟶ X) (hη : ν (genericPoint Z) ⤳ genericPoint X)
      (ψ : F →+* Z.functionField), IsArithVar (ν ≫ s) D ∧ ν (genericPoint Z) = genericPoint X ∧
      ν.residueDegree (genericPoint Z) ≠ 0 ∧
      ψ.comp (algebraMap X.functionField F) = TrueGeo.SmallSec.fnMap ν hη := by
  have := h.isLocallyNoetherian
  have : IsProper s := CommonModel.isProper_of_isProjOver h.isProjOver
  have := h.charZero
  have : CharZero X.functionField :=
    charZero_of_injective_ringHom (f := (X.presheaf.germ ⊤ (genericPoint X) trivial).hom)
      (germ_injective_of_isIntegral X (U := ⊤) (genericPoint X) trivial)
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap X.functionField F).injective
  let η := genericPoint X
  let α : X.presheaf.stalk η ⟶ CommRingCat.of F := CommRingCat.ofHom (algebraMap X.functionField F)
  let g : Spec (.of F) ⟶ X := Spec.map α ≫ X.fromSpecStalk η
  have hfin : IsFinite g.fromNormalization := by
    refine GlobalTheory.isFinite_fromNormalization_SpecMap_fromSpecStalk s η α ?_
    have h2 : (algebraMap X.functionField F).FiniteType := (RingHom.finite_algebraMap.2 inferInstance).finiteType
    exact h2.essFiniteType
  let pt : Spec (.of F) := IsLocalRing.closedPoint (CommRingCat.of F)
  have hgη : g pt = η := by
    change X.fromSpecStalk η (Spec.map α pt) = η
    rw [show Spec.map α pt = IsLocalRing.closedPoint (X.presheaf.stalk η) from
      Subsingleton.elim (α := PrimeSpectrum (X.presheaf.stalk η)) _ _]
    exact Scheme.fromSpecStalk_closedPoint
  have hg0 : η ∈ Set.range g := ⟨pt, hgη⟩
  have : IsDominant g := ⟨(dense_iff_closure_eq.2 (genericPoint_spec X)).mono
    (Set.singleton_subset_iff.2 hg0)⟩
  have : IsDominant g.fromNormalization := by
    have : IsDominant (g.toNormalization ≫ g.fromNormalization) := by
      rw [Scheme.Hom.toNormalization_fromNormalization]; infer_instance
    exact IsDominant.of_comp g.toNormalization g.fromNormalization
  have hρs : Surjective g.fromNormalization :=
    surjective_of_isDominant_of_isClosed_range _ g.fromNormalization.isClosedMap.isClosed_range
  have hdeg : 0 < g.fromNormalization.residueDegree (genericPoint g.normalization) := by
    let := (g.fromNormalization.residueFieldMap (genericPoint g.normalization)).hom.toAlgebra
    have : Module.Finite (X.residueField (g.fromNormalization (genericPoint g.normalization)))
        (g.normalization.residueField (genericPoint g.normalization)) :=
      residueFieldMap_finite_of_locallyQuasiFinite g.fromNormalization _
    exact Module.finrank_pos
  have hgen := apply_genericPoint_of_isDominant g.fromNormalization
  have hdim : topologicalKrullDim g.normalization = (D + 1 : ℕ) := by
    rw [← h.dim_eq]
    exact le_antisymm (ProperCover.dim_le_of_residueDegree_pos g.fromNormalization hgen hdeg)
      (PosBaseChange.dim_le_of_isClosedMap g.fromNormalization.isClosedMap hρs.surj)
  have hfl : Flat (g.fromNormalization ≫ s) :=
    GlobalTheory.flat_fromNormalization_comp g ℚ s (spMap (algebraMap ℚ F)) (specZIsTerminal.hom_ext _ _)
  obtain ⟨hη, ψ, hψ⟩ := NormFnField.normalization_functionField X F g rfl
  refine ⟨g.normalization, inferInstance, g.fromNormalization, hη, ψ,
    ⟨h.isDomain, h.finite, inferInstance, GlobalTheory.isProjOver_comp_of_finite _ _ _ _ _ hfin h.isProjOver, ?_, hdim⟩,
    hgen, hdeg.ne', hψ⟩
  convert hfl using 1
  exact specZIsTerminal.hom_ext _ _

theorem exists_regCover_extension : GlobalTheory.Published.RegularAlteration → ∀ (k : Type) [CommRing k] (X : Scheme.{0})
    (p : X ⟶ Sp k) [IsIntegral X], IsArithVar p 1 → ∀ (F : Type) [Field F] [Algebra X.functionField F],
    FiniteDimensional X.functionField F → ∃ (C : RegCover p) (t : Sp C.Y.functionField ⟶ Sp F),
      t ≫ Spec.map (CommRingCat.ofHom (algebraMap X.functionField F)) ≫ X.fromSpecStalk (genericPoint X) =
        C.Y.fromSpecStalk (genericPoint C.Y) ≫ C.ρ := by
  intro H k _ X p _ h F _ _ _
  obtain ⟨Z, _, ν, hη, ψ, hZ, hν, hνd, hψ⟩ :=
    exists_isArithVar_extension X _ 1 (ShFam.Pad.isArithVar_toSpZ h) F
  obtain ⟨Y, _, ρ, hY, hr, hg, hd⟩ := H Z _ 1 hZ
  have hρ : ρ (genericPoint Y) ⤳ genericPoint Z := hg ▸ specializes_rfl
  have key : Spec.map (CommRingCat.ofHom ((TrueGeo.SmallSec.fnMap ρ hρ).comp ψ)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap X.functionField F)) ≫ X.fromSpecStalk (genericPoint X) =
        Y.fromSpecStalk (genericPoint Y) ≫ ρ ≫ ν := by
    rw [← Category.assoc (Y.fromSpecStalk _), ← SpecMap_fnMap_fromSpecStalk ρ hρ, Category.assoc,
      ← SpecMap_fnMap_fromSpecStalk ν hη, ← hψ, ← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
    rfl
  refine ⟨⟨Y, ρ ≫ ν, ⟨RegCoverExists.isArithVar_of_toSpZ h.isDomain h.finite ((ρ ≫ ν) ≫ p) hY, hr⟩, ?_, ?_⟩,
    Spec.map (CommRingCat.ofHom ((TrueGeo.SmallSec.fnMap ρ hρ).comp ψ)), ?_⟩
  · rw [Scheme.Hom.comp_apply, hg, hν]
  · rw [CurveDegreesCompare.residueDegree_comp, hg]
    exact mul_ne_zero hνd hd
  · exact key

end GlobalTheory.RegCoverExt

end
