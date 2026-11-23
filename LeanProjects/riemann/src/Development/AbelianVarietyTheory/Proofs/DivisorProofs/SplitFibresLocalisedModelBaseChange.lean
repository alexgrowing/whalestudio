import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared

noncomputable section

namespace GlobalTheory.KeyUnitModels.SplitLoc

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open scoped CategoryTheory.Obj

theorem isIso_residueFieldMap {Z X : Scheme.{0}} (i : Z ⟶ X) [SurjectiveOnStalks i] (z : Z) :
    IsIso (i.residueFieldMap z) := by
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨RingHom.injective _, fun u => ?_⟩
  obtain ⟨u, rfl⟩ := Z.residue_surjective _ u
  obtain ⟨u, rfl⟩ := i.stalkMap_surjective _ u
  exact ⟨X.residue _ u, ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap i _) u⟩

theorem split_of_pullback {Z X : Scheme.{0}} (i : Z ⟶ X) [SurjectiveOnStalks i] {G : Over X} {G' : Over Z} [GrpObj G]
    [GrpObj G'] {φ : G'.left ⟶ G.left} (hφ : IsGrpPullback G' G i φ) (z : Z)
    (h : ∃ (k : Type) (_ : Field k) (_ : Algebra (X.residueField (i z)) k),
      FiniteDimensional (X.residueField (i z)) k ∧ Algebra.IsSeparable (X.residueField (i z)) k ∧
      ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField (i z)) k)) ≫ X.fromSpecResidueField (i z))).obj G)) :
    ∃ (k : Type) (_ : Field k) (_ : Algebra (Z.residueField z) k),
      FiniteDimensional (Z.residueField z) k ∧ Algebra.IsSeparable (Z.residueField z) k ∧
      ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) k)) ≫ Z.fromSpecResidueField z)).obj G') := by
  obtain ⟨k, _, _, hfin, hsep, S, hS⟩ := h
  have := isIso_residueFieldMap i z
  let e : X.residueField (i z) ≃+* Z.residueField z := (asIso (i.residueFieldMap z)).commRingCatIsoToRingEquiv
  let _ : Algebra (Z.residueField z) k := ((algebraMap (X.residueField (i z)) k).comp e.symm.toRingHom).toAlgebra
  have he : (algebraMap (Z.residueField z) k).comp (e : _ →+* _) =
      ((RingEquiv.refl k : k ≃+* k) : k →+* k).comp (algebraMap (X.residueField (i z)) k) :=
    RingHom.ext fun a => congrArg (algebraMap (X.residueField (i z)) k) (e.symm_apply_apply a)
  refine ⟨k, inferInstance, inferInstance, Module.Finite.of_equiv_equiv e (RingEquiv.refl k) he,
    Algebra.IsSeparable.of_equiv_equiv e (RingEquiv.refl k) he, S, ?_⟩
  have hc : i.residueFieldMap z ≫ CommRingCat.ofHom (algebraMap (Z.residueField z) k) =
      CommRingCat.ofHom (algebraMap (X.residueField (i z)) k) := CommRingCat.hom_ext he
  have key : (Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) k)) ≫ Z.fromSpecResidueField z) ≫ i =
      Spec.map (CommRingCat.ofHom (algebraMap (X.residueField (i z)) k)) ≫ X.fromSpecResidueField (i z) := by
    rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← hc]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ X.fromSpecResidueField (i z)) (Spec.map_comp _ _).symm)
  obtain ⟨j, hj, -⟩ := grpPullback_iso (isGrpPullback_pullback G _)
    (((isGrpPullback_pullback G' _).comp hφ).congr key rfl)
  exact isGt_of_iso j hS

theorem locModel_splitFibres : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β)
    (O' : Type) [CommRing O'] (β' : O' →+* c.F) (b : O →+* O') (hb : β'.comp b = β) [IsPreimmersion (spMap b)]
    [Flat (spMap b)], Y.SplitFibres → (locModel Y b hb).SplitFibres := by
  intro E _ _ _ H D l Xo c O _ β Y O' _ β' b hb _ _ h x
  exact split_of_pullback (pullback.fst Y.s (spMap b)) (locMap Y b).cart x (h _)

end GlobalTheory.KeyUnitModels.SplitLoc
