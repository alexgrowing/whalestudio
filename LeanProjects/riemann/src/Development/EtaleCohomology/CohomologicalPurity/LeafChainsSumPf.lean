import Development.EtaleCohomology.CohomologicalPurity.LeafSumPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut.SumCut.ChainsSumPf

universe v u
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]

def zeroColim {D : Type*} [Category* D] {J : Type*} [Category* J] (G : D ⥤ C) (hG : ∀ X, IsZero (G.obj X))
    {K : J ⥤ D} (s : Cocone K) : IsColimit (G.mapCocone s) where
  desc _ := 0
  fac _ _ := (hG _).eq_of_src _ _
  uniq _ _ _ := (hG _).eq_of_src _ _

theorem presZero {D : Type*} [Category* D] {J : Type*} [Category* J] (G : D ⥤ C) (hG : ∀ X, IsZero (G.obj X)) :
    PreservesColimitsOfShape J G :=
  ⟨fun {_} => ⟨fun {s} _ => ⟨zeroColim G hG s⟩⟩⟩

theorem presExtend {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')
    (J : Type*) [Category* J] [HasColimitsOfShape J C] : PreservesColimitsOfShape J (e.extendFunctor C) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro i'
  cases h : e.r i' with
  | none => exact presZero _ fun K => K.isZero_extend_X' e i' h
  | some p =>
    have hp : e.f p = i' := e.f_eq_of_r_eq_some h
    let φ : HomologicalComplex.eval C c p ≅ e.extendFunctor C ⋙ HomologicalComplex.eval C c' i' :=
      NatIso.ofComponents (fun K => (K.extendXIso e hp).symm) (fun {K L} f => by
        simp [ComplexShape.Embedding.extendFunctor, HomologicalComplex.extendMap_f _ e hp]
        exact (Iso.inv_hom_id_assoc _ _).symm)
    exact preservesColimitsOfShape_of_natIso φ

theorem presAFM {C : Type*} [Category* C] [Preadditive C] (J : Type*) [Category* J] [HasColimitsOfShape J C] :
    PreservesColimitsOfShape J (AlgebraicTopology.alternatingFaceMapComplex C) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  let φ : (evaluation _ C).obj (op (SimplexCategory.mk n)) ≅
      AlgebraicTopology.alternatingFaceMapComplex C ⋙ HomologicalComplex.eval C _ n :=
    NatIso.ofComponents (fun X => Iso.refl _) (fun {X Y} f => (Category.comp_id _).trans (Category.id_comp _).symm)
  exact preservesColimitsOfShape_of_natIso φ

variable (R : Type) [CommRing R]

theorem presFree (A : Type) : PreservesColimitsOfShape (Discrete A) (free R) := by
  have h1 : PreservesColimitsOfSize.{0, 0} (ModuleCat.free (ULift.{1} R)) :=
    (ModuleCat.adj (ULift.{1} R)).leftAdjoint_preservesColimits
  have h2 : PreservesColimitsOfSize.{0, 0} (presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))) :=
    (sheafificationAdjunction _ _).leftAdjoint_preservesColimits
  unfold free freeP
  infer_instance

instance hasCoprodShv (A : Type) : HasColimitsOfShape (Discrete A) (Shv R) := by
  have : HasColimitsOfSize.{1, 1} (Shv R) := IsGrothendieckAbelian.hasColimits (Shv R)
  have : HasColimitsOfSize.{0, 0} (Shv R) := hasColimitsOfSizeShrink.{0, 0, 1, 1} _
  infer_instance

theorem presChains (A : Type) : PreservesColimitsOfShape (Discrete A) (chains R) := by
  have := presFree R A
  have : PreservesColimitsOfShape (Discrete A) ((SimplicialObject.whiskering PSh (Shv R)).obj (free R)) := by
    unfold SimplicialObject.whiskering; infer_instance
  have := presAFM (C := Shv R) (Discrete A)
  have := presExtend (C := Shv R) ComplexShape.embeddingDownNat (Discrete A)
  unfold chains chainsN
  infer_instance

end LateralTheory.CohomologicalPurity.TubeCut.SumCut.ChainsSumPf

namespace LateralTheory.CohomologicalPurity.TubeCut.SumCut

theorem LeafChainsSum_of : LeafChainsSum := by
  intro R _ A E c ⟨hc⟩
  have := ChainsSumPf.presChains R A
  exact ⟨isColimitCofanMkObjOfIsColimit (chains R) E c.inj hc⟩

end LateralTheory.CohomologicalPurity.TubeCut.SumCut
