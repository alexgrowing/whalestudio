import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointMorphismFactorization
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverCompFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KrullDimOneOfFiniteGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldMapFiniteOfQuasiFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase
open CategoryTheory.Limits

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArLieBase

theorem spMap_fnMap_genericPoint {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y] (j : Y ⟶ Z)
    (hη : j (genericPoint Y) ⤳ genericPoint Z) :
    spMap (GlobalTheory.TrueGeo.SmallSec.fnMap j hη) ≫ Z.fromSpecStalk (genericPoint Z) = Y.fromSpecStalk (genericPoint Y) ≫ j := by
  have e : spMap (GlobalTheory.TrueGeo.SmallSec.fnMap j hη) =
      Spec.map (Z.presheaf.stalkSpecializes hη ≫ j.stalkMap (genericPoint Y)) := rfl
  rw [e, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

theorem normalization_isPre : ∀ (F : Type) [Field F] [NumberField F] (G T : Scheme.{0}) (s : G ⟶ Sp F) (S : Set G) (d : ℕ) (ι : G ⟶ T) (X W : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp (𝓞 F)) (jB : W ⟶ X) (πB : W ⟶ G) (ρ : X ⟶ T), IsPre s S d ι q jB πB ρ → ∀ (K : Type) [Field K] [Algebra X.functionField K], Module.Finite X.functionField K → ∃ (X' W' : Scheme.{0}) (_ : IsIntegral X') (ν : X' ⟶ X) (jB' : W' ⟶ X') (πB' : W' ⟶ G) (κ : K →+* X'.functionField), IsPre s S d ι (ν ≫ q) jB' πB' (ν ≫ ρ) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' ∧ X'.fromSpecStalk (genericPoint X') ≫ ν = spMap κ ≫ spMap (algebraMap X.functionField K) ≫ X.fromSpecStalk (genericPoint X) := by
  intro F _ _ G T s S d ι X W _ q jB πB ρ hP K _ _ hK
  obtain ⟨hX, hpb, hfin, hrange, hcomm⟩ := hP
  haveI := hX.isNoetherian
  haveI := hX.isLocallyNoetherian
  haveI : IsProper q := CommonModel.isProper_of_isProjOver hX.isProjOver
  haveI : FiniteDimensional X.functionField K := hK
  haveI : CharZero Γ(X, ⊤) := hX.charZero
  haveI : CharZero X.functionField :=
    charZero_of_injective_ringHom (f := (X.presheaf.germ ⊤ (genericPoint X) (TopologicalSpace.Opens.mem_top _)).hom)
      (germ_injective_of_isIntegral X _ (TopologicalSpace.Opens.mem_top _))
  haveI : CharZero K := charZero_of_injective_ringHom (algebraMap X.functionField K).injective
  let g : Sp K ⟶ X := spMap (algebraMap X.functionField K) ≫ X.fromSpecStalk (genericPoint X)
  haveI hνfin : IsFinite g.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_SpecMap_fromSpecStalk (o := CommRingCat.of (𝓞 F)) q (genericPoint X) (L := K)
      (CommRingCat.ofHom (algebraMap X.functionField K))
      (RingHom.finite_algebraMap.mpr hK).finiteType.essFiniteType
  haveI : GlobalTheory.IsNormalScheme g.normalization := GlobalTheory.IsNormalScheme.normalization_of_isIntegral g
  haveI hint : IsIntegral g.normalization := inferInstance
  obtain ⟨hη, ψ, hψ⟩ := GlobalTheory.NormFnField.normalization_functionField X K g rfl
  set ν := g.fromNormalization with hν
  haveI hνd : IsDominant ν := ⟨dense_iff_closure_eq.2 (Set.eq_univ_of_univ_subset
    ((genericPoint_spec X).def.ge.trans (closure_minimal (Set.singleton_subset_iff.2
      (closure_mono (Set.singleton_subset_iff.2 (Set.mem_range_self _)) (specializes_iff_mem_closure.1 hη))) isClosed_closure)))⟩
  have hs : Surjective ν := surjective_of_isDominant_of_isClosed_range _ ν.isClosedMap.isClosed_range
  have hgen : ν (genericPoint g.normalization) = genericPoint X := apply_genericPoint_of_isDominant ν
  have hdim : topologicalKrullDim g.normalization = (d + 1 : ℕ) := by
    rw [← hX.dim_eq]
    refine le_antisymm (ProperCover.dim_le_of_residueDegree_pos ν hgen ?_)
      (PosBaseChange.dim_le_of_isClosedMap ν.isClosedMap hs.surj)
    let := (ν.residueFieldMap (genericPoint g.normalization)).hom.toAlgebra
    have : Module.Finite (X.residueField (ν (genericPoint g.normalization)))
        (g.normalization.residueField (genericPoint g.normalization)) :=
      residueFieldMap_finite_of_locallyQuasiFinite ν _
    exact Module.finrank_pos
  haveI : CharZero g.normalization.functionField := charZero_of_injective_ringHom ψ.injective
  haveI : CharZero Γ(g.normalization, ⊤) :=
    RingHom.charZero (S := g.normalization.functionField)
      (g.normalization.presheaf.germ ⊤ (genericPoint g.normalization) (TopologicalSpace.Opens.mem_top _)).hom
  have hAr : IsArithVar (ν ≫ q) d :=
    ⟨hX.isDomain, hX.finite, hint, GlobalTheory.isProjOver_comp_of_finite _ _ _ ν q inferInstance hX.isProjOver,
      (flat_int_iff_charZero _).2 inferInstance, hdim⟩
  have hsq : IsPullback (pullback.snd jB ν) (pullback.fst jB ν) ν jB := (IsPullback.of_hasPullback jB ν).flip
  have hpb' : IsPullback (pullback.snd jB ν) ((pullback.fst jB ν ≫ πB) ≫ s) (ν ≫ q)
      (spMap (algebraMap (𝓞 F) F)) := by
    simpa only [Category.assoc] using hsq.paste_vert hpb
  have hprf : IsFinite (pullback.fst jB ν) :=
    MorphismProperty.of_isPullback (P := @IsFinite) hsq inferInstance
  have hprs : Surjective (pullback.fst jB ν) :=
    MorphismProperty.of_isPullback (P := @Surjective) hsq hs
  refine ⟨g.normalization, pullback jB ν, hint, ν, pullback.snd jB ν, pullback.fst jB ν ≫ πB, ψ,
    ⟨hAr, hpb', inferInstance, ?_, ?_⟩, GlobalTheory.IsNormalScheme.pred _, ?_⟩
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hprs.surj.range_eq, Set.image_univ, hrange]
  · rw [← Category.assoc, hsq.w, Category.assoc, hcomm, Category.assoc]
  · rw [← spMap_fnMap_genericPoint ν hη, ← hψ]
    simp only [spMap]
    rw [← Category.assoc, ← Spec.map_comp]
    rfl

end GlobalTheory.ArLieBase
