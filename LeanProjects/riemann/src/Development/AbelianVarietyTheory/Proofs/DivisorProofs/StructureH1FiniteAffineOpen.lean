import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RhoIsCoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentsAbelianSchemeConstantDimension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureCohomologyFlatBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianStructureCohomologyStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianLocusOpenFamilyOverLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocOfBijectiveLiftSemi
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechFinGen

theorem finite_piece (hO : GlobalTheory.AbCoh.OStr) {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A]
    (hA : IsAbelianScheme A) (f : R) (hf : IsIdempotentElem f) (g : ℕ)
    (hg : SmoothOfRelativeDimension g (pullback.snd A.hom (spMap (Ideal.Quotient.mk (Ideal.span {1 - f}))))) :
    Module.Finite (R ⧸ Ideal.span {1 - f}) ((R ⧸ Ideal.span {1 - f}) ⊗[R] HO1 A.hom) := by
  haveI : IsLocalization.Away f (R ⧸ Ideal.span {1 - f}) :=
    IsLocalization.Away.quotient_of_isIdempotentElem hf
  haveI : Module.Flat R (R ⧸ Ideal.span {1 - f}) :=
    IsLocalization.flat (R ⧸ Ideal.span {1 - f}) (Submonoid.powers f)
  let B : Over (Sp (R ⧸ Ideal.span {1 - f})) :=
    (Over.pullback (spMap (algebraMap R (R ⧸ Ideal.span {1 - f})))).obj A
  letI : GrpObj B := Functor.grpObjObj
  have hB : IsAbelianScheme B := isAbelianScheme_pullback_obj _ A hA
  have hBg : SmoothOfRelativeDimension g B.hom := hg
  obtain ⟨hfp, -, -, -⟩ := hO _ B g hB hBg
  haveI := hA.proper
  obtain ⟨⟨e, -⟩, -⟩ := GlobalTheory.AbCoh.flat_baseChange_HO R (R ⧸ Ideal.span {1 - f}) A.left B.left A.hom B.hom
    (pullback.fst _ _) (IsPullback.of_hasPullback _ _) inferInstance inferInstance
  haveI := hfp.1
  exact Module.Finite.equiv e.symm

theorem finite_HO1 (hO : GlobalTheory.AbCoh.OStr) {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A]
    (hA : IsAbelianScheme A) : Module.Finite R (HO1 A.hom) := by
  obtain ⟨n, e, he, hsm⟩ := GlobalTheory.DimSplit.exists_idempotents_smoothOfRelativeDimension R A hA
  have hspan : Ideal.span (Set.range e) = ⊤ := by
    rw [eq_top_iff, ← Ideal.span_singleton_one, Ideal.span_le, Set.singleton_subset_iff, ← he.complete]
    exact Ideal.sum_mem _ (fun k _ ↦ Ideal.subset_span ⟨k, rfl⟩)
  have hidem : ∀ g : Set.range e, IsIdempotentElem g.val := by
    rintro ⟨_, k, rfl⟩; exact he.idem k
  haveI : ∀ g : Set.range e, IsLocalization.Away g.val (R ⧸ Ideal.span {1 - g.val}) := fun g ↦
    IsLocalization.Away.quotient_of_isIdempotentElem (hidem g)
  haveI : ∀ g : Set.range e, IsLocalizedModule.Away g.val
      (TensorProduct.mk R (R ⧸ Ideal.span {1 - g.val}) (HO1 A.hom) 1) := fun g ↦
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers g.val) (R ⧸ Ideal.span {1 - g.val}) _).2
      (TensorProduct.isBaseChange R (HO1 A.hom) (R ⧸ Ideal.span {1 - g.val}))
  refine Module.Finite.of_localizationSpan' (Set.range e) hspan
    (Rₚ := fun g ↦ R ⧸ Ideal.span {1 - g.val})
    (Mₚ := fun g ↦ (R ⧸ Ideal.span {1 - g.val}) ⊗[R] HO1 A.hom)
    (fun g ↦ TensorProduct.mk R (R ⧸ Ideal.span {1 - g.val}) (HO1 A.hom) 1) (fun g ↦ ?_)
  obtain ⟨_, k, rfl⟩ := g
  obtain ⟨d, hd⟩ := hsm k
  exact finite_piece hO A hA (e k) (he.idem k) d hd

end GlobalTheory.CechFinGen

theorem GlobalTheory.CechFinGen.finite_HO1_onAff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → ∀ U : X.affineOpens,
    Module.Finite Γ(X, U.1) (HO1 (GlobalTheory.DeRhamSheaf.onAff t.G U.2).hom) := by
  intro E _ _ _ H X t hp U
  letI : GrpObj (GlobalTheory.DeRhamSheaf.onAff t.G U.2) := Functor.grpObjObj
  have hA : IsAbelianScheme t.G := GlobalTheory.AbelianLocusNormalisation.isAbelianScheme_of_isProper t hp
  exact GlobalTheory.CechFinGen.finite_HO1 GlobalTheory.AbCoh.oStr (GlobalTheory.DeRhamSheaf.onAff t.G U.2) (GlobalTheory.DeRhamSheaf.isAbelianScheme_onAff hA U.2)
