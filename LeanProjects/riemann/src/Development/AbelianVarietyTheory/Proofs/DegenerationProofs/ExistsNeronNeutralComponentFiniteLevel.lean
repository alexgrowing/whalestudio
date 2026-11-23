import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNeutralGroupModelStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmConnModelDescends
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAmpleCubSpFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAmpleCubicalOfGroupSchemeIsoStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusExtensionOverCompleteLocalDvr
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianProjectiveBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothOfRelativeDimensionOfGeneric

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.NeutralLevel

theorem isGrpPullback_of_iso_inv {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] {G' : Over S'} [GrpObj G']
    (e : (Over.pullback f).obj G ≅ G') (he : IsMonHom e.hom) :
    IsGrpPullback G' G f (e.inv.left ≫ pullback.fst G.hom f) :=
  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  ((isGrpPullback_of_iso e.symm).comp (isGrpPullback_pullback G f)).congr (Category.id_comp _) rfl

theorem exists_extension {S S' T : Scheme.{0}} {f : S' ⟶ S} {j : T ⟶ S'} {G : Over S} {G' : Over S'} {A : Over T}
    [GrpObj G] [GrpObj G'] [GrpObj A] {φ : G'.left ⟶ G.left} {ψ : A.left ⟶ G'.left}
    (h : IsGrpPullback G' G f φ) (hA : IsGrpPullback A G' j ψ) (c : ℕ)
    (hc : ∀ a : 𝟙_ (Over T) ⟶ A, ∃ s : 𝟙_ (Over S') ⟶ G', j ≫ s.left = (a ^ c).left ≫ ψ)
    (t : T ⟶ S) (ht : t = j ≫ f) (y : Over.mk t ⟶ G) :
    ∃ s : S' ⟶ G.left, s ≫ G.hom = f ∧ j ≫ s = (y ^ c).left := by
  have H := hA.comp h
  obtain rfl : t = (𝟙_ (Over T)).hom ≫ j ≫ f := ht.trans (Category.id_comp _).symm
  let a : 𝟙_ (Over T) ⟶ A := Over.homMk (H.1.lift y.left (𝟙_ (Over T)).hom (Over.w y)) (H.1.lift_snd _ _ _)
  have ha : pushHom H _ a = y := Over.OverMorphism.ext (H.1.lift_fst _ _ _)
  obtain ⟨s, hs⟩ := hc a
  refine ⟨s.left ≫ φ, ?_, ?_⟩
  · rw [Category.assoc, h.1.w, ← Category.assoc, Over.w s]
    exact Category.id_comp _
  · rw [← ha, ← map_pow, ← Category.assoc]
    exact (congrArg (· ≫ φ) hs).trans (Category.assoc _ _ _)

theorem exists_ampleCub_fibre {S S' T : Scheme.{0}} {f : S' ⟶ S} (j : T ⟶ S') {G : Over S} {G' : Over S'}
    [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ)
    (L : LB ((Over.pullback j).obj G').left) (hL : AmpleCub ((Over.pullback j).obj G') L)
    (t : T ⟶ S) (ht : j ≫ f = t) :
    ∃ N : LB ((Over.pullback t).obj G).left, AmpleCub ((Over.pullback t).obj G) N := by
  obtain ⟨e, he, -⟩ := grpPullback_iso (isGrpPullback_pullback G t)
    (((isGrpPullback_pullback G' j).comp h).congr ht rfl)
  exact GlobalTheory.T.exists_ampleCubical_of_groupScheme_iso _ _ _ e he L hL

theorem smoothOfRelativeDimension_model {K W : Type} [Field K] [CommRing W] [IsDomain W]
    [Algebra K (FractionRing W)] (P : Out.PolAV (Sp K)) (G : Over (Sp W)) [GrpObj G] (hG : SmConn G)
    (hm : IsModel (L := FractionRing W) P.A G) : SmoothOfRelativeDimension P.g G.hom := by
  obtain ⟨e, -⟩ := hm
  obtain ⟨-, _, -, -, _⟩ := hG
  refine GlobalTheory.GenericDim.smoothOfRelativeDimension_of_generic W G P.g ?_
  have w : e.hom.left ≫ _ = pullback.snd G.hom (Out.jK W) := Over.w e.hom
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
    (IsPullback.of_horiz_isIso (g := 𝟙 _) ⟨w.trans (Category.comp_id _).symm⟩)
    (GlobalTheory.TorusModel.polPull (spMap (algebraMap K (FractionRing W))) P).smoothDim

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem exists_level_model : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (R K' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra V R] [Field K'] [Algebra R K'] [Algebra K K'], SH R K' → (algebraMap R K').comp (algebraMap V R) = (algebraMap K K').comp (algebraMap V K) → ∀ P : Out.PolAV (Sp K), ∃ (s : Finset R) (c : ℕ), 1 ≤ c ∧ ∀ (W : Subalgebra V R) (_ : IsDiscreteValuationRing W), (↑s : Set R) ⊆ W → IsLocalHom W.val.toRingHom → ∃ (G : Over (Sp W)) (_ : GrpObj G) (L : Type) (_ : Field L) (_ : Algebra W L) (_ : IsFractionRing W L) (_ : Algebra K L), SmConn G ∧ (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K) ∧ IsModel (L := L) P.A G ∧ SmoothOfRelativeDimension P.g G.hom ∧ (∃ N : LB ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G).left, AmpleCub ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G) N) ∧ ∀ y : Over.mk (spMap ((algebraMap R K').comp (algebraMap W R))) ⟶ G, ∃ s : Sp R ⟶ G.left, s ≫ G.hom = spMap (algebraMap W R) ∧ spMap (algebraMap R K') ≫ s = (y ^ c).left := by
  intro V K _ _ _ _ _ _ R K' _ _ _ _ _ _ _ hR hc P
  have : IsFractionRing R K' := hR.2.2.2
  let P' := GlobalTheory.TorusModel.polPull (spMap (algebraMap K K')) P
  obtain ⟨G', _, hG', he, c, hc1, hext⟩ := GlobalTheory.T.exists_neutral_group_model' R K' hR P'.A P'.isAb
    (GlobalTheory.AbProj.isProjBy_of_isPullback P' (IsPullback.id_horiz _))
  obtain ⟨L', hL'⟩ := GlobalTheory.SS.exists_ampleCub_spFibre R K' hR P' G'.Y hG' G'.e he
  obtain ⟨s, hs⟩ := GlobalTheory.smConn_model_descends V K R K' hc P.A P.isAb G'.Y hG' ⟨G'.e, he⟩
  refine ⟨s, c, hc1, fun W hW hsW hl => ?_⟩
  obtain ⟨G, _, _, ε, hG, hε, hcomm, hm⟩ := hs W hW hsW hl
  have h := isGrpPullback_of_iso_inv _ G ε hε
  have hA := isGrpPullback_of_iso_inv _ G'.Y G'.e he
  exact ⟨G, inferInstance, FractionRing W, inferInstance, inferInstance, inferInstance, inferInstance, hG, hcomm, hm,
    smoothOfRelativeDimension_model P G hG hm,
    exists_ampleCub_fibre _ h L' hL' _ (spMap_comp_spMap _ _),
    fun y => exists_extension h hA c hext _ (spMap_comp_spMap _ _).symm y⟩

end GlobalTheory.NeutralLevel
