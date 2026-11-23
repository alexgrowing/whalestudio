import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCls

theorem isDominant_of_comp_eq_genPt {G W : Scheme.{0}} [IsIntegral G] (q : W ⟶ G) [IsOpenImmersion q]
    (r : Sp G.functionField ⟶ W) (hr : r ≫ q = GlobalTheory.FlagCov.genPt G) : IsDominant r := by
  refine ⟨q.isOpenEmbedding.isInducing.dense_iff.2 fun w => ?_⟩
  have e : q '' Set.range r = Set.range (GlobalTheory.FlagCov.genPt G) := by
    rw [← hr, ← Set.range_comp]
    rfl
  rw [e]
  have hm : genericPoint G ∈ Set.range (GlobalTheory.FlagCov.genPt G) :=
    ⟨IsLocalRing.closedPoint _, Scheme.fromSpecStalk_closedPoint⟩
  have hd : q w ∈ closure ({genericPoint G} : Set G) := by
    rw [(genericPoint_spec G).def]; trivial
  exact closure_mono (Set.singleton_subset_iff.2 hm) hd

theorem exists_hom_of_forall_stalk (G Y S : Scheme.{0}) [IsIntegral G] (s : G ⟶ S) (t : Y ⟶ S) [IsSeparated t]
    [LocallyOfFiniteType t] (p : Sp G.functionField ⟶ Y) (_hp : p ≫ t = GlobalTheory.FlagCov.genPt G ≫ s)
    (h : ∀ z : G, ∃ q : Sp (G.presheaf.stalk z) ⟶ Y,
      spMap (algebraMap (G.presheaf.stalk z) G.functionField) ≫ q = p ∧ q ≫ t = G.fromSpecStalk z ≫ s) :
    ∃ f : G ⟶ Y, GlobalTheory.FlagCov.genPt G ≫ f = p ∧ f ≫ t = s := by
  have h' : ∀ z : G, ∃ (U : G.Opens) (_ : z ∈ U) (g : U.toScheme ⟶ Y) (r : Sp G.functionField ⟶ U.toScheme),
      r ≫ U.ι = GlobalTheory.FlagCov.genPt G ∧ r ≫ g = p ∧ g ≫ t = U.ι ≫ s := fun z => by
    obtain ⟨q, h1, h2⟩ := h z
    obtain ⟨U, hU, g, h3, h4⟩ := spread_out_of_isGermInjective' s t (x := z) q h2
    refine ⟨U, hU, g, spMap (algebraMap (G.presheaf.stalk z) G.functionField) ≫ U.fromSpecStalkOfMem z hU, ?_, ?_, h4⟩
    · rw [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
      exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes z)
    · rw [Category.assoc, ← h1, h3]
  choose U hU g r hr hg hs using h'
  let 𝒰 : G.OpenCover := Scheme.Cover.mkOfCovers G (fun z => (U z).toScheme) (fun z => (U z).ι)
    fun z => ⟨z, ⟨z, hU z⟩, rfl⟩
  have hc : ∀ z w, Limits.pullback.fst (U z).ι (U w).ι ≫ g z = Limits.pullback.snd (U z).ι (U w).ι ≫ g w := fun z w => by
    have : IsReduced (Limits.pullback (U z).ι (U w).ι) :=
      isReduced_of_isOpenImmersion (Limits.pullback.fst (U z).ι (U w).ι ≫ (U z).ι)
    have := isDominant_of_comp_eq_genPt (Limits.pullback.fst (U z).ι (U w).ι ≫ (U z).ι)
      (Limits.pullback.lift (r z) (r w) ((hr z).trans (hr w).symm)) (by rw [Limits.pullback.lift_fst_assoc, hr])
    refine ext_of_isDominant_of_isSeparated t ?_ (Limits.pullback.lift (r z) (r w) ((hr z).trans (hr w).symm)) ?_
    · rw [Category.assoc, Category.assoc, hs, hs, Limits.pullback.condition_assoc]
    · rw [Limits.pullback.lift_fst_assoc, Limits.pullback.lift_snd_assoc, hg, hg]
  have e : ∀ z, (U z).ι ≫ 𝒰.glueMorphisms g hc = g z := fun z => 𝒰.ι_glueMorphisms g hc z
  refine ⟨𝒰.glueMorphisms g hc, ?_, 𝒰.hom_ext _ _ fun z => ?_⟩
  · rw [← hr (genericPoint G), Category.assoc, e, hg]
  · exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ t) (e z))).trans (hs z)

end GlobalTheory.FlagCls
