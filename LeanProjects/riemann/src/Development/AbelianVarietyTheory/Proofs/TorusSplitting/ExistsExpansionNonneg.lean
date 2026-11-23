import Mathlib
import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
import Formalism.LocalToGlobal.ProjectiveLattices.LiesOverBaseChange
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETPoint
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralDegenerationFamilyBaseChangeExtensionFie
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralFamilyLevelOne
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecLinOfSecScal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaVal

theorem secLin_one {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ₁ : K' → (Y' ⟶ X)} {ε₁ : K' → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {s : LB.Sec (LB.LinComb L φ ε)} {h : Y' ⟶ Y} {F : Type} [CommRing F] (p : Y' ⟶ Spec (CommRingCat.of F))
    (H : ∀ y J, Good L y J → sval s₁ (𝟙 Y') y J = sval s (𝟙 Y' ≫ h) y J) :
    GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ ε (fun _ : Fin 1 => s) h (fun _ => ReciprocityTheory.ChartRestriction.G.Out.scal p (1 : F)) := by
  refine (GlobalTheory.FieldBaseChange.secLin_iff_val hL _ _ _ _).2 fun y J hJ => ?_
  rw [Fin.sum_univ_one, H y J hJ, ReciprocityTheory.ChartRestriction.G.Out.scal, map_one, map_one, gs_eq _ y ⊤ trivial, map_one, map_one,
    _root_.one_mul]

theorem exists_expansion_nonneg : GlobalTheory.UT.AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ (w₀ : GlobalTheory.UT.W0 U.toUnifPre), w₀.IsGen → ∀ th : GlobalTheory.UT.SecA A F 1, IntTh U.toUnifPre w₀ th → ∃ ϑ : Fam D.toPre F 1, U.ExpandsF F 1 w₀ th ϑ ∧ NuGe D Q F v 1 ϑ 0 := by
  intro V _ _ _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ _ U w₀ _ th ⟨_, σ, hσ⟩
  let s : U.toUnifPre.SecK 1 := GlobalTheory.FieldBaseChange.pullOver (π := G.hom) (π' := pullback.snd G.hom (jK V)) U.LG.L _
    (p := pullback.fst G.hom (jK V)) pullback.condition (fun _ => (Category.comp_id _).symm) σ
  have hs : GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => ((1 : ℕ) : ℤ)) s
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ)) σ (pullback.fst G.hom (jK V)) 1 :=
    SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J hJ => (GlobalTheory.FieldBaseChange.sval_pullOver _ _ _ _ hJ).symm
  obtain ⟨E, hE⟩ := ((U.expand 1 le_rfl).1 s).exists
  obtain ⟨g, hg, hgE⟩ := GlobalTheory.ExpInt.main V ϖ hϖ D A G U.toUnifPre 1 σ s hs E hE
  obtain ⟨ϑ, hϑ⟩ := GlobalTheory.FamBaseChange.main GlobalTheory.ExpansionTotal.globalFns V _ D 1 E g hgE F
  refine ⟨ϑ, ?_, (GlobalTheory.integralFamily_levelOne V ϖ hϖ D Q hQ F v hv ϑ g hϑ).1⟩
  obtain ⟨σ', hσ'⟩ := GlobalTheory.BoxExpansion.exists_secLin U.LG.isLB
    (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left (UnifPre.gFK (G := G) F)
    (fun _ : Fin 1 => UnifPre.gFK (G := G) F) (φ := fun _ : Fin 1 => 𝟙 G.left) (fun _ => (Category.comp_id _).symm)
    (fun _ : Fin 1 => σ) (fun _ => (1 : F))
  refine ⟨σ', ?_, 1, fun _ => 1, fun _ => σ, fun _ => g, fun _ => hg, hσ', fun α => ?_⟩
  · have e₁ : (U.genF F).left ≫ (snd (TFK (R := V) F) A.A).left =
        (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left ≫ U.gen.hom.left :=
      congrArg (fun q => q.left) (lift_snd _ _ : U.genF F ≫ snd _ _ = _)
    refine GlobalTheory.BoxExpansion.isoRel_of_val A.isLB U.LG.isLB e₁ (Category.id_comp _) fun y J₁ J₂ h₁ h₂ => ?_
    have a := GlobalTheory.BoxExpansion.secLin_val hσ' (𝟙 _) y h₂
    rw [Fin.sum_univ_one, ReciprocityTheory.ChartRestriction.G.Out.scal, map_one, map_one, gs_eq _ y ⊤ trivial, map_one, map_one,
      _root_.one_mul] at a
    have b := hσ _ (𝟙 _) y J₁ J₂ h₁ h₂
    simp only [Category.id_comp, Category.comp_id] at a b
    rw [e₁] at b
    rw [pow_one]
    exact a.trans b
  · exact secLin_one D.toPre.P.isLB _ fun y J hJ => (SectionScalarValuation.secScal_sval (hϑ α) _ y hJ).symm

end GlobalTheory.EtaVal
