import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechConerveChainsQuasiIsoOfLocallySurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallySurjectiveEtaleSectionBaseChange
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.SmallEtaleCech

instance : PreservesLimitsOfSize.{0, 0} (disc : PSh ⥤ Spc) :=
  inferInstanceAs (PreservesLimitsOfSize.{0, 0} (Functor.const SimplexCategoryᵒᵖ : PSh ⥤ _))

instance : PreservesLimitsOfSize.{0, 0} sch := inferInstanceAs (PreservesLimitsOfSize.{0, 0} (yoneda ⋙ disc))

noncomputable def bcIso {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) :
    bc p ≅ Over.post sch ⋙ Over.pullback p ⋙ Over.forget E :=
  NatIso.ofComponents (fun U => pullbackSymmetry p (sch.map U.hom)) (fun {U V} g => by
    change pullback.map p (sch.map U.hom) p (sch.map V.hom) (𝟙 _) (sch.map g.left) (𝟙 _) (by simp)
        (by rw [Category.comp_id, ← sch.map_comp, Over.w g]) ≫ (pullbackSymmetry p (sch.map V.hom)).hom =
      (pullbackSymmetry p (sch.map U.hom)).hom ≫ pullback.lift (f := sch.map V.hom) (g := p)
        (pullback.fst (sch.map U.hom) p ≫ sch.map g.left) (pullback.snd (sch.map U.hom) p)
        (by rw [Category.assoc, ← sch.map_comp, Over.w g, pullback.condition])
    apply pullback.hom_ext <;> simp [pullback.map, pullback.lift_fst, pullback.lift_snd])

theorem bc_preserves {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) (J : Type) [SmallCategory J] [IsConnected J]
    [FinCategory J] : PreservesLimitsOfShape J (bc p) := by
  have : PreservesLimitsOfShape J (Over.post sch ⋙ Over.pullback p ⋙ Over.forget E : Over S ⥤ _) := inferInstance
  exact preservesLimitsOfShape_of_natIso (bcIso p).symm

theorem bc_isPullback {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) {U V : Over S} (g : U ⟶ V) :
    IsPullback (pullback.snd p (sch.map U.hom)) ((bc p).map g) (sch.map g.left) (pullback.snd p (sch.map V.hom)) := by
  refine IsPullback.flip (IsPullback.of_right (h₁₂ := pullback.fst p (sch.map V.hom)) (h₂₂ := sch.map V.hom) (v₁₃ := p) ?_ ?_
    (IsPullback.of_hasPullback p (sch.map V.hom)))
  · have h1 : (bc p).map g ≫ pullback.fst p (sch.map V.hom) = pullback.fst p (sch.map U.hom) := by
      simp [bc, pullback.map, pullback.lift_fst]
    have h2 : sch.map g.left ≫ sch.map V.hom = sch.map U.hom := by rw [← sch.map_comp, Over.w g]
    have h3 := IsPullback.of_hasPullback p (sch.map U.hom)
    rw [h2]
    exact h1 ▸ h3
  · simp [bc, pullback.map, pullback.lift_snd]

theorem hyp_coAug : ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (E : Spc) (p : E ⟶ sch.obj S) [HasFiniteWidePushouts (S.Etale)ᵒᵖ] (U V : (S.Etale)ᵒᵖ) (g : U ⟶ V), Surjective g.unop.left → Hyp R ((Scheme.Etale.forget S ⋙ bc p).op) (coAug g) := by
  intro R _ S E p _ U V g hg k
  refine GlobalTheory.T.cechConerve_chains_quasiIso_of_locallySurjective R _ _ (fun n => ?_) U V g ?_
  · have h1 := bc_preserves p (WidePullbackShape (Fin (n + 1)))
    have h2 : PreservesLimitsOfShape (WidePullbackShape (Fin (n + 1)))
        ((Scheme.Etale.forget S ⋙ bc p) ⋙ (evaluation _ PSh).obj k) := inferInstance
    have h3 := preservesLimitsOfShape_of_equiv (widePushoutShapeOpEquiv (Fin (n + 1))).symm
        ((Scheme.Etale.forget S ⋙ bc p) ⋙ (evaluation _ PSh).obj k)
    exact preservesColimitsOfShape_op _ ((Scheme.Etale.forget S ⋙ bc p) ⋙ (evaluation _ PSh).obj k)
  · have he : Etale g.unop.left := by
      have h1 : Etale V.unop.hom := V.unop.prop
      have h2 : Etale U.unop.hom := U.unop.prop
      have h3 : Etale (g.unop.left ≫ U.unop.hom) := by
        rw [MorphismProperty.Over.w g.unop]; exact h1
      exact Etale.of_comp _ U.unop.hom
    exact isLocallySurjective_of_isPullback _ _ _ _
      ((bc_isPullback p ((Scheme.Etale.forget S).map g.unop)).map ((evaluation _ PSh).obj k))
      (yoneda_map_isLocallySurjective_of_etale_surjective _ _ g.unop.left he hg)

end GlobalTheory.EtC.SmallEtaleCech
