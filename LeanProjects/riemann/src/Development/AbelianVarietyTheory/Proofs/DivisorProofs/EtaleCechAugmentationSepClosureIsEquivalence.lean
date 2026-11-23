import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingCocone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSurjectiveCechDescentCohomologyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCohomologyContinuousOnConeOfLevelwiseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLevelRepresentableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsColimitFiniteSubextensionRingCoconeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLimitFiniteSubextensionSpecArrowConeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechNerveLevelPreservesCofilteredLimitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuityCofilteredLimitRepresentedAffineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecMapSmoothSurjectiveOfIsSeparableStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.SepCech

theorem aug_comm {Y Y' X : Scheme.{0}} (f : Y ⟶ X) (g : Y' ⟶ X) (u : yoneda.obj Y ⟶ yoneda.obj Y')
    (w : u ≫ yoneda.map g = yoneda.map f ≫ 𝟙 _) :
    SimplicialObject.cechNerve.map (Arrow.homMk u (𝟙 _) w : Arrow.mk (yoneda.map f) ⟶ Arrow.mk (yoneda.map g)) ≫ cechAug g =
      cechAug f := by
  apply NatTrans.ext; funext n
  simp [cechAug, SimplicialObject.cechNerve, Arrow.mapCechNerve, Arrow.augmentedCechNerve]
  erw [NatTrans.comp_app, WidePullback.lift_base]

theorem cont (R : Type) [CommRing R] (F : Shv R) (hF : Finitary F) (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] : ContCone R F (cechCone K Ω) := by
  obtain ⟨hc⟩ := GlobalTheory.T.isColimit_finiteSubextensionRingCocone K Ω
  obtain ⟨hl⟩ := GlobalTheory.T.isLimit_finiteSubextensionSpecArrowCone K Ω hc
  refine GlobalTheory.T.isCohomologyContinuousOnCone_of_levelwise R F _ _ _ (fun k => ?_)
  obtain ⟨hk⟩ := GlobalTheory.T.cechNerve_level_preserves_cofiltered_limit _ _ _ hl (fun _ _ _ => show IsIso (𝟙 _) from inferInstance)
    (fun _ => show IsIso (𝟙 _) from inferInstance) k
  refine GlobalTheory.T.continuity_cofiltered_limit_represented_affine R F hF _ _ _ hk (fun L => ?_) ?_
  · obtain ⟨Z, π, e, hπ, -⟩ := GlobalTheory.T.exists_representable_cech_level_of_stable @IsAffineHom _ _ (Spec.map (CommRingCat.ofHom (algebraMap K L.unop.1))) inferInstance k
    haveI := hπ
    exact ⟨Z, isAffine_of_isAffineHom π, ⟨e⟩⟩
  · obtain ⟨Z, π, e, -, -⟩ := GlobalTheory.T.exists_representable_cech_level_of_stable @IsAffineHom _ _ (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) inferInstance k
    exact ⟨Z, ⟨e⟩⟩

theorem cechAug_sepClosure_eqv : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω], Eqv R (cechAug (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))) F := by
  intro R _ F hF K Ω _ _ _ _
  haveI : Algebra.IsSeparable K Ω := IsSepClosure.separable
  have hc := cont R F hF K Ω
  have hA : ∀ L : (FinSub K Ω)ᵒᵖ, Eqv R (cechAug (Spec.map (CommRingCat.ofHom (algebraMap K L.unop.1)))) F := by
    intro L
    haveI := L.unop.2
    haveI : Algebra.IsSeparable K L.unop.1 := Algebra.isSeparable_tower_bot_of_isSeparable K L.unop.1 Ω
    obtain ⟨h1, h2⟩ := GlobalTheory.T.smooth_and_surjective_spec_map_of_isSeparable K L.unop.1
    exact GlobalTheory.T.etC_a2 R _ F
  have hw : ∀ L : (FinSub K Ω)ᵒᵖ, (cechCone K Ω).π.app L ≫ cechAug (Spec.map (CommRingCat.ofHom (algebraMap K L.unop.1))) =
      cechAug (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) := fun L => aug_comm _ _ _ _
  have hw2 : ∀ ⦃L L' : (FinSub K Ω)ᵒᵖ⦄ (f : L ⟶ L'), (arr K Ω ⋙ SimplicialObject.cechNerve).map f ≫
      cechAug (Spec.map (CommRingCat.ofHom (algebraMap K L'.unop.1))) =
      cechAug (Spec.map (CommRingCat.ofHom (algebraMap K L.unop.1))) := fun L L' f => aug_comm _ _ _ _
  intro n
  constructor
  · refine (injective_iff_map_eq_zero (pull R _ F n)).mpr (fun z hz => ?_)
    let L0 : (FinSub K Ω)ᵒᵖ := op ⟨⊥, inferInstance⟩
    have h0 : pull R ((cechCone K Ω).π.app L0) F n
        (pull R (cechAug (Spec.map (CommRingCat.ofHom (algebraMap K L0.unop.1)))) F n z) = 0 :=
      (pull_comp R _ _ F n z).symm.trans ((congrArg (fun g => pull R g F n z) (hw L0)).trans hz)
    obtain ⟨L1, f, hf⟩ := (hc n).2 L0 _ h0
    have hf' : pull R (cechAug (Spec.map (CommRingCat.ofHom (algebraMap K L1.unop.1)))) F n z = 0 :=
      (congrArg (fun g => pull R g F n z) (hw2 f)).symm.trans
        ((pull_comp R ((arr K Ω ⋙ SimplicialObject.cechNerve).map f)
          (cechAug (Spec.map (CommRingCat.ofHom (algebraMap K L0.unop.1)))) F n z).trans hf)
    exact ((injective_iff_map_eq_zero (pull R _ F n)).mp (hA L1 n).1) z hf'
  · intro x
    obtain ⟨L, y, hy⟩ := (hc n).1 x
    obtain ⟨z, rfl⟩ := (hA L n).2 y
    refine ⟨z, ?_⟩
    rw [← hy]
    exact (congrArg (fun g => pull R g F n z) (hw L)).symm.trans (pull_comp R _ _ F n z)

end GlobalTheory.SepCech
