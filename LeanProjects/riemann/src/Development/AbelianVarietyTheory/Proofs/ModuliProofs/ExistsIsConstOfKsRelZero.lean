import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomFromConstThickeningOfDerivationStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ConstThickeningComplexFunctionsStructureStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlobalDerivationOfKodairaSpencerZeroStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoThickeningMapOfModEpsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsGrpPullbackRetraction
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

theorem isDer_snd_of_ringHom {R : Type} [CommRing R] (xD : R →+* DualNumber ℂ) :
    IsDer ((TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp xD) (fun r => (xD r).snd) := by
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · simp only [map_add, TrivSqZeroExt.snd_add]
  · simp only [map_mul, TrivSqZeroExt.snd_mul, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, TrivSqZeroExt.fstHom_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op]
    ring

theorem spMap_fst_comp_algebraMap :
    spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap (algebraMap ℂ (DualNumber ℂ)) = 𝟙 (Sp ℂ) := by
  unfold spMap Sp
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

theorem exists_isConst_of_ksRel_zero :
    Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (xD : R →+* DualNumber ℂ) (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (φ : A'.left ⟶ A.left) (j : P₀.A.left ⟶ A'.left) (s : (Fin P₀.g → ℂ) → ∀ W : A.left.Opens, Γ(A.left, W) → ℂ), IsAbelianScheme A → IsAbelianScheme A' → IsGrpPullback A' A (spMap xD) φ → IsGrpPullback P₀.A A' (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) j → KSRel u A.hom (j ≫ φ) (fun r => (xD r).snd) 0 s → ∃ ρ, IsConst A' P₀.A ρ j := by
  intro hL P₀ u Hm χ hU R _ xD A _ A' _ φ j s hA hA' hφ hj hKS

  have hcomp : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap xD =
      spMap ((TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp xD) := by
    unfold spMap
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hsq : IsPullback (j ≫ φ) P₀.A.hom A.hom
      (spMap ((TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp xD)) := by
    rw [← hcomp]
    exact hj.1.paste_horiz hφ.1

  obtain ⟨d, hd⟩ := GlobalTheory.T.exists_global_derivation_of_kodairaSpencer_zero hL P₀ u Hm χ hU R _ A.left A.hom (j ≫ φ) hA.smooth hsq
    (fun r => (xD r).snd) s (isDer_snd_of_ringHom xD) hKS

  obtain ⟨Y', ρ, π, hpb⟩ : ∃ (Y' : Scheme.{0}) (ρ : Y' ⟶ P₀.A.left) (π : Y' ⟶ Sp (DualNumber ℂ)),
      IsPullback ρ π P₀.A.hom (spMap (algebraMap ℂ (DualNumber ℂ))) :=
    ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  have hw : 𝟙 P₀.A.left ≫ P₀.A.hom =
      (P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ spMap (algebraMap ℂ (DualNumber ℂ)) := by
    rw [Category.assoc, spMap_fst_comp_algebraMap, Category.comp_id, Category.id_comp]
  obtain ⟨i, hiρ, hiπ⟩ := hpb.exists_lift (𝟙 _) (P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) hw

  have hm : (j ≫ φ) ≫ A.hom =
      P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap xD := by
    rw [Category.assoc, hφ.1.w, ← Category.assoc, hj.1.w, Category.assoc]
  obtain ⟨Φ, hiΦ, hΦ⟩ :=
    GlobalTheory.T.exists_hom_from_const_thickening_of_derivation P₀.A.left Y' P₀.A.hom π ρ i hpb hiρ hiπ R xD A.left A.hom (j ≫ φ) d hm hd

  obtain ⟨e, heφ, heπ⟩ := hφ.1.exists_lift Φ π hΦ
  have hie : i ≫ e = j := by
    refine hφ.1.hom_ext ?_ ?_
    · rw [Category.assoc, heφ, hiΦ]
    · rw [Category.assoc, heπ, hiπ, hj.1.w]

  have hpb' := (GlobalTheory.T.const_thickening_complex_functions_structure P₀.A.left Y' P₀.A.hom π ρ i hpb hiρ hiπ).2.1
  have := P₀.isAb.smooth
  have hfl : Flat π := MorphismProperty.of_isPullback (P := @Flat) hpb inferInstance
  have he : IsIso e := GlobalTheory.T.isIso_thickening_map_of_mod_eps P₀.A.left Y' A'.left P₀.A.hom π A'.hom i j e hpb' hj.1 hfl heπ hie

  have hsq2 : IsPullback (inv e) A'.hom π (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, IsIso.inv_comp_eq, heπ]⟩
  have hρ₀ : IsPullback (inv e ≫ ρ) A'.hom P₀.A.hom (spMap (algebraMap ℂ (DualNumber ℂ))) := by
    have h := hsq2.paste_horiz hpb
    rwa [Category.id_comp] at h
  have hjρ : j ≫ inv e ≫ ρ = 𝟙 _ := by
    rw [← hie, Category.assoc, IsIso.hom_inv_id_assoc, hiρ]
  exact exists_isConst_of_isPullback hL P₀.A A' (inv e ≫ ρ) j P₀.isAb hA' hj hρ₀ hjρ

end GlobalTheory.KS
