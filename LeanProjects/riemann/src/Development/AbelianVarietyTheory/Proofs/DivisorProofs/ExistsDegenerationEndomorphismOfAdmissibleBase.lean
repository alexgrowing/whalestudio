import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEndomorphismActionUniformizationData
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformizationEndomorphismCalculus
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.UT

set_option maxHeartbeats 1000000

namespace GlobalTheory.UT

open GlobalTheory.EndData in

theorem exists_degenerationEndomorphism_of_admissibleBase : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif I D A G, ∀ (aG : G ⟶ G) (aA : A.A ⟶ A.A), IsMonHom aG → IsMonHom aA → (Over.pullback (jK R)).map aG ≫ U.gen.hom = U.gen.hom ≫ aA → ∃ E : EndU U.toUnifPre, E.aG = aG ∧ E.aA = aA := by
  intro R _ _ I hR D A G _ _ _ U aG aA hG hA hext
  have hL := GlobalTheory.firstFiveLaws
  have hC := hR.2.2.2
  have hB := D.toPre.P.isLB
  obtain ⟨aB, haB, hq⟩ := exists_abelian hL hR U.toUnifPre aG
  obtain ⟨h, hh⟩ := T.uniformisation_endomorphism_character_map_constant hL R I hR D A G U.toUnifPre aG hG
  choose t ht hi using hh
  choose v hv vv using fun χ e => T.exists_gen_of_torusEnd_compat R I D.toPre e G (U.gt e) ((Over.pullback (thick R I e)).map aG) aB h (t e)
    inferInstance (ht e) (hi e) (hq e) χ
  have down : ∀ χ e (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.toPre.P.L z J →
      val ((U.gt (e + 1)).t χ) (r ≫ thickMap R I e G) z J = val ((U.gt e).t χ) r z J :=
    fun χ e Z r z J hJ => (val_pull hJ _ _ _).symm.trans (val_corr hJ (U.gt_t e χ) r)
  choose u hu uv using fun χ => T.exists_generator_of_compatible_thickening_generators R I hC D.toPre.P.A D.toPre.P.isAb.smooth
    (AbProj.isProjBy_of_isPullback D.toPre.P (IsPullback.id_horiz _)) _ D.toPre.P.L _ _ _ _ hB (fun _ _ => rfl)
    (v χ) (hv χ) (fun e z J hJ => by
      have := (U.gt e).q_flat
      have := (U.gt e).q_surj
      refine val_eq_of_flat hB _ _ _ _ (fun k => ?_) (U.gt e).q.left (fun x J hJ => ?_) z J hJ
      · rw [← Category.assoc, trans_fst, Category.id_comp]
      · have k₁ := vv χ (e + 1) _ (𝟙 _ ≫ thickMap R I e G) x J hJ
        have k₀ := vv χ e _ (𝟙 _) x J hJ
        rw [down _ _ _ _ _ _ hJ, Category.assoc, trans_map, ← Category.assoc, down _ _ _ _ _ _ hJ, k₀,
          Category.id_comp, Category.id_comp, UnifCompare.trans_comp_q] at k₁
        rw [Category.comp_id]
        exact (mul_left_cancel k₁).symm)
  refine ⟨⟨aG, aA, aB, hG, hA, haB, h, hext, hq, fun e => ⟨t e, ht e, hi e⟩, u, fun χ => ⟨hu χ, ?_⟩,
    fun e χ Z x z J hJ => ?_⟩, rfl, rfl⟩
  · refine corr_of_val hB fun y J hJ => Eq.trans ?_ (val_one _).symm
    refine val_eq_one I hB (fun V _ k => ?_) _ (pullGen_isGen _ _ _ _ (hu χ) _) (fun e z J hJ => ?_) y J hJ
    · refine (Fintype.prod_sum_type _).trans ((congrArg₂ (· * ·) (prod_unit D.toPre (𝟙 _) (h χ) k).1
        (prod_unit D.toPre aB χ k).2).trans ((_root_.mul_one _).trans (Fintype.prod_empty _).symm))
    · have := (U.gt e).q_hom
      have k := vv χ e _ (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left z J hJ
      rw [← Over.comp_left, ← Over.comp_left, MonObj.one_comp, MonObj.one_comp, TorusCoord.val_unit _ _ hJ,
        TorusCoord.val_unit _ _ hJ, _root_.one_mul, ← uv χ e _ _ z J hJ] at k
      have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e D.toPre.P.A) =
        η[thickObj R I e D.toPre.P.A] := by simp [Hom.one_def]
      rw [o] at k
      exact (val_pull hJ _ _ _).trans ((congrArg (fun p => val (u χ) p z J)
        (UnitValue.eSec_pullback_fst (thick R I e) D.toPre.P.A).symm).trans k.symm)
  · refine (vv χ e Z x z J hJ).trans (congrArg (_ * ·) ((uv χ e Z _ z J hJ).symm.trans ?_))
    exact congrArg (fun p => val (u χ) p z J) (Category.assoc _ _ _)

open GlobalTheory.EndRosati GlobalTheory.CechPic in

theorem rosatiAdjoint_and_linear_of_admissibleBase : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif I D A G, ∀ E E' : EndU U.toUnifPre, LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L) → RosatiAdj A.A A.L E.aA E'.aA ∧ RosatiAdj D.toPre.P.A D.toPre.P.L E.aB E'.aB ∧ (∀ χ, D.toPre.c (E.h χ) = D.toPre.c χ ≫ E'.aB) ∧ ∀ χ, D.toPre.c (E'.h χ) = D.toPre.c χ ≫ E.aB := by
  intro R _ _ I hR D A G _ _ hG U E E' H
  have hLL := GlobalTheory.firstFiveLaws
  have hGF := hLL.1.globalFns
  obtain ⟨-, -, -, hC⟩ := hR
  have := E.homG
  have := E'.homG
  have := E.homB
  have := E'.homB
  have := hG.geomConnected
  obtain ⟨u, hu, h₀⟩ := (NormRos.normRos_of_lbIso _ G U.LG.L U.LG.isLB E.aG E'.aG H).1
  have hP : AbLaw.IsProjBy D.toPre.P.A.hom := AbProj.isProjBy_of_isPullback D.toPre.P (IsPullback.id_horiz _)
  have hB : RosatiAdj D.toPre.P.A D.toPre.P.L E.aB E'.aB :=
    loc_gen_of_thickenings hGF I _ (AbelianSchemeGerms.isAbelianScheme_tensor _ _ D.toPre.P.isAb D.toPre.P.isAb)
      (AbLaw.isProjBy_tensor R _ _ hP hP) D.toPre.P.isLB _ _ fun e => by
      have := EndTorus.connectedSpace_thickening I e
      have : GeometricallyConnected (thickObj R I e G).hom :=
        inferInstanceAs (GeometricallyConnected (pullback.snd G.hom (thick R I e)))
      have : ConnectedSpace (thickObj R I e G).left :=
        GroupConn.connectedSpace_of_section (thickObj R I e G).hom (η : 𝟙_ _ ⟶ thickObj R I e G).left (Over.w _)
      exact exists_gen_thick U.toUnifPre e (E.q_lin e) (E'.q_lin e)
        (FamGerm.surjective_appTop_sq_cube U.toUnifPre).2 u hu h₀
  obtain ⟨r, hr, -⟩ := exists_ros hGF D.toPre.P.isAb D.toPre.P.isLB E.aB E'.aB hB
  refine ⟨rosatiAdj_generic U.toUnifPre E.ext E'.ext u hu, hB, fun χ => ?_, fun χ => ?_⟩
  · have h₁ := cls_of_gen D.toPre E.aB χ _ (E.u χ) (E.u_norm χ).1
    have h₂ := cls_of_rosati D.toPre.P.isLB r hr (𝟙 _) (toUnit _ ≫ D.toPre.c χ)
    rw [Category.id_comp, Category.assoc] at h₂
    refine eq_of_translate_cls D.toPre.P.isLB D.toPre.P.ktriv _ _ ?_
    linear_combination (norm := abel) h₁ + h₂
  · have h₁ := cls_of_gen D.toPre E'.aB χ _ (E'.u χ) (E'.u_norm χ).1
    have h₂ := cls_of_rosati D.toPre.P.isLB r hr (toUnit _ ≫ D.toPre.c χ) (𝟙 _)
    rw [Category.id_comp, Category.assoc, mul_comm _ (𝟙 D.toPre.P.A), mul_comm _ E'.aB] at h₂
    refine eq_of_translate_cls D.toPre.P.isLB D.toPre.P.ktriv _ _ ?_
    linear_combination (norm := abel) h₁ - h₂

end GlobalTheory.UT
