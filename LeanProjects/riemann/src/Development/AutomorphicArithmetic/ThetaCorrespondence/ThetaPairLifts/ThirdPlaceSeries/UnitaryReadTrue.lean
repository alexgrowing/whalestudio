import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.UnitaryReadTrue
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventuallyUnr
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SwOn
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SphRead
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodAUIso
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.ExistsCgTrueCharSide

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC GlobalTheory.UnitaryReadTrue
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace UpperTheory.One.M
theorem unitaryRead_true_alt (sw : _root_.UpperTheory.One.M.TrivialCondition) : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (A : _root_.GlobalTheory.HeightCounting.AUSideAlt D),
    _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL D T A → Ud.UnitaryReadS D.nbc (_root_.GlobalTheory.FormDict.recT_alt T hL) := by
  intro hL D T A hA j h1 h2 π
  obtain ⟨π₀, rfl⟩ := A.surj j h1 h2 π
  obtain ⟨F⟩ := GlobalTheory.T.unitaryFiniteAdeleIdentification_nonempty_presentations D.host.E D.R.nV
  obtain ⟨U, hU⟩ := GlobalTheory.T.exists_dictionary_cm_field_automorphic D.host.E D.R.nV F π₀
  refine ⟨U, hU.1, ?_, ?_, ?_⟩
  · intro w hw σ hσ
    obtain ⟨s, rfl⟩ := exists_splitPlace_w D w hw
    obtain ⟨τ, hτ, ⟨e⟩⟩ := GlobalTheory.T.localComponents_agree_splitPlace_dictionary _ _ F π₀ U hU s σ hσ
    have h := hA j h1 h2 π₀ s τ hτ
    show _ = (T.e s.w).symm _
    have hc : GlobalTheory.LocLanglands.cls τ = GlobalTheory.LocLanglands.cls (ParLaws.toRep σ) := by
      unfold GlobalTheory.LocLanglands.cls
      rw [(GlobalTheory.SmGL.IrrRep.cl_eq_iff (σ := τ) (τ := ParLaws.toRep σ)).2 ⟨e⟩]
    rw [Equiv.eq_symm_apply, h, hc]
  · intro w hw hsph
    let v := GlobalTheory.SplitConjPlace.belowE (D := D) w
    have hv : NG.OverPl w v := rfl
    have hsph0 := (A.sph j h1 h2 π₀ w v hw hv).1 hsph
    obtain ⟨s, ϖ, q, hs, hq⟩ :=
      GlobalTheory.InertPlaceConj.exists_conj_isUnramInv D.host.E w (host_unramified D.host w) (not_isSplitAt D w hw)
    obtain ⟨-, hI⟩ := _root_.UpperTheory.One.M.Sph.satAgree _ _ F π₀ U hU v w hv
    obtain ⟨⟨Dv, hDs, hDϖ⟩, hI2⟩ := hI s ϖ q hs hq
    obtain ⟨α, hα, hsat⟩ := A.sat j h1 h2 π₀ v w hv Dv (_root_.UpperTheory.One.M.Sph.exists_satAt_of_dict _ _ F π₀ U hU v w hv hsph0 Dv)
    obtain ⟨α', hα', hS⟩ := hI2 Dv α hDs hDϖ hα
    refine ⟨fun w' hw' σ hσ => ?_, α', ⟨s, ϖ, q, hs, hq, hS⟩, ?_⟩
    · obtain ⟨t, rfl⟩ := exists_splitPlace_w D w' hw'
      obtain ⟨τ, hτ, ⟨e⟩⟩ := GlobalTheory.T.localComponents_agree_splitPlace_dictionary _ _ F π₀ U hU t σ hσ
      have hc : GlobalTheory.LocLanglands.cls τ = GlobalTheory.LocLanglands.cls (ParLaws.toRep σ) := by
        unfold GlobalTheory.LocLanglands.cls
        rw [(GlobalTheory.SmGL.IrrRep.cl_eq_iff (σ := τ) (τ := ParLaws.toRep σ)).2 ⟨e⟩]
      have := _root_.UpperTheory.One.M.New.sphGood sw hsph0 (noSplit D w v hw hv) t τ hτ
      rwa [hc] at this
    · rw [hsat]
      congr 1
      funext i
      exact (hα' i).symm
  · intro τ
    obtain ⟨b, hb, -⟩ := GlobalTheory.algWt_contragredient _ _ π₀.toAlgWt
    obtain ⟨lam, hl, hhw⟩ := GlobalTheory.T.algebraicWeight_agrees_under_modularForm_dictionary _ _ F π₀ U hU b hb τ
    refine ⟨lam, hl, ?_⟩
    rw [A.wt j h1 h2 π₀ b hb, A.infW j h1 h2 b τ lam.w hhw, infOf_eq_infOfWeight]
theorem cusp_read_rec_t : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut),
    _root_.GlobalTheory.HeightCounting.CGTrueT hL D T → CuspReadG (_root_.GlobalTheory.FormDict.recT_alt T hL) := by
  intro hL D T C a P ha hP hg
  haveI := host_isCMField D.host
  have hu : (CG.mk P).IsUnitary := CsdUnitary.isUnitary_of_isCsd _ a (CG.mk P) hP
  obtain ⟨π, hπ⟩ := _root_.UpperTheory.One.M.New.cgSurj C a ha ⟨CG.mk P, hu⟩ fun w => by
    obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL D.host.E a P w
    exact (ParLawsT.cls_loc_eq_of_isLocComp hσ).symm ▸ hg w σ hσ
  refine ⟨π, (C.csd a _).2 (by rw [hπ]; exact hP), fun w σ hσ => ?_, fun τ m hm => ?_⟩
  · apply (T.e w).injective
    rw [C.loc, hπ]
    simp only [_root_.GlobalTheory.FormDict.recT_alt, Equiv.apply_symm_apply]
    exact _root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL hσ _
  · rw [C.inf, hπ]
    exact CG.HasInfChar.infChar_eq (π := CG.mk P) hm
end UpperTheory.One.M
end
end
