import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmDZOfLabelsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Laws
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTrueReadingStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SplitLoc
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InertialTypeOfTameM
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisBlockTypeSplit
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalSeriesConcreteOfDzSwap
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisConjPlaceDual
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsDepthZeroFixedVector
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisTameLabelMu
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DepthZeroRow
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → LabAll D P.T → GlobalTheory.HeightCounting.Up.CenLoc D P.M → GreenLab P.ty.grp → ChiTOk D P.cf → PairedCharacterCondition.RT.AdmDepthZeroTypes (D := D) := by
  intro hP hL D P hRow hLab hCen hGreen hChi
  obtain ⟨S, hS, -, -⟩ := _root_.GlobalTheory.T.exists_true_reading_with_laws_suppLaws hP.fin hL D P hRow
  have hLoc : _root_.GlobalTheory.PendOf.LocalDatumCondition hL D := _root_.GlobalTheory.DepthZeroAssembly.locDZ_of_split_reg_m_alt hL D
    (_root_.GlobalTheory.T.splitLoc_of_greenLab_depth_zero hP hL D P.ty.grp hGreen) (_root_.UpperTheory.Lit.Dz.blockTypeSplitProp hP hL D P.ty.grp hGreen)
  have hConj : ConjDual D := _root_.GlobalTheory.T.conjDual_of_labAll hP hL D P hLab
  intro i k v PI
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  intro ρ f hρ hser hocc hsq hu
  have hw : IsSplitPl D.host (D.naut.plGw k v) := GlobalTheory.T.isSplitPlace_of_over_type_prime D k _ (D.naut.plGw_over k v)
  obtain ⟨x, hx⟩ := _root_.GlobalTheory.T.exists_blockVec_notKilled_of_occurs hP hL D P hCen S hS i PI k v hw ρ f ⟨hρ, hser⟩ hocc
  obtain ⟨htame, hχ, u, hu', hlabχ⟩ := _root_.GlobalTheory.T.nonGalois_tame_label_mu_alt hP hL D P hChi S hS i k v hw
  obtain ⟨hmono, hlab⟩ := hLoc k v (S i _ hw).mu hχ (u : ZMod (D.host.g k)) ((S i _ hw).rep PI) ρ f htame hlabχ
    ⟨hρ, hser⟩ hsq (hu u hu') ⟨x, hx⟩
  have hrc : _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v) _ ((S i _ hw).rep PI) = P.T.e _ (D.naut.locV i PI (D.naut.plGw k v)) := by
    rw [← hS.rc i _ hw]
    exact ((S i _ hw).locV PI).symm
  have hm0 : D.naut.mono0 (D.naut.locV i PI (D.naut.plGw k v)) := by
    rw [hrc] at hmono
    exact (P.T.mono0 _ _).2 hmono
  have hl : D.naut.items₂ k (D.naut.plGw k v) (D.naut.locV i PI (D.naut.plGw k v)) =
      f * (X - C (u : ZMod (D.host.g k))) ^ D.R.t := by
    rw [P.lab k v, ← hlab]
    unfold _root_.GlobalTheory.PendOf.localLabelPolynomial
    rw [hrc]
  have hf0 : D.ntypes.eSer k f ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hser
    exact GlobalTheory.SerOSys.ZSum.zIdem_ne_zero ρ hρ hser.symm
  have hdegf : f.natDegree = D.R.r := by
    by_contra hne
    exact hf0 (D.ntypes.eSer_zero k f fun h => hne h.2.1)
  have hfne : f ≠ 0 := by
    intro h; apply hf0; exact D.ntypes.eSer_zero k f fun h' => by rw [h] at h'; exact (h'.1.ne_zero rfl)
  have hdeg : (f * (X - C (u : ZMod (D.host.g k))) ^ D.R.t).natDegree = D.R.nV := by
    rw [natDegree_mul hfne (pow_ne_zero _ (X_sub_C_ne_zero _)), natDegree_pow, natDegree_X_sub_C, hdegf, mul_one]
    rfl
  refine ⟨u, hu', hm0, hl, fun w' hc => ?_⟩
  obtain ⟨hc1, -, hc3⟩ := hConj i PI k v w' hc
  have hroots : Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w' (D.naut.locV i PI w')) =
      (Formalism.CyclotomicNorms.rootsBar (f * (X - C (u : ZMod (D.host.g k))) ^ D.R.t)).map (·⁻¹) := by
    rw [hc3, hl]
  refine ⟨hc1 hm0, ?_, hroots⟩
  rw [← card_rootsBar, hroots, Multiset.card_map, card_rootsBar, hdeg]
end GlobalTheory.DepthZeroRow
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admDepthZero_of_rowMod_labAll_greenLab : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → LabAll D P.T → GlobalTheory.HeightCounting.Up.CenLoc D P.M → GreenLab P.ty.grp → ChiTOk D P.cf → PairedCharacterCondition.RT.AdmDepthZeroTypes (D := D) := by
  first | exact @_root_.GlobalTheory.DepthZeroRow.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.DepthZeroRow.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.DepthZeroRow.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
