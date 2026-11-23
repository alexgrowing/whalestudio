import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroOfPrintsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Laws
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTrueReadingStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisMore
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisFurtherStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MDzLoc
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped Pointwise
namespace GlobalTheory.DepthZeroType
theorem depthZero_tame_alt : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → GlobalTheory.Published.DepthZeroSupport → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → GlobalTheory.HubX.DepthZeroG D := by
  intro hp h2 hL D P hR i w hwS hk Q σ hσ
  obtain ⟨S, hS, -, -⟩ := _root_.GlobalTheory.T.exists_true_reading_with_laws_suppLaws hp.fin hL D P hR
  have hw : IsSplitPl D.host w := hk.elim fun k h => isSplitPl_of_over D k w h
  have ht := (_root_.GlobalTheory.MuTameQS.main_alt_alt hL D P S hS i w hw (Or.inl hwS)).1
  obtain ⟨v, hv0, hv⟩ := (_root_.GlobalTheory.T.type_block_of_tame_at_split_place hL D P S hS i w hw hk ht).2 Q
  have hfix : v ∈ GlobalTheory.PRep.fixed ((S i w hw).rep Q).π
      (GlobalTheory.SplitWeil.KOne (w.adicCompletion D.host.E) (Fin (D.R.r + D.R.t))) := by
    intro h
    have := GlobalTheory.JacBlock.KOne_le_stab ht hv h.2
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    exact this
  rw [P.T.inePol w _ σ (mem_Ine_of_wild D w hσ), (S i w hw).locV Q, hS.rc]
  exact _root_.GlobalTheory.DepthZeroLoc.main_m_alt hp.bz h2 hL D w _ _ ⟨v, hfix, hv0⟩
    (hk.elim fun k h => UpperTheory.One.M.isQg_of_over D k w h) σ hσ
end GlobalTheory.DepthZeroType
end
end
end
