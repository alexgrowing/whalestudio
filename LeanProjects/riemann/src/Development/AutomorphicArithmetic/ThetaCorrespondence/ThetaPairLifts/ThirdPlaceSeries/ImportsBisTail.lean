import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NonemptyJoinOfAgreement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisSideStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainOfStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsThetaModStatement
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.JoinExists
theorem main_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Nonempty (_root_.GlobalTheory.NPin.CharacterChoiceJoin P) := by
  intro h1 h2 hL D P X hA
  have key : ∀ i : D.nd.Loc, ∃ Y : RowMod D P.rep (D.nd.j i),
      ∀ (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), GlobalTheory.NJoin.IsCanon X j hj Y := by
    intro i
    have hr := D.nd.j_range i
    have hlt : D.nd.j i - 1 < D.R.m := by omega
    obtain ⟨Y, hY⟩ := _root_.GlobalTheory.T.exists_canonical_module_at_successor h1 h2 hL D P X hA ⟨D.nd.j i - 1, hlt⟩ (D.nd.j i) (by simp only; omega)
    refine ⟨Y, fun j hj => ?_⟩
    have hj' : j = ⟨D.nd.j i - 1, hlt⟩ := Fin.ext (by simp only; omega)
    subst hj'
    exact hY
  choose Y hY using key
  exact ⟨{ form := _root_.GlobalTheory.T.mtForm_of_realAt_agree hL D P X hA
           rowM := Y
           th := fun i j hj => (_root_.GlobalTheory.T.nonempty_theta_mod_of_is_canon h1 h2 hL D P X hA i j hj (Y i) (hY i j hj)).some }⟩
end GlobalTheory.JoinExists
end
