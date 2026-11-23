import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfOverTwo
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.MuUnrTie
theorem main_alt_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D),
    GlobalTheory.HubX.MuUnr D := by
  intro _ hL D P i hl w hw
  have hj := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hjj : j.1 + 1 = D.nd.j i := by simp only [j]; omega
  have hlp : (D.nd.l i).Prime := (D.nd.lPrime i).out
  rw [P.chr.unr_iff, P.chr.tw, P.chr.muC i j hjj, P.chr.etaTinv]
  refine GlobalTheory.MuTameQS.unrAt_mul ?_ (unrAt_inv (P.cf.isEta.unr w))
  unfold TupTied.tup
  refine GlobalTheory.MuTameQS.unrAt_mul ?_ ?_
  · refine (P.cf.isMu0 j).unr w fun k hk => ?_
    have e := eq_of_over_two hlp (D.host.g_prime k) w hw hk
    apply hl
    rw [e]
    fin_cases k <;> simp [TwistedPlaces.gset]
  · rw [D.nd.mu_w i, P.tp.xi_tw, D.nd.w_l i]
    refine GlobalTheory.MuTameQS.unrAt_mul ?_ ?_
    · unfold CharFrame.delAt
      split_ifs with h
      · refine P.cf.isDel'.unr w fun ho => D.host.pde_ne ?_
        rw [← h]
        exact eq_of_over_two hlp D.host.pde'_prime w hw ho
      · refine P.cf.isDel.unr w fun ho => h ?_
        exact eq_of_over_two hlp D.host.pde_prime w hw ho
    · have hpsi := P.tp.psi_is (D.nd.w i) (D.nd.w_tw i)
      rw [D.nd.w_l i, ← P.Q_eq i] at hpsi
      exact (hpsi.ram w).2 fun hq => D.nd.SQ_l i w (Or.inr hq) hw
end GlobalTheory.MuUnrTie
end
