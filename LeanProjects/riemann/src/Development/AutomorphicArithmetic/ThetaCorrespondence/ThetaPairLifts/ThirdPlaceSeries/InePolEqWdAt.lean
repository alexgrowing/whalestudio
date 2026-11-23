import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaPolynomialCompatible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
namespace GlobalTheory.TieInePolyPin
theorem inePol_eq_wdAt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (m : ℕ) (r : GE D.nd →* GL (Fin m) (D.nd.O i)), Continuous (fun g => ((r g : GL _ _) : Matrix (Fin m) (Fin m) (D.nd.O i))) → GlobalTheory.Pst.IsPstAt (D.loc (D.nd.l i)) (D.nbr i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w) → ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), D.naut.inePol (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) r) w) σ = (GlobalTheory.Pst.wdAt (D.loc (D.nd.l i)) (D.naut.iotaQC i) (D.nbr i w hw) (D.nd.plOm.2 w) (D.nbr_ind i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w)).inePol σ := by
  intro hL D P i w hw m r hc hpst σ hσ
  have hc' : Continuous (fun g => ((GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w g : GL _ _) : Matrix (Fin m) (Fin m) (Om (D.nd.l i)))) :=
    ((hc.matrix_map (GlobalTheory.T.continuous_iotaOQ' D.nd D.naut i)).comp continuous_subtype_val)
  rw [(P.wdOf i m (mapRep (iotaOQ D.nd D.naut i) r) w).1, P.T.inePol w _ σ hσ]
  obtain ⟨LL, Bw, hj, e2⟩ := P.wd.above (D.nd.l i) (D.naut.iotaQC i) (mapRep (iotaOQ D.nd D.naut i) r) w hw
  rw [e2]
  refine congrArg (fun x => GlobalTheory.WeilDeligne.WD.inePol x σ) ?_
  exact GlobalTheory.Pst.BridgeParam.wdAt_indep_bridge (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) ⟨D.locT (D.nd.l i)⟩
    (D.naut.iotaQC i) D.host.E D.nd.Om (D.nd.plOm.1 w) w _ _ Bw (D.nbr i w hw) (D.nd.plOm.2 w) hj (D.nbr_ind i w hw) m _ hc'
    (GlobalTheory.T.isPotSemistable_independent_of_inducingEmbedding (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) ⟨D.locT (D.nd.l i)⟩ D.host.E D.nd.Om (D.nd.plOm.1 w) _ _
      (D.nbr i w hw) Bw (D.nbr_ind i w hw) hj m _ hc' hpst) hpst
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), GlobalTheory.Pass.TieInePoly D := by
  intro hL D P i w hw K' h hN hF hS m r hc hpot σ hσ p hp d hd
  exact GlobalTheory.T.inertiaPolynomial_kills_potentiallyCrystalline_module D i w hw K' h hN hF hS m r hc hpot σ hσ p
    (hp.trans (_root_.GlobalTheory.TieInePolyPin.inePol_eq_wdAt_alt hL D P i w hw m r hc (GlobalTheory.T.potSemistable_of_potCrystalline_decompositionGroup D i w hw K' h hN hF hS m r hc hpot) σ hσ)) d hd
end GlobalTheory.TieInePolyPin
end
