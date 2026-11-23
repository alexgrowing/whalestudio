import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelInductionFromPairs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelInductionFromPairsStatement

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.SepRows GlobalTheory.PairLift GlobalTheory.ChainFr GlobalTheory.Chain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.RowArrow
variable {D : D7}
end GlobalTheory.RowArrow
open GlobalTheory.RowArrow in
theorem GlobalTheory.RowArrow.separatingFamily_extends_by_twisted_row : _root_.GlobalTheory.FunPr.ThetaLocalInputs → PairEx → RowModels → RowStep := by
  intro pr hE _ D _ hS T L μ0 hL sc hc G W M hM i hi S S' MA MB e e' cA cB
  obtain ⟨X, hX, -, -, h3, h4, h5⟩ :=
    GlobalTheory.RealPlaceTheta.exists_record_theta_all pr.discreteSeriesCover pr.harishChandraModules
  have I := GlobalTheory.PairLift.inputs_of_chosenSeries pr.discreteSeriesCover pr.harishChandraModules pr.cuspRapidDecay pr.casselmanWallach D X hX
  have hP := GlobalTheory.PairLift.RuleLift.pairLifts D X I (GlobalTheory.PairLift.cuspAll_of_lowAll D X I
    (GlobalTheory.PairLift.lowAll_of_lowFock D X I (GlobalTheory.LowerMembersRule.lowFock D X I)))
  have rA : (Node.grid i 0).InRange D.R.m := ⟨hi.le, Nat.zero_le _⟩
  have rB : (Node.grid (i + 1) 0).InRange D.R.m := ⟨hi, Nat.zero_le _⟩
  obtain ⟨FA, a1, a2⟩ := exists_frame _ _ _ (W.onb_is _ rA)
  obtain ⟨FB, b1, b2⟩ := exists_frame _ _ _ (W.onb_is _ rB)
  have b3 : (frSgn true FB).cart = G.cartS W.cart (.chi i 0) := funext fun τ => by
    rw [cart_frSgn, b1]; rfl
  have b4 : (frSgn true FB).onb = G.onS W.onb (.chi i 0) := b2
  have hR : ∀ τ, PairPar (GlobalTheory.SignedHC.flip (S' τ)) (S τ)
      (att (GlobalTheory.Grid.cen D τ (D.R.m - i)) (GlobalTheory.Grid.rkV D (i + 1) 0)) (att (GlobalTheory.Grid.cen D τ (D.R.m - i)) (GlobalTheory.Grid.rkV D i 0)) :=
    fun τ => by
      rw [e, e', hc, parRow_eq, parRow_eq]
      exact GlobalTheory.GridParD.pairPar_X D hS i 0 τ hi (Nat.zero_le _)
  have hη : ∀ τ, HasInfExp D L.eta τ (1 / 2) := fun τ =>
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta
      (StepVac.hasInfQ_tau (a := fun _ => 1 / 2) ⟨_, fun _ => by norm_num, L.C.isEta.inf⟩) τ
  have hχ : ∀ τ, HasInfExp D (G.ch.chi (D.R.m - i)) τ (GlobalTheory.Grid.cen D τ (D.R.m - i)) := fun τ =>
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun τ => GlobalTheory.Grid.cen D τ (D.R.m - i)) (G.ch.chi_eq _ (by omega) (by omega))
      ⟨_, fun τ => by simp only [cen_eq, hc]; push_cast; rfl, G.ch.inf _ (by omega) (by omega)⟩ τ
  have hω : IsWeilExp W.ψ (GlobalTheory.Grid.sgn true (G.V (.grid (i + 1) 0))) (G.V (.grid i 0))
      (fun τ => att (GlobalTheory.Grid.cen D τ (D.R.m - i)) (GlobalTheory.Grid.rkV D (i + 1) 0))
      (fun τ => att (GlobalTheory.Grid.cen D τ (D.R.m - i)) (GlobalTheory.Grid.rkV D i 0)) (W.om (.chi i 0)) := by
    refine ⟨_, _, W.om_is (.chi i 0) rB, fun τ => ⟨?_, ?_⟩⟩
    · have r : (G.pS (.chi i 0)).rank = GlobalTheory.Grid.rkV D (i + 1) 0 := (node_isV G hL rB).rank
      rw [GridData.chrS, r]
      exact exp_att (hχ τ) (hη τ) _
    · have r : (G.pT (.chi i 0)).rank = GlobalTheory.Grid.rkV D i 0 := (node_isV G hL rA).rank
      rw [GridData.chrT, r]
      exact exp_att (hχ τ) (hη τ) _
  have hv := (W.vac_is i hi).2
  have v0 : IsVacF W.ψ W.θ (frSgn true FB) FA (W.vac i) := ⟨hv.theta, fun τ => by rw [b3, a1]; exact hv.fock τ⟩
  have n0 : W.vac i ≠ 0 := fun h => by
    obtain ⟨⟨p, hp⟩, h2⟩ := hv.norm
    have := h2 p hp
    simp [nrm2, h] at this
  have v1 : ∀ κ, IsVacF W.ψ W.θ (frSgn true FB) FA (W.cosVec i κ) := fun κ => by
    obtain ⟨u, hu, h⟩ := W.cosVec_is
    have th := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is (h i hi κ) hv.theta
    have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hu
    refine ⟨th, fun τ => ?_⟩
    rw [b3, a1]
    exact GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt W.ψ_std.1.1 W.θ_is ho.infPart_eq ho.conj.infPart_eq (h i hi κ) hv.theta th
      (hv.fock τ)
  obtain ⟨hν, h𝓕⟩ := (hM.row i hi.le).haar_fund
  obtain ⟨It, hIt⟩ := lifts_neg h3 h4 h5 hP hE W.θ_is W.ψ_std MA MB hR FA FB (cA.trans a1.symm) (cB.trans b1.symm) hω v0 n0 hν h𝓕
  refine ⟨It, fun F hF κ => ?_⟩
  obtain ⟨F', hF', h⟩ := hIt _ (v1 κ) F hF
  have ef : ∀ P, ptF W.ψ W.θ (frSgn true FB) FA (W.cosVec i κ) P = W.fock (.chi i 0) (W.cosVec i κ) P := fun P => by
    unfold ptF
    rw [b3, b4, a1, a2]
    rfl
  simp only [ef] at h
  exact ⟨F', hF', fun P v => ⟨fun g => (h P v g).1, funext fun g => (h P v g).2⟩⟩
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separating_family_extend_by_twist : _root_.GlobalTheory.FunPr.ThetaLocalInputs → PairEx → RowModels → RowStep := by
  first | exact @_root_.GlobalTheory.RowArrow.separatingFamily_extends_by_twisted_row | exact _root_.GlobalTheory.RowArrow.separatingFamily_extends_by_twisted_row | (intros; apply _root_.GlobalTheory.RowArrow.separatingFamily_extends_by_twisted_row <;> assumption)
end
