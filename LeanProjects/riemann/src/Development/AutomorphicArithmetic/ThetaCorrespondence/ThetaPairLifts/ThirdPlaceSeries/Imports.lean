import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FamilyRowsColumnsValid
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColJoinSOfSTiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IteratesSpanLastStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ItSpansPkStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftEqCIIoStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IoTLiftStatement

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam.IsFam
theorem main_alt_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ f : _root_.GlobalTheory.Fam.FamilyCharacter W u, f.RowOK → f.c.Is ∧ (f.ColOK → ∀ t, (f.t t).Is) := by
  intro hDS hHC D L hT Gi Gl Kc Yd cX ex W u hP f hR
  have hC := hP.bot.hyp.2.2.2.1
  have hstd : IsStdChar D (_root_.GlobalTheory.Fam.pk_z W).ψ (-1) := (hC.chain.ωX W.P.A3.A.μ0).std
  have hinf : IsInfFam (_root_.GlobalTheory.Fam.pk_z W).θ := hC.models.inf
  have spanT : ∀ n (e : D.R.m - 1 = n), GlobalTheory.Core.Mi.ItSpans ((_root_.GlobalTheory.Fam.pk_z W).MY n) (_root_.GlobalTheory.Fam.pk_z W).MX
      (Eq.rec (motive := fun n _ => PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] SmT ((_root_.GlobalTheory.Fam.pk_z W).MY n)) (_root_.GlobalTheory.Fam.pk_z W).ItX e) := by
    intro n e
    subst e
    exact _root_.GlobalTheory.T.itSpans_MY_last_MX hDS hHC W hP
  refine ⟨⟨hstd, hinf, hR.x, (GlobalTheory.Unf.CoCptOf.coCpt_of_isAniso_or_posDef D D.sp.X').2 GlobalTheory.Hk3.StepX.gram_posDef_X,
    hR.meas.μf, hR.meas.ρJ, hR.meas.ρB, fun j hj => _root_.GlobalTheory.T.itSpans_MY_succ hDS hHC W hP j hj, fun j h => spanT _ (idx_top h)⟩, fun hCol t => ?_⟩
  exact
    { sBF := fun j ρ h => ⟨((hR.row t).sBF j ρ h).1, ((hR.row t).sBF j ρ h).2.1⟩
      sFB := fun j σ h => ⟨((hR.row t).sFB j σ h).1, ((hR.row t).sFB j σ h).2.1⟩
      pt := fun j hj P => GlobalTheory.Chain.InnerSteps.theta_pureTensorO hstd hinf _ _ _ _
        (GlobalTheory.VecTheta.isThetaFunO_stepVec ((hR.row t).vP j hj)) P
      ptT := fun j h P => GlobalTheory.Chain.InnerSteps.theta_pureTensorO hstd hinf _ _ _ _
        (GlobalTheory.VecTheta.isThetaFunO_stepVec ((hR.row t).vT j h)) P
      CC := fun j _ => ⟨_, _, le_rfl⟩
      CT := ⟨_, _, le_rfl⟩
      io := _root_.GlobalTheory.T.lift_s_eq_ci_smul_io W u hP f hR t
      ioT := _root_.GlobalTheory.T.lift_s_last_eq_ci_succ_smul_io W u hP f hR t
      cI := fun j hj => hR.meas.cIOf_ne_zero (_root_.GlobalTheory.Fam.complexLevelStructure W) t j hj
      ker := hCol.ker t
      e := hCol.e t
      eT := hCol.eT t
      stabK := hCol.stabK t
      stabS := hCol.stabS t }
end GlobalTheory.Fam.IsFam
end
