import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutoffBoundStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TiedGoodIdemStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoUnitaryTiedStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ActMemMKStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwoLogCardLevelsLeStatement

set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
namespace GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem cutAt_of_rows_alt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz)
    (hp : p.PointConditions') (ht : RecTied D L) (i : Fin D.R.m) (PP A : ℝ) (hN : HostNum D L PP A 3) : CutAt p i := by
  obtain ⟨h1, h2, h3, h4⟩ := _root_.GlobalTheory.T.group_idempotent_coefficients_alt p hp ht
  have hI := GlobalTheory.T.twistedProjector_idempotent_of_groupAlgebra_idem (p.R.toRealDat.FW i) (fun g => (idemOf p.P.A3.A.X).coeff g) h1
  refine ⟨hI, fun σ x y => ?_, fun x hx => ?_, _root_.GlobalTheory.T.two_mul_log_card_Gp_le_b p hp ht PP A hN⟩
  · exact GlobalTheory.T.twistedProjector_orthogonal_of_unitary_action (p.R.toRealDat.FW i) (fun g => (idemOf p.P.A3.A.X).coeff g) _ hI (_root_.GlobalTheory.T.row_inner_product_invariant_alt p hp ht i σ)
      (fun g => h4 _ g) x y
  · exact GlobalTheory.T.card_smul_twistedProjector_mem_integralForms (p.R.toRealDat.FW i) (fun g => (idemOf p.P.A3.A.X).coeff g) h2 h3 (_root_.GlobalTheory.T.rho_mem_MK_of_mem_MK p hp ht i) _ _ x hx
end GlobalTheory.CovTop
end
end
