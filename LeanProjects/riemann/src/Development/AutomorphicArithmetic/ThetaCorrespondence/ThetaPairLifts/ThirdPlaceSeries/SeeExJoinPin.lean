import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SeeExJoinPin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealRecOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ToSTiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealPins
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JoinPin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColJoinSOfSTiesR

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain MeasureTheory
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.Theta Formalism.L2.SG.RowsJoinPinned
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe
namespace GlobalTheory.Mem.JPin
set_option maxHeartbeats 4000000 in
theorem seeEx_joinPin_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Yd cX) (x : TwIn ex) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : SPack D fun u => (Rc.T.cols.forms u).to0) (S : SRest P) (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc (S.toRealSpectralMatching Rc)) (c : ℝ), Holds x.R x.F → SeeAt x.R.toRealDat x.F.lv2 P.X P.inst y.tS → EvalTieT (MP x.R.toRealDat) x.R.toRealDat.ν0 x.R.toRealDat.fd0 (EP x.R.toRealDat x.F.lv2) P.X P.G (iotaX P.X P.inst).toMulEquiv y.tS c → RowJ x.R.toRealDat x.Y.eE P.X P.inst P.G y.tS S.j → _root_.Formalism.IndefR.IndefiniteRealisationExtends (_root_.GlobalTheory.Mem.R3.realisationOfInput y) ∧ _root_.GlobalTheory.Mem.JTop.JoinPinAlt (_root_.GlobalTheory.Mem.R3.realisationOfInput y) := by
  intro D L hT Gi Gl K Yd cX ex x Rc P S y c _ hS hE hR
  have hι : y.ιS = (iotaX P.X P.inst).toMulEquiv :=
    (GlobalTheory.Mem.JIota.heq_iota_iff D P.X P.inst y.ιS).1 y.ιS_eq
  have hinj : Function.Injective x.R.HE.e := x.pins.char.base.models.HE.1
  have hread : ∀ y1, x.Y.eE (D.jEE (x.Z.eRR y1)) = Tw.out (s := twAt D.what₂.embLL x.A3.A.v0) (E := x.R.HE.H)
      ((x.R.toCx3 x.F).iC x.F.cr true x.A3.A.μ0 (cpt x.A3.A.v0.embedding y1)) := by
    intro y1
    have h1 := x.Y.eE_read (D.jEE (x.Z.eRR y1))
    rw [x.Z.jEE y1] at h1
    exact hinj ((PiTensorProduct.lift : Mult.MMap (x.R.MY 0) ≃ₗ[ℂ] _).injective h1).symm
  refine ⟨⟨⟨y.tS, hS.fin, ?_, ?_⟩, c, ?_⟩, x.Y.eE, ?_, ?_⟩
  · show ConjLevel y.tS⁻¹ (JR x.R.toRealDat x.F.lv2) (chiR x.R.toRealDat x.F.lv2) (y.ιS ⁻¹' concreteLevelAdelicSubset P.X)
      (fun k => adelicCharacterOfHidaSetting P.X (y.ιS k))
    rw [hι]
    exact hS.conj
  · exact hS.mat
  · show EvalTieT (MP x.R.toRealDat) x.R.toRealDat.ν0 x.R.toRealDat.fd0 (EP x.R.toRealDat x.F.lv2) P.X P.G y.ιS y.tS c
    rw [hι]
    exact hE
  · intro y1 y' h
    obtain rfl := eq_of_heq h
    exact hread y1
  · intro hF
    have hj : _root_.Formalism.L2.SG.JoinSI.spectralRowIsometry (S.toRealSpectralMatching Rc) hF = S.j :=
      _root_.Formalism.L2.SG.JoinSI.isometryOfJoin_eq_of_conj_compat (S.toRealSpectralMatching Rc) hF S.j fun F => S.rowPin F
    rw [hj]
    exact hR
end GlobalTheory.Mem.JPin
end
