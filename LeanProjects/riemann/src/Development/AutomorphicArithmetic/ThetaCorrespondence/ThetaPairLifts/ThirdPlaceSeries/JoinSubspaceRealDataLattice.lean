import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JoinSubspaceRealDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealRecOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ToSTiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealPins
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColJoinSOfSTiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JoinPin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SeeExJoinPin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain MeasureTheory
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.Theta Formalism.L2.SG.RowsJoinPinned
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe GlobalTheory.Mem.SJ
namespace GlobalTheory.Mem.KJoinLat
section
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
  {R : _root_.Formalism.L2.RecTAlt ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} {P : RowSideFamily ex}
  {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs, SPer (Dcf Zs)}
  {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
theorem joinSI_nonempty_and_V0_spans (Q : _root_.Formalism.IndefR.IndefiniteRealisation R P Dcf Spf Zscf S Ks) (hPin : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation Q) (hSee : _root_.Formalism.IndefR.IndefiniteRealisationExtends Q) (n : ℕ)
    (hOk : P.A3.fam3.Ok3 n) (hSep : P.A3.fam3.TypesSep3) (hPrim : PrimRows3 Q.Rl Q.F)
    (hLat : HLatTie (Formalism.BasicNotions.RowSide.sharp D).RR (P.A3.indefDown P.S1).RR (P.A3.indefDown P.S1).XE P.I.eRR)
    (hDc : RowsHoldDcPt3 P) (hSchur : SchurAll D) (hSig : (D.sp.Y 0).SigOK) (hJ : _root_.GlobalTheory.Mem.JTop.JoinPinAlt Q) :
    Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin R S Q) ∧ (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  obtain ⟨eE, hRead, hRow⟩ := hJ
  have hι : Q.ιS = (Formalism.L2.SG.RowsJoinPinned.iotaX S.X S.inst).toMulEquiv :=
    (GlobalTheory.Mem.JIota.heq_iota_iff D S.X S.inst Q.ιS).1 Q.ιS_eq
  have hEv := Q.seeEval (by obtain ⟨-, c', hc'⟩ := hSee; exact ⟨c', hc'⟩)
  rw [hι] at hEv
  have hκ : Q.uS * (Q.κS : ℂ) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · intro h0
      have := Q.uS_norm
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    · exact_mod_cast Q.seeK.1.ne'
  obtain ⟨Rd, M, hw, h1, h2, h3, h4, hon, hT⟩ :=
    core_latTie Q.Rl Q.F n hOk hSep Q.charW hPrim hSchur hSig P.Zs Q.zs P.S0 P.S1 Q.s1 P.Dc Q.dc P.Sp Q.sp ex.p0 P.C P.NuC
      P.I P.tied.div hLat (fun u x y => hDc u P.A3.A.μ0 x y) S.X S.inst S.G S.Y.hK (_root_.Formalism.IndefR.pwOf_alt S Q.hin) Q.wdD Q.bR Q.wdD_wU
      Q.spPin (_root_.GlobalTheory.Mem.JTop.bR_heq_eMu_single Q hPin) Q.tS Q.cS hEv Q.sEE Q.sEEc _ Q.sEEj hκ
      (fun x hx => (Q.seeDef x hx).trans (by rw [hι])) eE hRead
  refine ⟨⟨⟨Rd.wU, hw, M.cφ, M.cF, M.eR, h1, h2, h3, h4, fun hF => ?_⟩⟩, hon⟩
  obtain ⟨v₀, -, a, -, hj⟩ := hRow hF
  exact hT (_root_.Formalism.L2.SG.JoinSI.spectralRowIsometry S hF) v₀ a hj
end
theorem join_subspace_real_data_lattice_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Yd cX) (x : TwIn ex) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : SPack D fun u => (Rc.T.cols.forms u).to0) (S : SRest P) (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc (S.toRealSpectralMatching Rc)) (c : ℝ), ∀ n : ℕ, SchurAll D → _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput y) → Holds x.R x.F → x.A3.fam3.Ok3 n → x.A3.fam3.TypesSep3 → HLatTie (Formalism.BasicNotions.RowSide.sharp D).RR (x.A3.indefDown (divisionPairOfAdelicFormsFaceColumnsData x).S1).RR (x.A3.indefDown (divisionPairOfAdelicFormsFaceColumnsData x).S1).XE (divisionPairOfAdelicFormsFaceColumnsData x).I.eRR → RowsHoldDcPt3 (divisionPairOfAdelicFormsFaceColumnsData x) → SeeAt x.R.toRealDat x.F.lv2 P.X P.inst y.tS → EvalTieT (MP x.R.toRealDat) x.R.toRealDat.ν0 x.R.toRealDat.fd0 (EP x.R.toRealDat x.F.lv2) P.X P.G (iotaX P.X P.inst).toMulEquiv y.tS c → RowJ x.R.toRealDat x.Y.eE P.X P.inst P.G y.tS S.j → Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin Rc (S.toRealSpectralMatching Rc) (_root_.GlobalTheory.Mem.R3.realisationOfInput y)) ∧ (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  intro D L hT Gi Gl K Yd cX ex x Rc P S y c n hSchur hPins hH hOk hSep hLat hDc hSee hEv hRow
  obtain ⟨hSx, hJ⟩ := _root_.GlobalTheory.Mem.JPin.seeEx_joinPin_alt D L hT Gi Gl K Yd cX ex x Rc P S y c hH hSee hEv hRow
  exact _root_.GlobalTheory.Mem.KJoinLat.joinSI_nonempty_and_V0_spans (_root_.GlobalTheory.Mem.R3.realisationOfInput y) hPins hSx n hOk hSep (Holds.prim hH) hLat hDc hSchur (D.sp.Y_sig 0) hJ
end GlobalTheory.Mem.KJoinLat
end
end
