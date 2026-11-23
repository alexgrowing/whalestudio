import Formalism.LocalToGlobal.BaseRankEqOfRealisation
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Module
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx
namespace Formalism.IndefR.LevelRealisationRankEquality
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
variable {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
theorem indefinite_realisation_base_rank_eq (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) :
    D.what₂.D0 = (P.A3.A.fam.R P.A3.A.fam.μ0).dZ (P.A3.A.fam.lvl P.P0 P.ψ0) (P.Zs.Z P.A3.A.fam.μ0) := by
  have hD := D_of_heq (congrArg (fun Z => P.A3.side3 P.P0 P.ψ0 Z) Q.zs) Q.s0
  have hz : (P.A3.side3 P.P0 P.ψ0 (Q.Rl.toCx3 (faceT P Dcf Spf Zscf)).zs).dQ P.A3.fam3.base3.μ0 =
      (P.A3.side3 P.P0 P.ψ0 P.Zs).dQ P.A3.fam3.base3.μ0 := by rw [Q.zs]
  rw [base_rank_eq_of_tied_level P, ← hD]
  exact hz
theorem indefinite_realisation_mu_eq (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) : Q.Rl.mu = P.S0.μ :=
  mu_of_heq (congrArg (fun Z => P.A3.side3 P.P0 P.ψ0 Z) Q.zs) Q.s0
theorem tup_all_used_of_realisation (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) : TupAllUsed P := by
  apply tupAllUsed_of_cover
  intro t
  rcases Q.charW.tup.mu_used t with h | ⟨w, h⟩
  · exact Or.inl h
  · refine Or.inr ⟨D.plEq.symm w, ?_⟩
    show t = P.S0.μ (D.plEq (D.plEq.symm w))
    rw [← _root_.Formalism.IndefR.LevelRealisationRankEquality.indefinite_realisation_mu_eq Q, Equiv.apply_symm_apply]
    exact h.symm
end Formalism.IndefR.LevelRealisationRankEquality
end
end
