import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.RationalColumns.ColFacts
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
namespace Formalism.L2.DIV.RatFullPt
section CSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) {G : Type} [Group G] [Fintype G]
  (r : Representation K G S.Forms) (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ)
end CSD
section Forms
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end Forms
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
theorem indefinite_realisation_column_facts (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) {s : ℕ} (hOk : P.A3.fam3.Ok3 s) (hsep : P.A3.fam3.TypesSep3)
    (hP : PrimRows3 Q.Rl Q.F) (hS : (Q.Rl.toCx3 Q.F).SEEIso Q.sEE)
    (hM : (Q.Rl.toCx3 Q.F).MIstar2 (Q.F.eV (Q.Rl.toCx3 Q.F).zs) Q.sEE) : ColFacts P.S1 P.C := by
  have hC := complex_data_conditions_base_level_of_primitive_links hOk hsep Q.charW hP
  have hcols := (Q.Rl.toCx3 Q.F).exists_zeta_pairing_factors_through_periods Q.F.cr Q.F.cv (Q.F.eV (Q.Rl.toCx3 Q.F).zs) Q.sEE (hC.wf true) hC.h4pos (hC.what₂ true).1
    (hC.ratMu true) hC.jIsoR (hC.levs true).1 (hC.levs true).2.1 (hC.levs true).2.2 (definite_coordinates_in_good_part _ true)
    (EvTie.evTie_of_ok hOk Q.F _) hS hM
  have hDc : HEq (Dcf (Q.Rl.toCx3 Q.F).zs) P.Dc :=
    (congr_arg_heq Dcf Q.zs).trans (heq_of_eq Q.dc)
  have hSp : HEq (Spf (Q.Rl.toCx3 Q.F).zs) P.Sp := (congr_arg_heq Spf Q.zs).trans Q.sp
  exact colFacts_transport Q.zs hDc hSp Q.s1 Q.col
    ⟨hC.wf true, hC.h0, fun t => (Q.Rl.toCx3 Q.F).rowMat_bij Q.F.cr true (hC.what₂ true).1 (hC.ratMu true) t,
      (Classical.epsilon_spec hcols).1⟩
end Formalism.L2.DIV.RatFullPt
end
end
