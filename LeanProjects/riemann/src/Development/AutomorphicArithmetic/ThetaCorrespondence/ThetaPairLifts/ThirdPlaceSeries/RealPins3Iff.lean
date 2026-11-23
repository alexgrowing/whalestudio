import Formalism.LocalToGlobal.IndefiniteReal.NonzeroIndexPlaceIndepConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx
namespace Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
structure IndefiniteRealisationNormalisationDegreeThree {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
    {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
    {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) : Prop where
  muDef : ∀ C CH : ℝ, (Q.Rl.toCx3 Q.F).MuDef Q.F.cr (Q.Rl.num Q.F C CH) Q.Rl.mu
namespace Pins3
variable {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
theorem muDef_iff_alt (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (C CH : ℝ) :
    (Q.Rl.toCx3 Q.F).MuDef Q.F.cr (Q.Rl.num Q.F C CH) Q.Rl.mu ↔
      ∀ w, w ∈ Q.Rl.twPl ↔ (Q.Rl.toCx3 Q.F).W1 Q.F.cr (Q.Rl.num Q.F C CH) w := by
  have ht := Q.charW.tup
  constructor
  · rintro ⟨_, _, _, h4⟩
    exact h4
  · intro h
    refine ⟨fun w hw => ht.mu_ne w ((h w).2 hw), fun w _ => ht.mu_conj w, fun w => ?_, h⟩
    show Q.Rl.mu w = _
    split_ifs with hw
    · rfl
    · exact ht.mu_off w fun hm => hw ((h w).1 hm)
theorem realPins3_iff_twPl_iff_W1 (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) :
    _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree Q ↔ ∀ w, w ∈ Q.Rl.twPl ↔ (Q.Rl.toCx3 Q.F).W1 Q.F.cr (Q.Rl.num Q.F 0 0) w :=
  ⟨fun h => (_root_.Formalism.IndefR.Pins3.muDef_iff_alt Q 0 0).1 (h.muDef 0 0), fun h => ⟨fun C CH => (_root_.Formalism.IndefR.Pins3.muDef_iff_alt Q C CH).2 h⟩⟩
end Pins3
namespace RealPins3
variable {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks}
theorem _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree.w1 (h : _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree Q) (C CH : ℝ) :
    ∀ w, (Q.Rl.toCx3 Q.F).W1 Q.F.cr (Q.Rl.num Q.F C CH) w → w ∈ Q.Rl.twPl :=
  fun w hw => (h.muDef C CH).2.2.2 w |>.2 hw
end RealPins3
end Formalism.IndefR
end
end
