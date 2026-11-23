import Formalism.LocalToGlobal.IndefiniteRealisationChoice
import Formalism.LocalToGlobal.FiniteTOf
import Formalism.LocalToGlobal.BaseRankEqOfRealisation
import Formalism.LocalToGlobal.IndefiniteReal.RealTB
import Formalism.LocalToGlobal.IndefiniteReal.RealPins
import Formalism.LocalToGlobal.IndefiniteReal.RealRec
import Formalism.LocalToGlobal.IndefiniteReal.RealRecPins
import Formalism.LocalToGlobal.Divisibility.PsiWeilOfAbsNorm
import Formalism.LocalToGlobal.IndefiniteReal.ThetaFireRow
import Formalism.LocalToGlobal.CarriedPlMap
import Formalism.LocalToGlobal.Divisibility.ColPins
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT

namespace Formalism.L2.Top4

open Formalism.L2.Top3

section StageB

abbrev SelB (𝒜 : FamClass) (sel : Formalism.L2.TSel 𝒜) (selS : SelS 𝒜 sel) (selP : BaseLevelCompatibleSelection 𝒜 sel) (selDH : SelDH 𝒜 sel) (selC : ColumnCompatibleSelection 𝒜 sel selP) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    Formalism.IndefR.RealTB ((sel Fm hc).2 x hx h i) (selP Fm hc x hx h i).1 (selC Fm hc x hx h i).c.face (selC Fm hc x hx h i).Sp
      (ZscAt sel selP selDH Fm hc x hx h i) (selS Fm hc x hx h i)

variable {𝒜 : FamClass} {sel : Formalism.L2.TSel 𝒜} {selS : SelS 𝒜 sel} {selP : BaseLevelCompatibleSelection 𝒜 sel} {selDH : SelDH 𝒜 sel} {selC : ColumnCompatibleSelection 𝒜 sel selP}

def selKOf (selB : SelB 𝒜 sel selS selP selDH selC) : SelK 𝒜 sel :=
  fun Fm hc x hx h i => { Ks := (selB Fm hc x hx h i).T.Q.c.F }

def selIOf (selB : SelB 𝒜 sel selS selP selDH selC) : IndefiniteRealisationChoice 𝒜 sel selS selP selDH selC (selKOf selB) :=
  fun Fm hc x hx h i => (selB Fm hc x hx h i).Q

def OneMapOf (selB : SelB 𝒜 sel selS selP selDH selC) {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x)
    (i : Fm.Ix x) : Prop :=
  ∀ j, Formalism.IndefR.FWT.OneMapRowR (selB Fm hc x hx h i).T (selB Fm hc x hx h i).Q.Rl.toRealDat (selB Fm hc x hx h i).κ
    (selB Fm hc x hx h i).v₀ (selB Fm hc x hx h i).O (Formalism.IndefR.phEff (selB Fm hc x hx h i).Q.Rl) j

end StageB

section TwPl

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX} {Rc : Formalism.L2.RecT ex} {P : RowSideFamily ex}
  {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)}
  {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem tw_of_heq {Bs : DefBase D.what₂.LL} {Df Df' : DefSide Bs} (h : Df = Df') {S0 : IndefData Df} {S1 : IndefData Df'}
    (hS : HEq S0 S1) : S0.Tw = S1.Tw := by
  subst h; cases eq_of_heq hS; rfl

theorem twPl_eq (Q : RealT Rc P Dcf Spf Zscf S Ks) : Q.Rl.twPl = P.S0.Tw :=
  tw_of_heq (congrArg (fun Z => P.A3.side3 P.P0 P.ψ0 Z) Q.zs) Q.s0

theorem tieTwRec_of {Q : RealT Rc P Dcf Spf Zscf S Ks} (Qr : RealRec Q)
    (hs : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → w ∈ L.supp) : TieTwRec L P.S0.Tw := by
  intro y hy
  rw [← twPl_eq Q] at hy
  have h := (Qr.tw_iff (D.plEq.symm y)).1 (by simpa using hy)
  exact ⟨hs _ h, h⟩

end TwPl

end Formalism.L2.Top4

end
