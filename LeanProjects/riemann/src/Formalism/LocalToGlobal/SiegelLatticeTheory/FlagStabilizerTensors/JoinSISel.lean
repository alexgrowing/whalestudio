import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSI
import Formalism.LocalToGlobal.IndefiniteRealisationChoice
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TheoremSRecursion

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Top4 Formalism.L2.SG.JoinSI Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.JoinSISel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section At

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

def MIAt {R : Formalism.L2.RecT ex} {P : Formalism.L2.Rows.RowSideFamily ex}
    {Dcf : ∀ Zs : Formalism.L2.Indef.DefSub P.A3.fam3.amb3, Formalism.L2.Indef.DefCols (P.A3.side3 P.Ps P.ψs Zs)}
    {Spf : ∀ Zs, Formalism.L2.Indef.SPer (Dcf Zs)} {Zscf : Formalism.L2.Indef.DefSub P.A3.fam3.amb3 → Formalism.L2.Indef.IndefScale P.A3.fam3.base3}
    {S : Formalism.L2.SG.SpectralTiesReal.STiesR R} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : Formalism.IndefR.RealT R P Dcf Spf Zscf S Ks) : Prop :=
  (cx Q).MIstar (Q.F.eV (cx Q).zs) Q.sEE

end At

def BaseVectorImageFull (D : D7) : Prop := (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤

abbrev SelJ (𝒜 : FamClass) (sel : Formalism.L2.TSel 𝒜) (selS : SelS 𝒜 sel) (selP : BaseLevelCompatibleSelection 𝒜 sel) (selDH : Formalism.L2.Top3.SelDH 𝒜 sel)
    (selC : ColumnCompatibleSelection 𝒜 sel selP) (selK : SelK 𝒜 sel) (selI : IndefiniteRealisationChoice 𝒜 sel selS selP selDH selC selK) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    JoinSI (R := (sel Fm hc).2 x hx h i) (S := selS Fm hc x hx h i) (Q := selI Fm hc x hx h i)

variable {𝒜 : FamClass} {sel : Formalism.L2.TSel 𝒜} {selS : SelS 𝒜 sel} {selP : BaseLevelCompatibleSelection 𝒜 sel} {selDH : Formalism.L2.Top3.SelDH 𝒜 sel}
  {selC : ColumnCompatibleSelection 𝒜 sel selP} {selK : SelK 𝒜 sel} {selI : IndefiniteRealisationChoice 𝒜 sel selS selP selDH selC selK}

theorem finXRow_of_gap (hFXC : Formalism.L2.SG.PoincareAmplitudeLowerBounds.FinXC)
    (hG : Closed 𝒜 fun Fm _ => ∀ hc : 𝒜 Fm, EvSel sel Fm hc fun x _ _ i => Formalism.L2.SG.ConcreteSettingExists.GapHyp (Fm.D x i)) :
    Closed 𝒜 fun Fm _ => ∀ hc : 𝒜 Fm, EvSel sel Fm hc fun x hx h i => FinX (selS Fm hc x hx h i).Y :=
  hG.imp fun Fm _ _ H hc => by
    obtain ⟨x0, H'⟩ := H hc
    exact ⟨x0, fun x hx h hx0 i => hFXC _ (selS Fm hc x hx h i).toSTies (H' x hx h hx0 i)⟩

end Formalism.L2.SG.JoinSISel
