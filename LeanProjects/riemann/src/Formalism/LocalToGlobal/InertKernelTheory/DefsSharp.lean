import Formalism.LocalToGlobal.InertKernelTheory.SecondKernelEntrywiseLastLevel

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.SecondKernelSharpWeights

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.KerInert.K2 Formalism.L2.KerInert.SecondKernelInstances

section Gen

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc0 : G.Consts} {Dx : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc0 Dx cX}

def FormsVLamAt (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (j : ℕ) : Prop :=
  ∀ (x : ((ex.tw.fm u μ).lat j).V) (c : (D.chTw u μ).cls j),
    IsVLam ((t.O u μ).frm j) (fun τ r => (nuT D u j τ r : ℤ) - (D.chTw u μ).sSharp j τ) ((ex.tw.fm u μ).emb j x c)

def FormsTrueWtAt (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (j : ℕ) : Prop :=
  ∀ lamT : D.what₂.Tau → Fin (D.R.N j) → ℤ,
    (∀ τ r, (lamT τ r : ℚ) = ((((ex.tw.fm u μ).lam j τ).w r : ℤ) : ℚ) - (j : ℚ) * ((D.R.t : ℚ) + 1) / 2) →
    ∀ (x : ((ex.tw.fm u μ).lat j).V) (c : (D.chTw u μ).cls j),
      IsVLam ((t.O u μ).frm j) lamT ((ex.tw.fm u μ).emb j x c)

end Gen

def SharpWtIs : Prop :=
  ∀ (D : D7) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (j : ℕ), j < D.R.m →
    ∀ (τ : D.what₂.Tau) (r : Fin (D.R.N j)),
      ((((nuT D u j τ r : ℤ) - (D.chTw u μ).sSharp j τ : ℤ)) : ℚ) =
        ((((Tw.fm u μ).lam j τ).w r : ℤ) : ℚ) - (j : ℚ) * ((D.R.t : ℚ) + 1) / 2

def FormsSharpAtOf : Prop :=
  SharpPoly → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (j : ℕ),
    j ≤ D.R.m → FormsVLamAt t u μ j → FormsSharpAt t u μ j

def FormsSharpAtOfTrue : Prop :=
  SharpPoly → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (j : ℕ),
    j < D.R.m → FormsTrueWtAt t u μ j → FormsSharpAt t u μ j

end Formalism.L2.KerInert.SecondKernelSharpWeights
