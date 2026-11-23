import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsFramedAdapted
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmulColMul

noncomputable section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeSaw GlobalTheory.Fam Matrix ValuativeRel IsLocalRing GlobalTheory.LocMod

namespace GlobalTheory.MiTop

section Prim

open GlobalTheory.FinPl

variable {D : D7} {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}

def TopPrim (v : VCom c) (o : TDat c k ι) : Prop :=
  ∀ n (h : n = D.R.m) x, x ∉ v.tP → ∀ a ∈ idAt D (· = x),
    a • ratV (vecB (c.oT n h) o.ζ₀) ∈ latV (c.X n) (c.x n).L (· = x) ↔ a ∈ intAt D (· = x)

variable {v : VCom c} {o : TDat c k ι}

theorem TopPrim.line (H : TopPrim v o) {n : ℕ} (h : n = D.R.m) {x : GlobalTheory.FinPl.Pl D} (hx : x ∉ v.tP) {LT : Lat c.T} {LZ : Lat c.Lz}
    (ho : OrthAt (c.oT n h) (c.x n).L LT LZ x) {a : AE D} (ha : a ∈ idAt D (· = x)) :
    a • ratV o.ζ₀ ∈ latV c.Lz LZ (· = x) ↔ a ∈ intAt D (· = x) :=
  (GlobalTheory.GoodPos.orth_line _ ho _ a).trans (H n h x hx a ha)

end Prim

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word} (f : FamCh W u)
  (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))

def PlacedPrim : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (ι : Type)
    (v : VCom f.c) (o : TDat f.c k ι) (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (pk W).Pg),
    f.c.Is ∧ v.Is ∧ VTie f v ∧ ShapeOff v o ∧ GPin G ∧ GRead f G pl ∧ BotTie f B v o G ∧ TopPrim v o

def InPosition : Prop := PlacedPrim f B ∧ Framed B

variable {f B}

theorem PlacedPrim.placed (h : PlacedPrim f B) : Placed f B := by
  obtain ⟨k, i1, i2, i3, i4, ι, v, o, n, G, pl, h1, h2, h3, h4, h5, h6, h7, -⟩ := h
  exact ⟨k, i1, i2, i3, i4, ι, v, o, n, G, pl, h1, h2, h3, h4, h5, h6, h7⟩

theorem InPosition.placed (h : InPosition f B) : Placed f B := h.1.placed

end GlobalTheory.MiTop

end
