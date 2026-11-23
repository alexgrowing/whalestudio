import Mathlib
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalToGlobal.HermitianForms.TiedTwGen

noncomputable section

namespace GlobalTheory.KerJ

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms NumberField

def IsVal {ι Yv : Type} [Fintype ι] {n : ℕ} (fr : Yv → ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n) {k : Type} [Field k]
    (σ : k →+* ℂ) (f : Yv → ℂ) : Prop :=
  ∃ P ∈ Formalism.L2.DIV.VV k lam, f = evG fr (fun τ => (lam τ).detShift) σ P

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl K Y cX}

def VQTie (t : KerEntTied ex) : Prop :=
  ∀ u μ i, i ≤ D.R.m → ∀ (c : (D.chTw u μ).cls i) (f : (D.chTw u μ).Y i → ℂ),
    (∃ v : t.ent.VQ u μ i c, t.ent.ev u μ i c v = f) ↔ IsVal ((t.O u μ).frm i) (lamTG (ex.tw.fm u μ) i) D.what₂.embLL f

def JetLL (t : KerEntTied ex) : Prop :=
  ∀ u μ, DV.Used D μ → ∀ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1))
    (a : DVar D.what₂.Tau (D.R.N i) (D.R.N (i + 1)) →₀ ℕ),
    (∀ τ, (a.sum fun v n => open Classical in if v.1 = τ then n else 0) = ∑ r, nuT D u i τ r) →
    ∃ k : D.what₂.LL, D.what₂.embLL k =
      (D.chTw u μ).rhoDet i c * (D.chTw u μ).rhoDet' i c' * jetC (t.O u μ).dgen ((t.O u μ).Th i c c') a

end GlobalTheory.KerJ
