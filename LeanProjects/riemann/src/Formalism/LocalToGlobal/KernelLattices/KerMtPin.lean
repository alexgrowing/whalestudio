import Formalism.LocalToGlobal.KernelLattices.KerMemPin

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def twMt (D : D7) (ξ : D.Dt →* ℂˣ) : ℕ → D.Dt →* ℂˣ := fun j =>
  if 1 ≤ j ∧ j ≤ D.R.m then D.muTil j * ξ else D.muTil j

section Comparison₂

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

def KerEntTied.IsUnitNormOneQuotient {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) (q : (AfE t.X.F t.X.E)ˣ →* D.Dt) : Prop :=
  Function.Surjective q ∧
  ∀ (k : t.X.Eˣ) (z : unitary D.host.E), (z : D.host.E) * D.host.conj (t.seam.iE (k : t.X.E)) = t.seam.iE (k : t.X.E) →
    q (ratId t.X.F t.X.E k) = D.e1Dt z

def KerEntTied.XiTil {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) (q : (AfE t.X.F t.X.E)ˣ →* D.Dt) (μ : D.what₂.Tup)
    (ξ : D.Dt →* ℂˣ) : Prop :=
  ∀ x, ξ (q x) = Units.map t.seam.σ₀.toMonoidHom ((t.tup μ : Chr t.X.F t.X.E t.X.K) x)

def KerEntTied.MtTwAt {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) (q : (AfE t.X.F t.X.E)ˣ →* D.Dt) (P : D.what₂.Tup → Prop) : Prop :=
  ∀ μ, μ ≠ D.what₂.mu0 → P μ → ∃ ξ : D.Dt →* ℂˣ, t.XiTil q μ ξ ∧ ∀ u, (t.O u μ).mt = twMt D ξ

def KerEntTied.MtTwOn {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) (P : D.what₂.Tup → Prop) : Prop :=
  ∃ q : (AfE t.X.F t.X.E)ˣ →* D.Dt, t.IsUnitNormOneQuotient q ∧ t.MtTwAt q P

def KerEntTied.MtTwTie {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop := t.MtTwOn fun _ => True

end Comparison₂

def XiTilUnique : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex) (q : (AfE t.X.F t.X.E)ˣ →* D.Dt) (μ : D.what₂.Tup) (ξ ξ' : D.Dt →* ℂˣ),
    t.IsUnitNormOneQuotient q → t.XiTil q μ ξ → t.XiTil q μ ξ' → ξ = ξ'

def XiTilFin : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex) (q : (AfE t.X.F t.X.E)ˣ →* D.Dt) (μ : D.what₂.Tup) (ξ : D.Dt →* ℂˣ),
    t.IsUnitNormOneQuotient q → t.XiTil q μ ξ → ∃ n : ℕ, 0 < n ∧ ∀ x, ξ x ^ n = 1

def XiTilRat : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex) (q : (AfE t.X.F t.X.E)ˣ →* D.Dt) (μ : D.what₂.Tup) (ξ : D.Dt →* ℂˣ),
    t.IsUnitNormOneQuotient q → t.XiTil q μ ξ → ∀ z : unitary D.host.E, ξ (D.e1Dt z) = 1

def RhoMul : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (C₀ C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (mt mt' : ℕ → D.Dt →* ℂˣ) (ξ : D.Dt →* ℂˣ),
    (∀ i < D.R.m, mt' (i + 1) = mt (i + 1) * ξ) → (∃ n : ℕ, 0 < n ∧ ∀ x, ξ x ^ n = 1) → (∀ z : unitary D.host.E, ξ (D.e1Dt z) = 1) →
    GL3Theta.rhoThreeOf D C₀ mt → GL3Theta.rhoThreeOf D C mt'

def RhoOfMtOn : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex) (P : D.what₂.Tup → Prop), t.ChrMu0 → t.MtTwOn P → GL3Theta.rhoThree D →
    ∀ u μ, (μ = D.what₂.mu0 ∨ P μ) → GL3Theta.rhoThreeOf D (D.chTw u μ) (t.O u μ).mt

def RhoOfMt : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.ChrMu0 → t.MtTwTie → GL3Theta.rhoThree D →
    ∀ u μ, GL3Theta.rhoThreeOf D (D.chTw u μ) (t.O u μ).mt

def TwMtOne : Prop := ∀ D : D7, twMt D 1 = D.muTil

def MtTwSees : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), 0 < D.R.m → t.MtTwTie → ∀ u μ, μ ≠ D.what₂.mu0 → (t.O u μ).mt = D.muTil →
    (t.tup μ : Chr t.X.F t.X.E t.X.K) = 1

def MtTwNoU : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.MtTwTie → ∀ u u' μ μ', μ ≠ D.what₂.mu0 → μ' ≠ D.what₂.mu0 → t.tup μ = t.tup μ' →
    (t.O u μ).mt = (t.O u' μ').mt

end Formalism.L2.Ker
