import Formalism.LocalToGlobal.KernelLattices.KerChTie

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mem

variable {D : D7} {u : D.what₂.Word}

def MemLatCo (O : GL3Theta.LiftObj D (D.mem u).C) (π : 𝓞 D.host.E) (i : ℕ) (co : (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)) : Prop :=
  letI := D.host.cmStar
  (∀ x y, stdH D.host.E (D.R.N i) (co x) (co y) = (D.sp.X i).hT x y) ∧
  (∀ y, co y ∈ (O.L0 i).1 ↔ y ∈ (D.sp.X i).L0) ∧
  ∀ (c : (D.mem u).C.cls i) y, co y ∈ (O.lat i c).1 ↔
    ∃ a ∈ D.clsLat u i c, ∃ b ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X i).hT (D.clsLat u i c),
      y = a + D.host.conj (π : D.host.E) • b

def MemLatOf (u : D.what₂.Word) (π : 𝓞 D.host.E) {ι : ℕ → Type} (e : ∀ i, ι i → (D.mem u).C.cls i)
    (lat : ∀ i, ι i → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) : Prop :=
  letI := D.host.cmStar
  ∀ i, i ≤ D.R.m → ∃ co : (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E),
    (∀ x y, stdH D.host.E (D.R.N i) (co x) (co y) = (D.sp.X i).hT x y) ∧
    (∀ y, (∀ k, IsIntegral ℤ (co y k)) ↔ y ∈ (D.sp.X i).L0) ∧
    ∀ (c : ι i) y, co y ∈ lat i c ↔
      ∃ a ∈ D.clsLat u i (e i c), ∃ b ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X i).hT (D.clsLat u i (e i c)),
        y = a + D.host.conj (π : D.host.E) • b

end Mem

def clsMu0 (D : D7) (u : D.what₂.Word) (i : ℕ) : (D.chTw u D.what₂.mu0).cls i ≃ (D.mem u).C.cls i :=
  Equiv.cast (congrArg (fun C : ColumnChain D.R D.what₂.Tau (D.hcW u) => C.cls i) (D.memberColumns_twistedChain_base u))

def MemLatAtIffCo : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (O : GL3Theta.LiftObj D (D.mem u).C) (π : 𝓞 D.host.E),
    MemLatAt O π ↔ ∀ i, i ≤ D.R.m → ∃ co, MemLatCo O π i co

def MemSideTest : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (O : GL3Theta.LiftObj D (D.mem u).C) (π π' : 𝓞 D.host.E) (i : ℕ)
    (co : (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)),
    D.host.conj (π : D.host.E) = (π' : D.host.E) → D.host.conj (π' : D.host.E) = (π : D.host.E) → IsCoprime π π' →
    MemLatCo O π i co → MemLatCo O π' i co →
      ∀ (c : (D.mem u).C.cls i) y, co y ∈ (O.lat i c).1 ↔ y ∈ (letI := D.host.cmStar; Formalism.HermitianLatticesTheory.dual (D.sp.X i).hT (D.clsLat u i c))

def MemRigid : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (O O' : GL3Theta.LiftObj D (D.mem u).C) (π : 𝓞 D.host.E), IsMemAt O π → IsMemAt O' π →
    O.mt = O'.mt ∧ (∀ i c, O.dt i c = O'.dt i c) ∧
    ∀ i, i ≤ D.R.m → ∃ γ : (Fin (D.R.N i) → D.host.E) ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E),
      (letI := D.host.cmStar; ∀ x y, stdH D.host.E (D.R.N i) (γ x) (γ y) = stdH D.host.E (D.R.N i) x y) ∧
      (∀ x, γ x ∈ (O'.L0 i).1 ↔ x ∈ (O.L0 i).1) ∧ ∀ c x, γ x ∈ (O'.lat i c).1 ↔ x ∈ (O.lat i c).1

section Comparison₂

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

def KerEntTied.MemSideU {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop :=
  ∀ u, IsMemAt (t.memObj u) (ex.errX.piT u)

def KerEntTied.MemSideCo {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex)
    (co : ∀ (_ : D.what₂.Word) i, i ≤ D.R.m → ((D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E))) : Prop :=
  ∀ u, (t.memObj u).mt = D.muTil ∧ (∀ i c, (t.memObj u).dt i c = D.detCls u i c) ∧
    ∀ i (hi : i ≤ D.R.m), MemLatCo (t.memObj u) (ex.errX.piT u) i (co u i hi)

def KerEntTied.ChrMu0 {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop :=
  ∀ u, (t.O u D.what₂.mu0).mt = D.muTil

def KerEntTied.DetMu0 {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop :=
  ∀ u i c, (t.O u D.what₂.mu0).dt i c = D.detCls u i (clsMu0 D u i c)

def KerEntTied.LatMu0 {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop :=
  ∀ u, MemLatOf u (ex.errX.piT u) (fun i => clsMu0 D u i) (fun i c => t.seam.lat ((t.rd u D.what₂.mu0).N i c))

end Comparison₂

def MemSideUIff : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.MemSideU ↔ t.MemSide ∧ ∀ u, (t.memObj u).IsMem

def MemSideIdle : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ u, ¬ (t.memObj u).IsMem) → t.MemSide

def MemSideUIffMu0 : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.MemSideU ↔ t.ChrMu0 ∧ t.DetMu0 ∧ t.LatMu0

end Formalism.L2.Ker
