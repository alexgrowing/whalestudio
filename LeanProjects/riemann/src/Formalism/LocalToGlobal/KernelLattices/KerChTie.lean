import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Gen

variable {X : Fields} {Pr : Primes X} {m : ℕ}

def OffG (Pr : Primes X) (v : HeightOneSpectrum (𝓞 X.E)) : Prop := ∀ i, ((Pr.g i : ℕ) : 𝓞 X.E) ∉ v.asIdeal

def MuValTie (Ch : Chars X Pr m) (G : ChGlob X m) : Prop :=
  ∀ (j : Fin m) (v : HeightOneSpectrum (𝓞 X.E)), OffG Pr v → G.σ₀ ((Ch.muVal j v : X.Kˣ) : X.K) = (((G.mu0 j).val v : ℂˣ) : ℂ)

end Gen

def MuValueOfCompatibleData : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (m : ℕ) (Ch : Chars X Pr m) (G : ChGlob X m) (e : Fin m → X.Tau → ℚ) (eta : Formalism.L2.Host.HChar X.E),
    Ch.Tied G.σ₀ e G.mu0 eta → MuValTie Ch G

def MuValRigid : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (m : ℕ) (Ch Ch' : Chars X Pr m) (G : ChGlob X m), MuValTie Ch G → MuValTie Ch' G →
    ∀ (j : Fin m) (v : HeightOneSpectrum (𝓞 X.E)), OffG Pr v → Ch.muVal j v = Ch'.muVal j v

def MuValOne : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (m : ℕ) (Ch : Chars X Pr m) (G : ChGlob X m), (∀ j, G.mu0 j = 1) →
    (MuValTie Ch G ↔ ∀ (j : Fin m) (v : HeightOneSpectrum (𝓞 X.E)), OffG Pr v → Ch.muVal j v = 1)

section Mem

variable {D : D7} {u : D.what₂.Word}

def MemLatAt (O : GL3Theta.LiftObj D (D.mem u).C) (π : 𝓞 D.host.E) : Prop :=
  letI := D.host.cmStar
  ∀ i, i ≤ D.R.m → ∃ co : (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E),
    (∀ x y, stdH D.host.E (D.R.N i) (co x) (co y) = (D.sp.X i).hT x y) ∧
    (∀ y, co y ∈ (O.L0 i).1 ↔ y ∈ (D.sp.X i).L0) ∧
    ∀ (c : (D.mem u).C.cls i) y, co y ∈ (O.lat i c).1 ↔
      ∃ a ∈ D.clsLat u i c, ∃ b ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X i).hT (D.clsLat u i c),
        y = a + D.host.conj (π : D.host.E) • b

def IsMemAt (O : GL3Theta.LiftObj D (D.mem u).C) (π : 𝓞 D.host.E) : Prop :=
  O.mt = D.muTil ∧ (∀ i c, O.dt i c = D.detCls u i c) ∧ MemLatAt O π

end Mem

def IsMemIff : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (O : GL3Theta.LiftObj D (D.mem u).C),
    O.IsMem ↔ ∃ π : 𝓞 D.host.E, (π : D.host.E) ∈ D.host.K ∧
      (π : D.host.E) * D.host.conj (π : D.host.E) = ((D.mem u).A.T : D.host.E) ∧ IsMemAt O π

section Comparison₂

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

def KerEntTied.PiSide {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop :=
  ∀ u, t.seam.iE ((t.Pr.piT (t.word u) : 𝓞 t.X.E) : t.X.E) = ((ex.errX.piT u : 𝓞 D.host.E) : D.host.E)

def KerEntTied.memObj {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) (u : D.what₂.Word) : GL3Theta.LiftObj D (D.mem u).C :=
  D.memberColumns_twistedChain_base u ▸ t.O u D.what₂.mu0

def KerEntTied.MemSide {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop :=
  ∀ u, (t.memObj u).IsMem → IsMemAt (t.memObj u) (ex.errX.piT u)

structure KerEntTied.ChTie {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop where

  ch_ok : t.Ch.Ok

  muVal : MuValTie t.Ch t.glob

  piT : t.PiSide

  mem : t.MemSide

def InUse (D : D7) (μ : D.what₂.Tup) : Prop := μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w

end Comparison₂

def PiSideVT : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.PiSide → ∀ u (P : HeightOneSpectrum (𝓞 t.X.E)),
      P ∈ t.Pr.vT (t.word u) ↔ ∃ y ∈ P.asIdeal, t.seam.iE ((y : 𝓞 t.X.E) : t.X.E) = ((ex.errX.piT u : 𝓞 D.host.E) : D.host.E)

def PiSideNeConj : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.PiSide → ∀ u,
      t.seam.iE ((t.X.conjO (t.Pr.piT (t.word u)) : 𝓞 t.X.E) : t.X.E) ≠ ((ex.errX.piT u : 𝓞 D.host.E) : D.host.E)

def PiSideEmb : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex),
      (t.PiSide → ∀ u τ, t.seam.σ₀ (t.X.emb τ ((t.Pr.piT (t.word u) : 𝓞 t.X.E) : t.X.E)) =
        TaylorLogMetric.embT D (t.seam.iT τ) ((ex.errX.piT u : 𝓞 D.host.E) : D.host.E)) ∧
      ∀ τ, (∀ u, t.seam.σ₀ (t.X.emb τ ((t.Pr.piT (t.word u) : 𝓞 t.X.E) : t.X.E)) =
        TaylorLogMetric.embT D (t.seam.iT τ) ((ex.errX.piT u : 𝓞 D.host.E) : D.host.E)) → t.PiSide

def QOffG : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex) (μ : D.what₂.Tup), InUse D μ →
      ∀ P ∈ QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K), OffG t.Pr P

def MuqAtQ : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), MuValTie t.Ch t.glob → ∀ (μ : D.what₂.Tup), InUse D μ →
      ∀ (i : ℕ) (h : i < D.R.m) (P : rowSG t.Pr t.sel (t.tup μ)), P.1 ∉ t.Pr.vGs →
        t.glob.σ₀ ((t.cst μ).muq (i + 1) P) =
          (((t.glob.mu0 ⟨i, h⟩).val P.1 : ℂˣ) : ℂ)⁻¹ * t.glob.σ₀ ((((qValC (t.tup μ : Chr t.X.F t.X.E t.X.K) P.1)⁻¹ : t.X.Kˣ)) : t.X.K)

def MuqAtQLoc : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), MuValTie t.Ch t.glob → ∀ (μ : D.what₂.Tup), InUse D μ →
      ∀ (i : ℕ) (h : i < D.R.m) (P : rowSG t.Pr t.sel (t.tup μ)), P.1 ∉ t.Pr.vGs → (t.glob.mu0 ⟨i, h⟩).UnrAt P.1 →
        ((qOf P.1 : ℕ) : 𝓞 t.X.E) ∉ P.1.asIdeal ^ 2 → ∀ qu : t.X.Eˣ, (qu : t.X.E) = (qOf P.1 : t.X.E) →
          t.glob.σ₀ ((t.cst μ).muq (i + 1) P) =
            (((t.glob.mu0 ⟨i, h⟩).locK P.1 qu : ℂˣ) : ℂ)⁻¹ * t.glob.σ₀ ((((qValC (t.tup μ : Chr t.X.F t.X.E t.X.K) P.1)⁻¹ : t.X.Kˣ)) : t.X.K)

end Formalism.L2.Ker
