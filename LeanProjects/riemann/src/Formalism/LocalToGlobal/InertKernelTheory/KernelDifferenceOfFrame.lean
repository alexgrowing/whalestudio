import Formalism.LocalToGlobal.InertKernelTheory.SecondKernelEntrywiseLastLevel

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.SecondKernelDifference

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.KerInert.K2 Formalism.L2.KerInert.SecondKernelInstances

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc0 : G.Consts} {Dx : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc0 Dx cX}

def entQ (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (c : (D.chTw u μ).cls i)
    (Q : MvPolynomial (GL3Theta.FrV D (D.R.N i)) ℂ) : (D.chTw u μ).cls (i + 1) → (D.chTw u μ).Y (i + 1) → ℂ :=
  fun c' y' =>
    (((GL3Theta.rhoOf D (t.O u μ).mt i ((t.O u μ).dt i c) : ℂˣ) : ℂ) *
        ((GL3Theta.rhoOf' D (t.O u μ).mt i ((t.O u μ).dt (i + 1) c') : ℂˣ) : ℂ)) *
      ((∏ τ, ((D.chTw u μ).de (i + 1) y' τ) ^ ((D.chTw u μ).sDiv i τ))⁻¹ *
        GL3Theta.applyAt0 D (GL3Theta.polD D (t.O u μ).dgen Q ((t.O u μ).frm (i + 1) y'))
          ((t.rd u μ).Th t.seam t.amb i c c'))

def FrPolyInj : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (O : GL3Theta.LiftObj D C) (i : ℕ), i ≤ D.R.m →
    Function.Injective (frPoly O i)

def EntRecQ : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (t : KerEntTied ex) (Tw : TwForms D) (u : D.what₂.Word)
    (μ : D.what₂.Tup) (i : ℕ), i ≤ D.R.m → ∀ (x : ((Tw.fm u μ).lat i).V) Q, SharpQ t Tw u μ i x Q →
      ∀ c, entRec t Tw u μ i c x = entQ t u μ i c (Q c)

def KernelDifferenceRationalAtLevel {p : ℕ} [Fact p.Prime] {X : Sys p} {Y : Pend X} (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    {σ : D.what₂.LL →+* X.G.Kf} (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j)
    (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j) (ι : ℂ →+* Y.Kc)
    (Rd : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup →
      ((D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc)
    (Sr : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Y.Kc) (j : ℕ) (cK : Y.Kc) : Prop :=
  ∀ La ∈ Y.Rep j, ∀ (x : ((ex.tw.fm u μ).lat j).V) Q, SharpQ t ex.tw u μ j x Q →
    ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
      Rd j c' L' (entQ t u μ j (cls j La.1 La.2) (Q (cls j La.1 La.2))) =
        cK • Y.DelF j (cmp j x La.1 La.2) (Sr j La (c', L'))

def KernelDifferenceIffRational : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (p : ℕ) [Fact p.Prime] (X : Sys p) (Y : Pend X) (σ : D.what₂.LL →+* X.G.Kf)
    (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j) (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j)
    (ι : ℂ →+* Y.Kc)
    (Rd : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup →
      ((D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc)
    (Sr : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Y.Kc) (j : ℕ) (cK : Y.Kc),
    j ≤ D.R.m → FormsSharpAt t u μ j →
      (KernelDifferenceAtLevel (Y := Y) t u μ cls cmp ι Rd Sr j cK ↔ KernelDifferenceRationalAtLevel (Y := Y) t u μ cls cmp ι Rd Sr j cK)

section Frame

open MvPolynomial

def polDY (D : D7) {N N' : ℕ} (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ) :
    MvPolynomial (GL3Theta.Idx D N N') (MvPolynomial (GL3Theta.FrV D N') ℂ) :=
  aeval (fun k : GL3Theta.FrV D N => ∑ b : Fin N',
    C (C (s k.1) * (if h : (k.2.2 : ℕ) < N' then (X (k.1, b, ⟨k.2.2, h⟩) : MvPolynomial (GL3Theta.FrV D N') ℂ) else 0)) *
      X ((k.1, b, k.2.1) : GL3Theta.Idx D N N')) Q

def framePol (D : D7) {N N' : ℕ} (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ) (G : TaylorLogMetric.VC D N N' → ℂ) :
    MvPolynomial (GL3Theta.FrV D N') ℂ :=
  ∑ α ∈ (polDY D s Q (N' := N')).support,
    coeff α (polDY D s Q) * C ((α.prod fun _ n => (n.factorial : ℂ)) * TaylorLogMetric.taylor D G α)

end Frame

def ApplyFrame : Prop :=
  ∀ (D : D7) (N N' : ℕ) (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ) (G : TaylorLogMetric.VC D N N' → ℂ)
    (y' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ),
    GL3Theta.applyAt0 D (GL3Theta.polD D s Q y') G = GL3Theta.evFr D (framePol D s Q G) y'

def EntQFrame : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ)
    (c : (D.chTw u μ).cls i) (Q : MvPolynomial (GL3Theta.FrV D (D.R.N i)) ℂ) (c' : (D.chTw u μ).cls (i + 1))
    (y' : (D.chTw u μ).Y (i + 1)),
    entQ t u μ i c Q c' y' =
      (((GL3Theta.rhoOf D (t.O u μ).mt i ((t.O u μ).dt i c) : ℂˣ) : ℂ) *
          ((GL3Theta.rhoOf' D (t.O u μ).mt i ((t.O u μ).dt (i + 1) c') : ℂˣ) : ℂ)) *
        ((∏ τ, ((D.chTw u μ).de (i + 1) y' τ) ^ ((D.chTw u μ).sDiv i τ))⁻¹ *
          frPoly (t.O u μ) (i + 1) (framePol D (t.O u μ).dgen Q ((t.rd u μ).Th t.seam t.amb i c c')) y')

def RdFrameAt {p : ℕ} [Fact p.Prime] {X : Sys p} {Y : Pend X} (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    {ι : ℂ →+* Y.Kc}
    (Rd : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup →
      ((D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc)
    (κ : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → (D.chTw u μ).cls (j + 1))
    (ΦR : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ →
      XspC (X.Pj (j + 1)) Y.Kc) (j : ℕ) : Prop :=
  ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
    ∀ P : (D.chTw u μ).cls (j + 1) → MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ,
      Rd j c' L' (fun c'' y' => (∏ τ, ((D.chTw u μ).de (j + 1) y' τ) ^ ((D.chTw u μ).sDiv j τ))⁻¹ *
          frPoly (t.O u μ) (j + 1) (P c'') y') = ΦR j c' L' (P (κ j c' L'))

def DelPolAt {p : ℕ} [Fact p.Prime] {X : Sys p} {Y : Pend X} (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    {σ : D.what₂.LL →+* X.G.Kf} (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j)
    (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j)
    (κ : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → (D.chTw u μ).cls (j + 1))
    (ΦR : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ →
      XspC (X.Pj (j + 1)) Y.Kc)
    (Sr : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Y.Kc) (j : ℕ) (cK : Y.Kc) : Prop :=
  ∀ La ∈ Y.Rep j, ∀ (x : ((ex.tw.fm u μ).lat j).V) Q, SharpQ t ex.tw u μ j x Q →
    ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
      ΦR j c' L' ((((GL3Theta.rhoOf D (t.O u μ).mt j ((t.O u μ).dt j (cls j La.1 La.2)) : ℂˣ) : ℂ) *
          ((GL3Theta.rhoOf' D (t.O u μ).mt j ((t.O u μ).dt (j + 1) (κ j c' L')) : ℂˣ) : ℂ)) •
          framePol D (t.O u μ).dgen (Q (cls j La.1 La.2))
            ((t.rd u μ).Th t.seam t.amb j (cls j La.1 La.2) (κ j c' L'))) =
        cK • Y.DelF j (cmp j x La.1 La.2) (Sr j La (c', L'))

def KernelDifferenceOfFrame : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (p : ℕ) [Fact p.Prime] (X : Sys p) (Y : Pend X) (σ : D.what₂.LL →+* X.G.Kf)
    (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j) (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j)
    (ι : ℂ →+* Y.Kc)
    (Rd : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup →
      ((D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc)
    (Sr : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Y.Kc)
    (κ : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → (D.chTw u μ).cls (j + 1))
    (ΦR : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ →
      XspC (X.Pj (j + 1)) Y.Kc) (j : ℕ) (cK : Y.Kc),
    j ≤ D.R.m → FormsSharpAt t u μ j → RdFrameAt (Y := Y) t u μ Rd κ ΦR j →
      DelPolAt (Y := Y) t u μ cls cmp κ ΦR Sr j cK → KernelDifferenceAtLevel (Y := Y) t u μ cls cmp ι Rd Sr j cK

end Formalism.L2.KerInert.SecondKernelDifference
