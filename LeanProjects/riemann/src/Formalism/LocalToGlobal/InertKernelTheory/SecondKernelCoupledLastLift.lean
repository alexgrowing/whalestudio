import Formalism.LocalToGlobal.InertKernelTheory.SecondKernelEntrywiseLastLevel

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.SecondKernelCoupled

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.KerInert.K2 Formalism.L2.KerInert.SecondKernelInstances

section Gen

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc0 : G.Consts} {Dx : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc0 Dx cX}
variable {p : ℕ} [Fact p.Prime] {X : Sys p} (Y : Pend X)
variable (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)

def LatC (j : ℕ) (lp : (D.chTw u μ).cls j → X.Lt j) : Prop :=
  ∀ x, (X.Pj j).IsLatTup (lp x).2

def DegreeCompatibilityAtLevel (j : ℕ) : Prop :=
  ∀ x : (D.chTw u μ).cls j, padicValNat p (Nat.card ((D.chTw u μ).stab j x)) ≤ X.dG j

def TieSerC (Sr : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Y.Kc) (j : ℕ) (lp : (D.chTw u μ).cls j → X.Lt j) :
    Prop :=
  ∀ (x : (D.chTw u μ).cls j) (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
    Y.ThF j (lp x) (c', L') = ((Y.eS j (lp x) * (Y.eT j (c', L'))⁻¹)⁻¹ : X.G.Kf) • Sr j (lp x) (c', L')

def KernelDifferenceWithConstant {σ : D.what₂.LL →+* X.G.Kf} (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j) (ι : ℂ →+* Y.Kc)
    (Rd : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup →
      ((D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc)
    (Sr : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Y.Kc) (j : ℕ) (lp : (D.chTw u μ).cls j → X.Lt j) (cK : Y.Kc) :
    Prop :=
  ∀ (x : (D.chTw u μ).cls j) (y : ((ex.tw.fm u μ).lat j).V) (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup),
    (X.Pj (j + 1)).IsLatTup L' →
      Rd j c' L' (entRec t ex.tw u μ j x y) = cK • Y.DelF j (cmp j y (lp x).1 (lp x).2) (Sr j (lp x) (c', L'))

def HeckeC (j : ℕ) (lp : (D.chTw u μ).cls j → X.Lt j) : Prop :=
  ∀ (v : X.Pl) (i : ℕ), ∀ F ∈ X.FQ j, ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    ∑ x : (D.chTw u μ).cls j, (((Nat.card ((D.chTw u μ).stab j x) : ℕ) : Y.Kc))⁻¹ •
        ∑ᶠ (L1 : Submodule ((X.Pj j).W (X.vJ j v)) (Fin ((X.Pj j).m + 1) → (X.Pj j).Qq (X.vJ j v)))
          (_ : IsEdge p ((X.Pj j).n' (X.vJ j v)) i ⟨(lp x).2 (X.vJ j v), L1⟩),
          Y.ker j ((lp x).1, Function.update (lp x).2 (X.vJ j v) L1) La' (F (lp x).1 (lp x).2) =
      ∑ x : (D.chTw u μ).cls j, (((Nat.card ((D.chTw u μ).stab j x) : ℕ) : Y.Kc))⁻¹ •
        Y.ker j (lp x) La' (X.Tm v i j F (lp x).1 (lp x).2)

def TiesC {σ : D.what₂.LL →+* X.G.Kf} (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j) (ι : ℂ →+* Y.Kc)
    (Rd : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup →
      ((D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc)
    (Sr : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Y.Kc) (j : ℕ) (lp : (D.chTw u μ).cls j → X.Lt j) : Prop :=
  FormsSharpAt t u μ j ∧ TieReadAt (Y := Y) u μ cmp ι Rd j ∧ LatC u μ j lp ∧ DegreeCompatibilityAtLevel (X := X) u μ j ∧ TieSerC Y u μ Sr j lp ∧
    ∃ cK : Y.Kc, cK ∈ Y.Oc ∧ cK⁻¹ ∈ Y.Oc ∧ cK ≠ 0 ∧ KernelDifferenceWithConstant Y t u μ cmp ι Rd Sr j lp cK

def SecC (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j) (j : ℕ) (lp : (D.chTw u μ).cls j → X.Lt j) : Prop :=
  ∀ x, lp x ∈ Y.Rep j ∧ cls j (lp x).1 (lp x).2 = x

end Gen

def SecondKernelCoupledLastLift : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl) (Ch : Chain Lv) (KA : TwTie.KerAtMu D ex.cmp ex.tw u μ w h Ch)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    (Y : Pend (sysAt Ch std vp unif eO eO_spec dG dG_spec om)) (ι : ℂ →+* Y.Kc) (Rd : _) (Sr : _)
    (lp : (D.chTw u μ).cls (D.R.m - 1) → (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (D.R.m - 1)),
    0 < D.R.m → TiesC Y t u μ KA.cmp ι Rd Sr (D.R.m - 1) lp → HeckeC Y u μ (D.R.m - 1) lp →
      ExpansionDecomposition D _ Y (D.R.m - 1)

def Adm4NewInst : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl) (Ch : Chain Lv) (KA : TwTie.KerAtMu D ex.cmp ex.tw u μ w h Ch)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    (Y : Pend (sysAt Ch std vp unif eO eO_spec dG dG_spec om)) (ι : ℂ →+* Y.Kc) (Rd : _) (Sr : _)
    (lp : (D.chTw u μ).cls (D.R.m - 1) → (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (D.R.m - 1)),
    (∀ j, j + 1 < D.R.m → TiesAt t u μ KA.cls KA.cmp ι Rd Sr j) →
    (0 < D.R.m → TiesC Y t u μ KA.cmp ι Rd Sr (D.R.m - 1) lp ∧ HeckeC Y u μ (D.R.m - 1) lp) →
      ArchimedeanSignatureMatching D _ Y

def HeckeCEntry : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl) (Ch : Chain Lv) (KA : TwTie.KerAtMu D ex.cmp ex.tw u μ w h Ch)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    (Y : Pend (sysAt Ch std vp unif eO eO_spec dG dG_spec om))
    (lp : (D.chTw u μ).cls (D.R.m - 1) → (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (D.R.m - 1)),
    0 < D.R.m → MinkowskiCounting D _ Y → SecC Y u μ KA.cls (D.R.m - 1) lp → TieStabAt (Y := Y) u μ KA.cls (D.R.m - 1) →
      HeckeC Y u μ (D.R.m - 1) lp

def TiesCOfAt : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl) (Ch : Chain Lv) (KA : TwTie.KerAtMu D ex.cmp ex.tw u μ w h Ch)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    (Y : Pend (sysAt Ch std vp unif eO eO_spec dG dG_spec om)) (ι : ℂ →+* Y.Kc) (Rd : _) (Sr : _)
    (lp : (D.chTw u μ).cls (D.R.m - 1) → (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (D.R.m - 1)),
    0 < D.R.m → SecC Y u μ KA.cls (D.R.m - 1) lp → TiesAt t u μ KA.cls KA.cmp ι Rd Sr (D.R.m - 1) →
      TiesC Y t u μ KA.cmp ι Rd Sr (D.R.m - 1) lp

def SecCEx : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl) (Ch : Chain Lv) (KA : TwTie.KerAtMu D ex.cmp ex.tw u μ w h Ch)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    (Y : Pend (sysAt Ch std vp unif eO eO_spec dG dG_spec om)),
    0 < D.R.m → ∃ lp, SecC Y u μ KA.cls (D.R.m - 1) lp

end Formalism.L2.KerInert.SecondKernelCoupled
