import Formalism.SharpRestriction.GrowthBounds.ChartComparison

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms

namespace Formalism.L2.KerInert.SecondKernelStabilizers

def StabEqFor {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
    {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}
    (cls : ∀ j, Lv.comp j → (Fl.Pj j).Tup → (D.chTw u μ).cls j) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ (a : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    Nat.card ((D.chTw u μ).stab j (cls j a L)) = Nat.card {γ : (Lv.lev j a).Γ // (Lv.lev j a).smul γ L = L}

def Level.dbl {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {P : Places p O Kf} (C : Level P) : Level P where
  Γ := C.Γ × Multiplicative (ZMod 2)
  act v := (C.act v).comp (MonoidHom.fst _ _)
  χ := C.χ.comp (MonoidHom.fst _ _)

def LabStabEq : Prop :=
  ∀ (D : D7) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Fl : Fills (D.gat u w h)) (Lv : Levels Fl)
    (K : CmpJ.KerLabelsMu Tw u μ w h Lv), StabEqFor K.cls

def RelabelCls : Prop :=
  ∀ (D : D7) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Fl : Fills (D.gat u w h)) (Lv : Levels Fl)
    (K : CmpJ.KerLabelsMu Tw u μ w h Lv) (σ : ∀ j, Equiv.Perm ((D.chTw u μ).cls j)),
    (∀ j, j ≤ D.R.m → ∀ (a a' : Lv.comp j) (L L' : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L → (Fl.Pj j).IsLatTup L' →
      (σ j (K.cls j a L) = σ j (K.cls j a' L') ↔ a = a' ∧ ∃ γ : (Lv.lev j a).Γ, L' = (Lv.lev j a).smul γ L)) ∧
    (∀ j, j ≤ D.R.m → ∀ x : (D.chTw u μ).cls j, ∃ a L, (Fl.Pj j).IsLatTup L ∧ σ j (K.cls j a L) = x) ∧
    (StabEqFor (fun j a L => σ j (K.cls j a L)) ↔
      ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ x, Nat.card ((D.chTw u μ).stab j (σ j x)) = Nat.card ((D.chTw u μ).stab j x))

def RelabelAll : Prop :=
  ∀ (D : D7) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Fl : Fills (D.gat u w h)) (Lv : Levels Fl)
    (K : CmpJ.KerLabelsMu Tw u μ w h Lv),
    (∀ σ : ∀ j, Equiv.Perm ((D.chTw u μ).cls j), StabEqFor (fun j a L => σ j (K.cls j a L))) →
      ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ x y : (D.chTw u μ).cls j,
        Nat.card ((D.chTw u μ).stab j x) = Nat.card ((D.chTw u μ).stab j y)

def DblLevel : Prop :=
  ∀ (p : ℕ) (O Kf : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (P : Places p O Kf) (C : Level P),
    (∀ (g : (Level.dbl C).Γ) (L : P.Tup), (Level.dbl C).smul g L = C.smul g.1 L) ∧
    (∀ L L' : P.Tup, (∃ g : (Level.dbl C).Γ, L' = (Level.dbl C).smul g L) ↔ ∃ γ : C.Γ, L' = C.smul γ L) ∧
    (∀ Hv : P.Tup → Submodule O P.Xsp, (Level.dbl C).funMod Hv = C.funMod Hv) ∧
    ∀ L : P.Tup, Nat.card {g : (Level.dbl C).Γ // (Level.dbl C).smul g L = L} =
      2 * Nat.card {γ : C.Γ // C.smul γ L = L}

end Formalism.L2.KerInert.SecondKernelStabilizers
