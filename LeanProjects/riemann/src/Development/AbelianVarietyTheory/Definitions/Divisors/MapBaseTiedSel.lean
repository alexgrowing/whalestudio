import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ColumnCompatibleSelection
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
import Formalism.LocalToGlobal.IndefiniteReal.NonzeroIndexPlaceIndepConstants

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.EX GlobalTheory.EX.OB

namespace GlobalTheory.Fc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Point

variable {D : D7} {O : Obj D} {c : ℝ}

def Bundle.TiePins (b : Bundle D O c) (Rr : RealRec b.B.Q) : Prop :=
  PsiPPTie D b.P.P0 b.P.ψ0 b.P.Ps b.P.ψs b.P.I.eG ∧ RealPins3 b.B.Q ∧ ∃ pins : RealPins b.B.Q, RealRecPins pins Rr

abbrev Bundle.Comparison₂ (b : Bundle D O c) : Type 1 := {Rr : RealRec b.B.Q // b.TiePins Rr}

abbrev Bundle.mkTie (b : Bundle D O c) (Rr : RealRec b.B.Q) (psi : PsiPPTie D b.P.P0 b.P.ψ0 b.P.Ps b.P.ψs b.P.I.eG)
    (pins : RealPins b.B.Q) (pins3 : RealPins3 b.B.Q) (recPins : RealRecPins pins Rr) : b.Comparison₂ :=
  ⟨Rr, psi, pins3, pins, recPins⟩

theorem Bundle.Comparison₂.psi {b : Bundle D O c} (t : b.Comparison₂) : PsiPPTie D b.P.P0 b.P.ψ0 b.P.Ps b.P.ψs b.P.I.eG := t.2.1

theorem Bundle.Comparison₂.pins3 {b : Bundle D O c} (t : b.Comparison₂) : RealPins3 b.B.Q := t.2.2.1

theorem Bundle.Comparison₂.pins {b : Bundle D O c} (t : b.Comparison₂) : RealPins b.B.Q := let ⟨h, _⟩ := t.2.2.2; h

theorem Bundle.Comparison₂.recPins {b : Bundle D O c} (t : b.Comparison₂) : RealRecPins t.pins t.1 := let ⟨_, h⟩ := t.2.2.2; h

@[reducible] def Bundle.part (b : Bundle D O c) (t : b.Comparison₂) : Ind.Part D O c where
  R := b.R
  S := b.S
  P := b.P
  pin := b.pin
  DH := b.DH
  Dcf := b.C.c.face
  Spf := b.C.Sp
  ok1 := b.C.ok1
  B := b.B
  Rr := t.1
  psi := t.psi
  pins := t.pins
  muDef := t.pins3.muDef
  recPins := t.recPins

theorem zsc_eq_ind (P : RowSideFamily O.ex) (Del h0 : ℕ) (c : ℝ) : Ind.zsc P Del h0 c = zsc P Del h0 c := rfl

theorem exists_part_eq (p : Ind.Part D O c) (C : GlobalTheory.Cp.SquareIntegrableColumnsCompatible p.R.T p.P) (hD : p.Dcf = C.c.face) (hS : HEq p.Spf C.Sp) :
    ∃ (b : Bundle D O c) (t : b.Comparison₂), b.part t = p := by
  revert C
  obtain ⟨R, S, P, pin, DH, Dcf, Spf, ok1, B, Rr, psi, pins, muDef, recPins⟩ := p
  show ∀ C : GlobalTheory.Cp.SquareIntegrableColumnsCompatible R.T P, Dcf = C.c.face → HEq Spf C.Sp → _
  intro C hD hS
  subst hD
  obtain rfl := eq_of_heq hS
  exact ⟨⟨R, S, P, pin, DH, C, B⟩, ⟨Rr, psi, ⟨muDef⟩, pins, recPins⟩, rfl⟩

example (b : Bundle D O c) (t : b.Comparison₂) : (b.part t).B = b.B := rfl

example (b : Bundle D O c) (t : b.Comparison₂) : (b.part t).P = b.P := rfl

example (b : Bundle D O c) (t : b.Comparison₂) : (b.part t).Rr = t.1 := rfl

example (b : Bundle D O c) (t : b.Comparison₂) : Ind.PRB D O c (b.part t) ↔ RowsB b.B := Iff.rfl

example (b : Bundle D O c) (t : b.Comparison₂) : (b.part t).pt.R = b.B.Q.Rl := rfl

end Point

def HasTie : BdP Bundle := fun _ _ _ b => Nonempty b.Comparison₂

abbrev TiedBundle : BdT := fun D O c => Σ b : Bundle D O c, b.Comparison₂

abbrev TiedBundle.base : ∀ D O c, TiedBundle D O c → Bundle D O c := fun _ _ _ b => b.1

abbrev TiedBundle.part : ∀ D O c, TiedBundle D O c → Ind.Part D O c := fun _ _ _ b => b.1.part b.2

abbrev LkT.onTied (Lk : LkT Bundle) : LkT TiedBundle := fun K β c b => Lk K β c b.1

section Sel

variable {𝒜 : FamClass}

abbrev TieSel (σ : RawSel Bundle 𝒜) : Type 1 :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), (σ Fm hc x hx i).Comparison₂

def compatibleSelection (σ : RawSel Bundle 𝒜) (τ : TieSel σ) : RawSel TiedBundle 𝒜 :=
  fun Fm hc x hx i => ⟨σ Fm hc x hx i, τ Fm hc x hx i⟩

def partSel (σ : RawSel Bundle 𝒜) (τ : TieSel σ) : RawSel Ind.Part 𝒜 :=
  fun Fm hc x hx i => (σ Fm hc x hx i).part (τ Fm hc x hx i)

def tieSelOf {σ : RawSel Bundle 𝒜} (h : AtAll HasTie 𝒜 σ) : TieSel σ :=
  fun Fm hc x hx i => Classical.choice (h Fm hc x hx i)

theorem map_base_tiedSel (σ : RawSel Bundle 𝒜) (τ : TieSel σ) :
    (RawSel.map TiedBundle.base (compatibleSelection σ τ) : RawSel Bundle 𝒜) = @σ := rfl

theorem map_part_tiedSel (σ : RawSel Bundle 𝒜) (τ : TieSel σ) :
    (RawSel.map TiedBundle.part (compatibleSelection σ τ) : RawSel Ind.Part 𝒜) = @partSel 𝒜 σ τ := rfl

end Sel

section Construction₂

open GlobalTheory.Mem GlobalTheory.Mem.Top

variable {Q Q' : V4.Slot} {Lk : LkT Bundle}

theorem Row.of_tied {Lk' : LkT TiedBundle} (hQ : ∀ K X f T c, Q K X f T c → Q' K X f T c)
    (hL : EvP fun _ K => ∀ β : BPt K, β.Is Q → ∀ (c : ℝ) (b : Bundle β.D β.O c), Lk K β c b → ∃ t : b.Comparison₂, Lk' K β c ⟨b, t⟩)
    {H : ∀ 𝒜 : FamClass, RawSel TiedBundle 𝒜 → Prop} (h : Row Q' Lk' H) :
    Row Q Lk fun 𝒜 σ => ∃ τ : TieSel σ, H 𝒜 (compatibleSelection σ τ) := by
  obtain ⟨E, e, h⟩ := h
  refine ⟨fun κ D O c b => ∃ t : b.Comparison₂, Built Q' Lk' κ D O c ⟨b, t⟩ ∧ E κ D O c ⟨b, t⟩,
    (EvP.and hL e).mono fun κ K hk H β hq c b hl => ?_, fun 𝒜 σ s => ?_⟩
  · obtain ⟨t, ht⟩ := H.1 β hq c b hl
    exact ⟨t, Built.intro hk (hQ _ _ _ _ _ hq) ht, H.2 β (hQ _ _ _ _ _ hq) c _ ht⟩
  · choose κ h1 h2 h3 using @s
    choose τ h4 using fun (eps : ℝ) (Fm : FamP eps) (hc : 𝒜 Fm) x hx i => (h3 Fm hc x hx i).2
    exact ⟨fun Fm hc => τ _ Fm hc, h 𝒜 _ fun Fm hc => ⟨κ Fm hc, h1 Fm hc, h2 Fm hc, h4 _ Fm hc⟩⟩

theorem Row.descend {Lk' : LkT TiedBundle} (hQ : ∀ K X f T c, Q K X f T c → Q' K X f T c)
    (hL : EvP fun _ K => ∀ β : BPt K, β.Is Q → ∀ (c : ℝ) (b : Bundle β.D β.O c), Lk K β c b → ∃ t : b.Comparison₂, Lk' K β c ⟨b, t⟩)
    {H : ∀ 𝒜 : FamClass, RawSel Bundle 𝒜 → Prop} (h : Row Q' Lk' fun 𝒜 σ => H 𝒜 (RawSel.map TiedBundle.base σ)) :
    Row Q Lk H :=
  (Row.of_tied hQ hL h).imp fun _ _ _ H => let ⟨_, t⟩ := H; t

theorem Row.of_part {Lk' : LkT Ind.Part} (hQ : ∀ K X f T c, Q K X f T c → Q' K X f T c)
    (hL : EvP fun _ K => ∀ β : BPt K, β.Is Q → ∀ (c : ℝ) (b : Bundle β.D β.O c), Lk K β c b → ∃ t : b.Comparison₂, Lk' K β c (b.part t))
    {H : ∀ 𝒜 : FamClass, RawSel Ind.Part 𝒜 → Prop} (h : Row Q' Lk' H) :
    Row Q Lk fun 𝒜 σ => ∃ τ : TieSel σ, H 𝒜 (partSel σ τ) :=
  Row.of_tied (Lk' := fun K β c b => Lk' K β c (TiedBundle.part _ _ c b)) hQ hL
    (H := fun 𝒜 σ => H 𝒜 (RawSel.map TiedBundle.part σ))
    (Row.map (Bd := TiedBundle) TiedBundle.part (fun _ _ _ _ _ t => t) (fun _ _ _ _ _ t => t) h)

theorem Row.onTied {H : ∀ 𝒜 : FamClass, RawSel Bundle 𝒜 → Prop} (h : Row Q Lk H) :
    Row Q Lk.onTied fun 𝒜 σ => H 𝒜 (RawSel.map TiedBundle.base σ) :=
  Row.map (Bd := TiedBundle) TiedBundle.base (fun _ _ _ _ _ t => t) (fun _ _ _ _ _ t => t) h

theorem Row.of_onTied (hT : RowE Q Lk fun _ => HasTie) {H : ∀ 𝒜 : FamClass, RawSel Bundle 𝒜 → Prop}
    (h : Row Q Lk.onTied fun 𝒜 σ => H 𝒜 (RawSel.map TiedBundle.base σ)) : Row Q Lk H :=
  Row.descend (fun _ _ _ _ _ t => t)
    (EvP.mono (fun _ _ _ H β hq c b hl => let ⟨t⟩ := H β hq c b hl; ⟨t, hl⟩) hT) h

end Construction₂

end GlobalTheory.Fc

end
