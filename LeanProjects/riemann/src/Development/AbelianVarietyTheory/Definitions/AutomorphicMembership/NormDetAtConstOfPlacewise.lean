import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal

namespace GlobalTheory.ShFam.Pad

def inclQb {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H}
    (c : Coeff l) : c.F →+* Qb :=
  c.F.val.toRingHom.codRestrict (algebraicClosure ℚ ℂ) fun a =>
    haveI := c.fin
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) a).algHom c.F.val)

open Classical in

def carry {F : Type} [Field F] (f g : F →+* Qb) : Qb →+* Qb :=
  haveI : Nonempty (Qb →+* Qb) := ⟨RingHom.id Qb⟩
  if f = g then RingHom.id Qb else Classical.epsilon fun σ => σ.comp f = g

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ)

example (a : κ.c.F) : ((inclQb κ.c a : Qb) : ℂ) = a := rfl

def ioAt (p : ℕ) [Fact p.Prime] (y : Pt s) : Qb →+* ℂ_[p] := (iotaP p).comp (carry y.fK (inclQb κ.c))

def normDetIo (p : ℕ) [Fact p.Prime] (b : Bool) (τ : D.what₂.Tau) (y : Pt s) (io : Qb →+* ℂ_[p]) (a : Qb) : ℝ :=
  ‖io a‖ * Real.exp (∑ i : Fin N, y.lnRoot io p b (DV.tauEmb D τ) i)

open Classical in

def normDetAt (p : ℕ) (b : Bool) (τ : D.what₂.Tau) (y : Pt s) (a : Qb) : ℝ :=
  if h : p.Prime then (haveI := Fact.mk h; normDetIo s p b τ y (ioAt s p y) a) else 1

def padAt {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg} (L : LocSt D N j ng)
    (G : GlobSt fun p => (L.loc p).Mdl) (M : AdmSt D N j jC) (F : FlatSt s)
    (I : ArIn D.what₂.Tau N (D.R.f * N) s.Comp) : PadPkg D N j s.Comp jC ng :=
  { padOf s L G M F I with
    normDetT := fun p τ (y : Pt s) => normDetAt s p true τ y (F.sv τ y)
    normDetH := fun p τ (y : Pt s) => normDetAt s p false τ y (F.sv τ y) }

section Unfold

variable {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg} (L : LocSt D N j ng)
  (G : GlobSt fun p => (L.loc p).Mdl) (M : AdmSt D N j jC) (F : FlatSt s) (I : ArIn D.what₂.Tau N (D.R.f * N) s.Comp)

end Unfold

end GlobalTheory.ShFam.Pad
