import Formalism.LocalToGlobal.ProjectiveLattices.IsThRule

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def ThValTot (nab : NabV Xo c) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (x : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n →
      ∃! v, ThValAt Xo c nab y x P v

def LastPos (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) : Prop :=
  ∀ τ : E →+* ℂ, InPsi H τ → 0 < Dw.mult τ → 0 < a (τ, Dw.mult τ - 1)

def ThInCusp (nab : NabV Xo c)
    (cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → LastPos Dw a →
    ∀ f ∈ thGen Xo c nab a n, f ∈ cusp a n

def DF (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) : ℕ := ∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i)

def ThNe0 (nab : NabV Xo c) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → 0 < n → Dw.p + Dw.q ≤ n → DF Dw a + 2 ≤ l.M →
    (∃ P ∈ harmA (Dw := Dw) c a n, P ≠ 0) → ∃ f ∈ thGen Xo c nab a n, f ≠ 0

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj in
attribute [local instance] Over.cartesianMonoidalCategory in

def NabZero (nab : NabV Xo c) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k : ℤ)
    (F : LB.Sec (ReciprocityTheory.ChartRestriction.G.Out.LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))),
    ReciprocityTheory.ChartRestriction.G.Out.IsValueAt Xo.univ.t.G Xo.univ.t.PP.L k F 1
      (ReciprocityTheory.ChartRestriction.G.Out.rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (ptO Xo y.x) k)
      (toΓ S (nab y k F 0))

theorem existsUnique_thRule (nab : NabV Xo c) (h : ThValTot Xo c nab) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    (x : Fin n → Dw.La) {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA c a n) :
    ∃! f : Rul Xo c, IsThRule Xo c nab x P f := by
  refine ⟨fun p y => (h p.R y a n x P hP).exists.choose,
    fun p y => (h p.R y a n x P hP).exists.choose_spec, ?_⟩
  intro g hg
  funext p y
  exact (h p.R y a n x P hP).unique (hg p y) (h p.R y a n x P hP).exists.choose_spec

end Formalism.L2.Pj
