import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SectionBaseChangeTests

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def SecBC (Xo : Moduli Dw l) {c c' : Coeff l} (hle : c.F ≤ c'.F) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ f' ∈ sec Xo c' a n, ∃ (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c),
    (∀ i, fs i ∈ sec Xo c a n) ∧ IsBC hle f' as fs

def SecBCAll (Xo : Moduli Dw l) {c c' : Coeff l} (hle : c.F ≤ c'.F) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), SecBC Xo hle a n

def IsBCTest {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {m : ℕ} (f' : Rul Xo c') (as : Fin m → c'.F)
    (fs : Fin m → Rul Xo c) : Prop :=
  ∀ (p' : TRing c'.F) [Algebra c.F p'.R] (h : AlgOver c c' hle p'.R) (y' : FrPt Xo c' p'.R)
    (p : TRing c.F) (φ : p.R →ₐ[c.F] p'.R) (y : FrPt Xo c p.R), FrMap φ y (y'.res hle h) →
    f' p' y' = ∑ i, algebraMap c'.F p'.R (as i) * φ (fs i p y)

def SecBCTest (Xo : Moduli Dw l) {c c' : Coeff l} (hle : c.F ≤ c'.F) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ f' ∈ sec Xo c' a n, ∃ (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c),
    (∀ i, fs i ∈ sec Xo c a n) ∧ IsBCTest hle f' as fs

end GlobalTheory.IndefiniteRowSideFullHecke.SectionBaseChangeTests
