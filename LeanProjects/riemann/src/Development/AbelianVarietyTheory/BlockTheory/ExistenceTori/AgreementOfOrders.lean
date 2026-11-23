import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.ProjectiveLattices.RegularityR2Quotient

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AgreementOfOrders

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def ptK (q : QPt Xo c) : Sp q.T.Fr ⟶ Xo.XF c :=
  letI := q.ι.toAlgebra
  pullback.lift q.y.1.x (spMap q.ι) (by
    rw [q.y.1.x_over, sOf, ← Spec.map_comp]
    rfl)

def LiesOn (Z : Comp Xo c) (q : QPt Xo c) : Prop :=
  ∀ p : Sp q.T.Fr, ptK q p ∈ (Z : Set (Xo.XF c))

def OrdersAgree (h : GenFrEx Xo c) (Z : Comp Xo c) (ord : WTZ E → AC Z → ℤ) (q : QPt Xo c) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n,
    (evC h Z f ≠ 0 → ordQ Xo c q f = (((ord (wtZ a n) (valC h a n f Z) : ℤ) : ℝ) : EReal)) ∧
    (evC h Z f = 0 → ordQ Xo c q f = ⊤)

theorem OrdersAgree.ne_top_iff {h : GenFrEx Xo c} {Z : Comp Xo c} {ord : WTZ E → AC Z → ℤ} {q : QPt Xo c}
    (hq : OrdersAgree h Z ord q) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) :
    ordQ Xo c q f ≠ ⊤ ↔ evC h Z f ≠ 0 := by
  refine ⟨fun h1 h2 => h1 ((hq a n f hf).2 h2), fun h1 => ?_⟩
  rw [(hq a n f hf).1 h1]
  exact EReal.coe_ne_top _

def OrdTieTriv [Fintype (Comp Xo c)] (h : GenFrEx Xo c)
    (d : Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z)) : Prop :=
  ∀ (Z : Comp Xo c) (v : AddValuation (Om Z) (WithTop ℤ)), d.admitted Z v → IsTrivOn c.F v →
    ∃ q : QPt Xo c, LiesOn Z q ∧ OrdersAgree h Z (d.ord Z v) q

end GlobalTheory.IndefiniteRowSideFullHecke.AgreementOfOrders
