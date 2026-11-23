import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy

namespace GlobalTheory.PairStep

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]

def IsQCart [IsLocallyNoetherian X] (D : X → ℚ) : Prop :=
  ∃ (m : ℕ) (D₀ : CartierDiv X), 0 < m ∧ D₀.Eff ∧ D = qWeil D₀ m

def QNum [IsLocallyNoetherian X] (p : X ⟶ Sp k) (N : LB X) (b : ℚ) (D : X → ℚ) : Prop :=
  letI := algebraΓOfHom p
  ∃ (m : ℕ) (D₀ : CartierDiv X), 0 < m ∧ D₀.Eff ∧ D = qWeil D₀ m ∧
    ∀ C : Closeds X, IsCompleteCurve k C →
      (interNumRed k C ![toLB D₀] : ℚ) / m = b * interNumRed k C ![N]

omit [IsIntegral X] in

def Off (B : X → ℚ) (z : X) : Prop := ∀ w, w ⤳ z → B w = 0

def CentreAt {p : X ⟶ Sp k} (E : DivOver p) (z : X) : Prop :=
  E.Through z ∧ ∀ f : X.functionFieldˣ, RegAt z (f : X.functionField) → E.ord f = 0 →
    RegAt z ((f⁻¹ : X.functionFieldˣ) : X.functionField)

def IsNkltCentre (p : X ⟶ Sp k) (n : ℕ) (Γ : X → ℚ) (z : X) : Prop :=
  ∃ (E : DivOver p) (η : RatForms p n) (m : ℕ) (g : X.functionFieldˣ),
    η ≠ 0 ∧ 0 < m ∧ IsLogEqn p Γ η z m g ∧ CentreAt E z ∧ discrep E η m g ≤ -1

def LcCut (p : X ⟶ Sp k) (n : ℕ) (Γ : X → ℚ) (x : X) (j : ℕ) : Prop :=
  LcAt p n Γ x ∧ ¬ KltAt p n Γ x ∧
    ∀ z, z ⤳ x → ¬ KltAt p n Γ z → topologicalKrullDim (closure ({z} : Set X)) ≤ j

theorem QNum.isQCart [IsLocallyNoetherian X] {p : X ⟶ Sp k} {N : LB X} {b : ℚ} {D : X → ℚ}
    (h : QNum p N b D) : IsQCart D := by
  obtain ⟨m, D₀, hm, he, hD, -⟩ := h
  exact ⟨m, D₀, hm, he, hD⟩

end GlobalTheory.PairStep
