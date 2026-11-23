import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS

namespace GlobalTheory.HSApp

variable {k : Type} [Field k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {B : LB Y}

def Centred (y : Y) (ν : Valuation (Y.presheaf.stalk y) (WithZero (Multiplicative ℤ))) : Prop :=
  (∀ a, ν a ≤ 1) ∧ (∀ a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y), ν a < 1) ∧ ∀ a, ν a = 0 → a = 0

def SteepOn (W : Submodule k (H0 p B ⊤)) (C : Set Y) (s : H0 p B ⊤) : Prop :=
  ∀ y ∈ C, ∀ ν, Centred y ν → ∃ w ∈ W, ∀ (i : B.ι) (hi : y ∈ B.U i),
    ν (H0.germ i y (memTop y) hi s) < ν (H0.germ i y (memTop y) hi w)

theorem SteepOn.mono {W : Submodule k (H0 p B ⊤)} {C C' : Set Y} {s : H0 p B ⊤} (h : SteepOn W C s) (e : C' ⊆ C) :
    SteepOn W C' s := by
  intro y hy
  exact h y (e hy)

end GlobalTheory.HSApp
