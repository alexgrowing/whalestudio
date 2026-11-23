import Formalism.LocalToGlobal.CharacterGerms.RowTieTop

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.PGsh.Up CharacteristicFromRanks ValuationFitting

def RawChart.HTDPack {C : Type} [Field C] {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type}
    [Fintype κ] {X : RawChart C d I κ} (Hc : ∀ g, X.CartHyp V g) : Prop :=
  ∃ (rh : ℕ) (h : Fin 2 → ℕ) (ht : ∀ g, Fin (h g) → I g → C) (vm : Valuation C NNReal)
    (R : Type) (_ : CommRing R) (_ : Algebra R C) (_ : Algebra ℤ_[V.l] R)
    (O : Type) (_ : CommRing O) (_ : Algebra ℤ_[V.l] O) (σ : O ≃ₐ[ℤ_[V.l]] O) (cp : R) (gB : ℕ)
    (Hh : HodgeTateDatum V.l gB vm R O σ cp) (U : UnramData V.l gB vm R O σ cp Hh),
    (∀ g i x, V.Ge 0 (ht g i x)) ∧ HodgeTateSetting V.l vm R O σ cp ∧
    Nonempty (Comparison₂ (fun g => RawChart.cart (Hc g)) X.big rh h ht vm R O σ cp gB Hh U) ∧
    ∀ g (i : Fin (h g)) (S : ∀ g, Sys (RawChart.cart (Hc g))) (t : ∀ g, I g → MvPowerSeries (I g) C),
      (∀ g, (S g).IsT (t g)) →
      upG g (mvExp (∑ x : I g, ht g i x • (MvPowerSeries.X x : MvPowerSeries (I g) C))) ∈ IntGerm V t

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

def HodgeTateAllCharts : Prop := AllCharts Xo c fun _ _ V _ _ _ _ X => ∀ Hc : ∀ g, X.CartHyp V g, RawChart.HTDPack Hc

end Formalism.L2.FormalSeriesBounds
