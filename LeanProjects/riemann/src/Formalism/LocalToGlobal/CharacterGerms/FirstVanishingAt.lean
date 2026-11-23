import Formalism.LocalToGlobal.CharacterGerms.RankMaximalOfNondegenerateOfUnitSeriesIntegral

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section Defs

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

def FBChart.FirstVanishingAt (Y : FBChart C V O dd) (u : Fin dd → C) : Prop :=
  ∀ k : Fin dd,
    V.MM (∑ i, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) V.l) (mulL Y.B.G.F V.l k) * u i ^ V.l)

def FBChart.aLin (Y : FBChart C V O dd) (u v : Fin dd → C) : C :=
  ∑ j, v j * MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (Y.aOf u)

def FBChart.LgLin (Y : FBChart C V O dd) (γ : Fin dd → PowerSeries C) (U : Fin dd → C) : Prop :=
  ∀ i, Agr (V.l ^ 2) (alongCv γ (un1 (Y.lg i))) (U i • (MvPowerSeries.X () : PowerSeries C))

end Defs

def FirstVanishingCore : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (γ : Fin dd → PowerSeries C) (U : Fin dd → C),
    IsCv V γ → Y.LgLin γ U → Y.FirstVanishingAt U

def FunEqCoreSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (u : Fin dd → C), (∀ i, V.Ge 0 (u i)) → Y.FirstVanishingAt u →
    ∀ μ, V.MM (MvPowerSeries.coeff μ (cobd Y.B.G.F (Y.aOf u) - frobTw V.l (Y.chartLinearTerm u)))

def CurveLinearTermCondition : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (γ : Fin dd → PowerSeries C) (U : Fin dd → C),
    IsCv V γ → Y.LgLin γ U → ∀ v : Fin dd → C, (∀ i, V.Ge 0 (v i)) →
    V.MM ((V.l : C) * PowerSeries.coeff V.l (alongCv γ (un1 (Y.sgP v))) - Y.aLin U v)

def ALinAdjSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (e eb : Pt C 1 dd),
    (∀ i, IntS V (e i)) → (∀ i, IntS V (eb i)) →
    (∀ i, MvPowerSeries.constantCoeff (e i) = 0) → (∀ i, MvPowerSeries.constantCoeff (eb i) = 0) →
    comp1 e (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1)) →
    IntS V (FB.expS C (ev (n := 2) ![comp1 e (pt C dd 0), pt C dd 1] Y.h -
      ev (n := 2) ![pt C dd 0, comp1 eb (pt C dd 1)] Y.h)) →
    ∀ u : Fin dd → C, (∀ i, V.Ge 0 (u i)) → Y.FirstVanishingAt u → ∀ v : Fin dd → C, (∀ i, V.Ge 0 (v i)) →
    V.MM (Y.aLin (linAct e u) v - Y.aLin u (linAct eb v))

end Formalism.L2.FormalSeriesBounds
