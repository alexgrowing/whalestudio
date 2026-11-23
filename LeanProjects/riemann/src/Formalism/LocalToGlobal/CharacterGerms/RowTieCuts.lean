import Formalism.LocalToGlobal.CharacterGerms.HostTraceIdentity

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

def LogExSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (dd : ℕ) (G : FGLaw C dd), ∃ lg ex : Pt C 1 dd,
    (∀ i (μ : Fin 1 × Fin dd →₀ ℕ), μ.degree ≤ 1 →
      MvPowerSeries.coeff μ (lg i) = MvPowerSeries.coeff μ (MvPowerSeries.X ((0 : Fin 1), i) : PS C 1 dd)) ∧
    (∀ i, ev (n := 2) ![addOf G.F (pt C dd 0) (pt C dd 1)] (lg i) =
      ev (n := 2) ![pt C dd 0] (lg i) + ev (n := 2) ![pt C dd 1] (lg i)) ∧
    (∀ i, MvPowerSeries.constantCoeff (ex i) = 0) ∧ comp1 lg ex = pt C dd 0 ∧ comp1 ex lg = pt C dd 0

structure IsMapFB {K C : Type} [Field K] [Field C] (φ : K →+* C) {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (B : FB K dd O) (B' : FB C dd O) : Prop where
  F : ∀ j, B'.G.F j = MvPowerSeries.map φ (B.G.F j)
  act : ∀ a j, B'.A.act a j = MvPowerSeries.map φ (B.A.act a j)
  ph1 : B'.ph1 = MvPowerSeries.map φ B.ph1
  ph2 : B'.ph2 = MvPowerSeries.map φ B.ph2
  sy : B'.sy = MvPowerSeries.map φ B.sy
  ad : ∀ a, B'.ad a = MvPowerSeries.map φ (B.ad a)

def FBMapSt : Prop :=
  ∀ (K C : Type) [Field K] [Field C] (φ : K →+* C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (B : FB K dd O),
    ∃ B' : FB C dd O, IsMapFB φ B B'

def GaugeMapSt : Prop :=
  ∀ (K C : Type) [Field K] [Field C] [CharZero K] [CharZero C] (φ : K →+* C) (O : Type) [CommRing O] [StarRing O]
    (dd : ℕ) (B : FB K dd O) (B' : FB C dd O), IsMapFB φ B B' →
    ∀ h : PS K 2 dd, B.IsCanonGauge K h → B'.IsCanonGauge C (MvPowerSeries.map φ h)

def EmbIntSt : Prop :=
  ∀ (T : CDVR) (C : Type) [Field C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ t : T.V, V.Ge 0 (ι (algebraMap T.V T.Fr t))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

end Formalism.L2.FormalSeriesBounds
