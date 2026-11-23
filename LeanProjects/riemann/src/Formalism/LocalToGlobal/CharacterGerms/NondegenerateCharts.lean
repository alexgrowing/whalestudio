import Formalism.LocalToGlobal.CharacterGerms.RowTieTop

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section Formal

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

def FBChart.chartLinearTerm (Y : FBChart C V O dd) (u : Fin dd → C) : PS C 2 dd :=
  fun μ => ∑ i, u i * MvPowerSeries.coeff
    (μ.mapDomain (fun p : Fin 2 × Fin dd => (p.1.succ, p.2)) + Finsupp.single ((0 : Fin 3), i) 1) Y.B.ph2

def cvAt (s : MvPowerSeries (Fin 2) C) (γ : PowerSeries C) : MvPowerSeries (Fin 2) C :=
  MvPowerSeries.subst (fun _ : Unit => s) γ

def NDG (Y : FBChart C V O dd) : Prop :=
  ∀ γ : Fin dd → PowerSeries C, IsCv V γ → (∃ i, ¬ V.MM (PowerSeries.coeff 1 (γ i))) →
    (∀ i (μ : Fin 2 →₀ ℕ), μ 0 < V.l → μ 1 < V.l → V.MM (MvPowerSeries.coeff μ
      (MvPowerSeries.subst (fun p : Fin 2 × Fin dd => cvAt (MvPowerSeries.X p.1) (γ p.2)) (Y.B.G.F i) -
        cvAt (MvPowerSeries.X 0 + MvPowerSeries.X 1) (γ i)))) →
    ¬ ∃ b : PS C 1 dd, IntS V b ∧ ∀ μ, V.MM (MvPowerSeries.coeff μ
      (Y.chartLinearTerm (fun i => PowerSeries.coeff 1 (γ i)) -
        (ev (n := 2) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1)] b - ev (n := 2) ![pt C dd 0] b -
          ev (n := 2) ![pt C dd 1] b)))

end Formal

def RankMaximalOfNondegenerate : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I),
    NDG Y → (Y.raw p).RankHyp → ∀ Hc : ∀ g, (Y.raw p).CartHyp V g, RawChart.RankMaximalCondition Hc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

def NondegenerateCharts : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → NDG Y

theorem rank_maximal_charts_of_nondegenerate (h1 : RankMaximalOfNondegenerate) (h2 : NondegenerateCharts Xo c) : RankMaximalCharts Xo c :=
  fun hstar T io y C3 C _ _ V ι hι k Y hY _ d _ lab ha hg hr o Hc =>
    h1 C V (𝓞 E) _ Y d _ (pairOfLab ha hg o) (h2 hstar T io y C3 C V ι hι k Y hY) (rankHyp_ofLab ha hg hr o) Hc

end Formalism.L2.FormalSeriesBounds
