import Mathlib
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExists

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor

def GoodOrigin.Extra {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} [DecidableEq (CMType H)]
    {T : RootTower (CMType H) (D.p + D.q)} (o : GoodOrigin Y T) : Prop :=
  (∀ a, ∀ x : (o.Sys a).X, ∃ (U : Set (o.Sys a).X) (lam : (o.Sys a).X → Fin ((o.Fx a).m + 1) → ℂ),
    IsOpen U ∧ x ∈ U ∧ (∀ i, (o.Sys a).A.HoloOn U fun y => lam y i) ∧
    (∀ y ∈ U, ∃ a₀ : ℂ, a₀ ≠ 0 ∧ lam y = a₀ • (o.Fx a).pt y) ∧
    ∀ p, lam x p ≠ 0 → ∀ j, x ∈ ((o.Sys a).A.chart j).source →
      (fderiv ℂ (fun z i => lam (((o.Sys a).A.chart j).symm z) i / lam (((o.Sys a).A.chart j).symm z) p)
        ((o.Sys a).A.chart j x)).ker = ⊥) ∧
  ∀ B a, ∀ p ∈ o.S B, (o.Or B a).𝔐.R p = 4

def GoodTowerExistsX : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l)
    (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)],
    IsGlobal Xo l c Y → SplitComps Y → 1 ≤ D.p → 1 ≤ D.q →
      ∃ (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T), o.Extra

def VolumeTheoremX : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H)
      (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F))
      [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem),
      IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.q →
      3 * D.q + 1 ≤ D.p + D.q → T.bad.card ≤ 4 * Fintype.card (CMType H) * (D.p + D.q) ^ 2 →
        T.Proportional ∧ T.VolEq ∧ T.T1 II ∧ T.ThmB II (hhFl (CMType H) (D.p + D.q) II) ∧
          T.T2 II C (hostRd E) (hostLval H) ∧ T.MeanSlope II C (hostRd E) (hostLval H)

end GlobalTheory.CompanionTheory.Ar.Top
