import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor

def GoodTowerExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l)
    (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)],
    IsGlobal Xo l c Y → SplitComps Y → 1 ≤ D.p → 1 ≤ D.q →
      ∃ T : RootTower (CMType H) (D.p + D.q), Nonempty (GoodOrigin Y T)

def VolumeTheorem : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H)
      (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F))
      [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (II : IntersectionSystem),
      IsGlobal Xo l c Y → Nonempty (GoodOrigin Y T) → IsFullIntersectionSystem II → 1 ≤ D.q →
      3 * D.q + 1 ≤ D.p + D.q → T.bad.card ≤ 4 * Fintype.card (CMType H) * (D.p + D.q) ^ 2 →
        T.Proportional ∧ T.VolEq ∧ T.T1 II ∧ T.ThmB II (hhFl (CMType H) (D.p + D.q) II) ∧
          T.T2 II C (hostRd E) (hostLval H) ∧ T.MeanSlope II C (hostRd E) (hostLval H)

end GlobalTheory.CompanionTheory.Ar.Top
