import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGoodMapSideCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalCoeffF
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_good_map_side_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l₁ l₂ : Level H)
    (Xo : Moduli D (GlobalTheory.LvCover.top l₁ l₂)) (Xs : Moduli D (GlobalTheory.LvCover.side l₁ l₂)) (c₁ : Coeff l₁) (c₂ : Coeff l₂)
    (Y : GlobalTheory.TorRef.GMod Xo (GlobalTheory.LvCover.coeffTop c₁ c₂)) (Ys : GlobalTheory.TorRef.GMod Xs (GlobalTheory.LvCover.coeffSide c₁ c₂)),
    ∃ r, GlobalTheory.LvCover.GoodMap (le_refl (GlobalTheory.LvCover.coeffF c₁ c₂)) Y Ys r := by
  first | exact @GlobalTheory.LvCover.side_goodMap | exact GlobalTheory.LvCover.side_goodMap | (intros; apply GlobalTheory.LvCover.side_goodMap <;> assumption)
