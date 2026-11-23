import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellLeastDimVanishesWhereFormVanishesDiagonal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkValEqZeroOrOne
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_leastDim_vanishes_where_form_vanishes_diagonal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ lab : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCarrierDim H.bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → Dominates H.bar X → ∀ (m : ℕ) (τ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ τ → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone τ β → (genRank τ : ℝ) ≤ lab.evalZ β → ∀ j y, β y y = 0 → τ j y y = 0 := by
  first | exact @GlobalTheory.PolFan.Mark.vanish_of_inRCone_of_genRank_le | exact GlobalTheory.PolFan.Mark.vanish_of_inRCone_of_genRank_le | (intros; apply GlobalTheory.PolFan.Mark.vanish_of_inRCone_of_genRank_le <;> assumption)
