import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.Discrepancy

theorem kltAt_lcAt_of_specializes (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    (p : X ⟶ Sp ℂ) (n : ℕ) (Γ : X → ℚ) (x z : X) (hzx : z ⤳ x) :
    (KltAt p n Γ x → KltAt p n Γ z) ∧ (LcAt p n Γ x → LcAt p n Γ z) :=
  ⟨fun ⟨η, m, g, h₁, h₂, h₃, h₄⟩ =>
      ⟨η, m, g, h₁, h₂, fun w hw E hE => h₃ w (hw.trans hzx) E hE,
        fun E hE => h₄ E (hE.of_specializes hzx)⟩,
    fun ⟨η, m, g, h₁, h₂, h₃, h₄⟩ =>
      ⟨η, m, g, h₁, h₂, fun w hw E hE => h₃ w (hw.trans hzx) E hE,
        fun E hE => h₄ E (hE.of_specializes hzx)⟩⟩

theorem kltAt_lcAt_generisation :
    ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ),
      ∀ (Γ : X → ℚ) (x z : X), z ⤳ x →
        (KltAt p n Γ x → KltAt p n Γ z) ∧ (LcAt p n Γ x → LcAt p n Γ z) :=
  fun X _ _ p n Γ x z h => kltAt_lcAt_of_specializes X p n Γ x z h

end GlobalTheory.Discrepancy
