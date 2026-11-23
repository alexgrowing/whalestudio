import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem lcAt_iff_of_isLogEqn : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Γ : X → ℚ) (η : RatForms p n) (x : X) (m : ℕ) (g : X.functionFieldˣ), η ≠ 0 → 0 < m → IsLogEqn p Γ η x m g → (LcAt p n Γ x ↔ ∀ E : DivOver p, E.Through x → -1 ≤ discrep E η m g) := by
  intro X _ _ _ p n hp hn Γ η x m g hη hm h
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  exact ⟨fun ⟨_, _, _, h₁, h₂, h₃, h₄⟩ E hE => discrep_eq hn h₁ hη h₂ hm h₃ h hE ▸ h₄ E hE,
    fun h' => ⟨η, m, g, hη, hm, h, h'⟩⟩

end GlobalTheory.PairStep
