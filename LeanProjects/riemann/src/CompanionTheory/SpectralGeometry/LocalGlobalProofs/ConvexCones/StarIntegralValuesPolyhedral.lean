import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyFanOfStarSubdivisionCells
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthToFunNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SuperadditiveOfCellsCoverConeStatement
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.IsStarOfFiniteCover
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.StarPolyhedralFan

theorem isPolyFan_star : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ w ψ' : InvFun O), IsPolyFan bar q ψ → IsCentreSet bar q ψ w → IsStarOf bar q ψ w ψ' → (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, ψ'.evalZ β = n) → (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < ψ'.evalZ β) → IsPolyFan bar q ψ' := by
  intro O _ _ _ _ bar hO q ψ w ψ' hψ hc hs hint hpos
  unfold GlobalTheory.PolFan.IsPolyFan
  intro X _ _ _ _ hX
  obtain ⟨S, hSf, hS⟩ := GlobalTheory.CompanionTheory.Ar.Fan.StarFiniteCover.isStarOf_finite_cover O bar hO q ψ w ψ' hψ hc hs X hX
  refine ⟨GlobalTheory.PolFan.StarFan.homog_of_cover O bar ψ' X ?_, GlobalTheory.T.superadditive_of_cells_cover_cone O bar ψ' X ?_, hint X hX, hpos X hX,
    ⟨S, hSf, hS⟩⟩
  all_goals
    intro B hB
    obtain ⟨e, m, γ, c, h1, -, h3, h4⟩ := hS B hB
    exact ⟨e, m, γ, c, h1, h3, h4⟩

end GlobalTheory.CompanionTheory.Ar.Fan.StarPolyhedralFan
