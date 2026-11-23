import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ConeSite
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartOpenMemCoverOfO1Statement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeSite

theorem wU_le_KS : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (D : E.LineData X) {N m : ℕ}
    (i : X ⟶ PSpace K N) (y : Fin m → MvPolynomial (Fin (N + 1)) K) (s : ℕ), IsTautologicalLineAt D N i → wU q i y s ≤ KS q s (𝒱D D) := by
  intro K _ X q D N m i y s hO T hT
  obtain ⟨k, hQ, V, ⟨j, rfl⟩, hV⟩ := hT
  exact ⟨hQ, wch i j, GlobalTheory.T.chart_open_mem_cover_of_O1 D N i hO j, fun x hx => (hV hx).2⟩

end GlobalTheory.CompanionTheory.ConeSite
