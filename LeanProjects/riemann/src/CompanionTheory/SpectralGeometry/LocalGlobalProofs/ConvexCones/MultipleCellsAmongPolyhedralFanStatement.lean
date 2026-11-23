import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MultipleCellsAmongPolyhedralFan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMultCellsAmongOfIsPolyFan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiple_cells_among_polyhedral_fan : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (φ : InvFun O),
    IsPolyFan bar q φ → ∀ M : ℕ, ∃ n : ℕ, MultCellsAmong bar q φ M n := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.MultipleCells.multCellsAmong_of_isPolyFan | exact GlobalTheory.CompanionTheory.Ar.Fan.MultipleCells.multCellsAmong_of_isPolyFan | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.MultipleCells.multCellsAmong_of_isPolyFan <;> assumption)
