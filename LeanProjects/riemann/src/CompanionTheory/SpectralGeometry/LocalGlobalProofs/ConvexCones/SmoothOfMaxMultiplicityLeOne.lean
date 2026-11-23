import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotIsPrimZero
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.SmoothFanTerminal

theorem smoothEnd : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (φ lab : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) → IsPolyFan bar q φ → SimpLab bar q φ lab → maxMult bar q φ ≤ 1 → IsPolFan bar q φ ∧ NoSelfInt bar q φ :=
  fun _ _ _ _ _ _ _ _ _ _ hD hPF hSL hM => GlobalTheory.PolFan.SmoothEnd.isPolFan_of_maxMult_le_one hD hPF hSL hM

end GlobalTheory.CompanionTheory.Ar.Fan.SmoothFanTerminal
