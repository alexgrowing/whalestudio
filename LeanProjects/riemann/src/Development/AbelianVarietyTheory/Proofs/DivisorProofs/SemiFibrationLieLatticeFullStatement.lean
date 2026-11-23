import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibrationLieLatticeFull
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semi_fibration_lie_lattice_full : ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K), Full F.lieLat ∧ (∃ h, F.IsHerm h) ∧ (∀ h, F.IsHerm h → GlobalTheory.Published.ConjInv h) ∧ (0 < F.P₀.g → ∃ ρ, F.IsRho ρ ∧ ∀ σ, 0 < ρ σ) := by
  first | exact @GlobalTheory.LieHt.SemiFib.full_herm_conj_rho | exact GlobalTheory.LieHt.SemiFib.full_herm_conj_rho | (intros; apply GlobalTheory.LieHt.SemiFib.full_herm_conj_rho <;> assumption)
