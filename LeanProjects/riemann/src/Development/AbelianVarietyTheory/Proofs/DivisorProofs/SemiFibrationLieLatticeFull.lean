import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLeastHermLength
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibLieLatticeFullStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFamilyConjInvariantStatement

open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder

namespace GlobalTheory.LieHt.SemiFib

theorem full_herm_conj_rho : ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K), Full F.lieLat ∧
    (∃ h, F.IsHerm h) ∧ (∀ h, F.IsHerm h → GlobalTheory.Published.ConjInv h) ∧ (0 < F.P₀.g → ∃ ρ, F.IsRho ρ ∧ ∀ σ, 0 < ρ σ) :=
  fun K _ _ F => ⟨GlobalTheory.T.semiFib_lie_lattice_full K F, F.exists_isHerm, fun h hh => GlobalTheory.T.hermitian_family_conj_invariant K F h hh, F.exists_isRho⟩

end GlobalTheory.LieHt.SemiFib
