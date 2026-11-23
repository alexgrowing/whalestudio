import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfInterGrLineShiftCoordinate
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FlagZ GlobalTheory.ArInt Formalism.DegreeFormula GlobalTheory.Cartier

noncomputable section

namespace GlobalTheory.FlagZ

theorem flDet_zero_last_isometric_triv : ∀ (ι : Type) [Fintype ι] (N : ℕ) (τ : ι),
    (flDet τ 0 : GlobalTheory.HermLB (flStr ι N)).Isometric (GlobalTheory.HermLB.triv _) ∧
      (flDet τ (Fin.last N) : GlobalTheory.HermLB (flStr ι N)).Isometric (GlobalTheory.HermLB.triv _) := by
  intro ι _ N τ
  exact ⟨HermLB.icls_eq_iff.1 ((icls_flDet_eq_zero τ 0 (by simp [plDim])).trans HermLB.icls_triv.symm),
    HermLB.icls_eq_iff.1 ((icls_flDet_eq_zero τ (Fin.last N) (by simp [plDim])).trans HermLB.icls_triv.symm)⟩

end GlobalTheory.FlagZ
