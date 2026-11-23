import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SumEigenProjectionsEqSelf
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigCoordApply
open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_eigen_projections_eq_self : ∀ (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C] [Fintype (E →+* C)], Fintype.card (E →+* C) = Module.finrank ℚ E → ∀ (M : Type) [AddCommGroup M] [Module C M] (ρ : 𝓞 E →+* Module.End C M) (y : M), ∑ s, HT.eigProj ρ s y = y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ExG.SumEig.sum_eigProj | exact GlobalTheory.CompanionTheory.Ar.Flat.ExG.SumEig.sum_eigProj | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ExG.SumEig.sum_eigProj <;> assumption)
