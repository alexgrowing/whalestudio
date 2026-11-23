import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryExponentialPathExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsTestZero
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_exponential_path_exists : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (k : Kinf E a), ∃ (c : ℝ → GL (Fin a) (Cinf E)) (Y : Lie E a), c 0 = 1 ∧ c 1 = Unitary.toUnits k ∧ (∀ s, HasDerivAt (fun t => toL (c t).val) (toL ((c s).val * Matrix.of Y)) s) ∧ (∀ s, HasDerivAt (fun t => toL ((c t)⁻¹).val) (toL (-(Matrix.of Y * ((c s)⁻¹).val))) s) := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.KCurve.exists_curve | exact GlobalTheory.CompanionTheory.SmoothRep.KCurve.exists_curve | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.KCurve.exists_curve <;> assumption)
