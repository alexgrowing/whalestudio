import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SymplecticValTauCompat
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_val_tau_compat : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V W : HSp D) (τ : D.what₂.Tau) (x y : WA V W), valTau θ τ (sympl V W x y) = symplC V W τ (wAt θ V W τ x) (wAt θ V W τ y) := by
  first | exact @GlobalTheory.FockCompare.SymplVal.valTau_sympl | exact GlobalTheory.FockCompare.SymplVal.valTau_sympl | (intros; apply GlobalTheory.FockCompare.SymplVal.valTau_sympl <;> assumption)
