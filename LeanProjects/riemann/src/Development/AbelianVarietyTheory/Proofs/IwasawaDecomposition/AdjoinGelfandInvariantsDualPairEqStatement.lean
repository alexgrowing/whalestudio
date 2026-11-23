import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdjoinGelfandInvariantsDualPairEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PolarConjTranspose
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRel
open Matrix GlobalTheory.Mem.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoin_gelfandInvariants_dual_pair_eq : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n m : ℕ) (x d : Fin n × Fin m → A), IsCCR x d → ∀ c c' : ℂ, Algebra.adjoin ℂ (Set.range (GlobalTheory.SmoothForms.gelfA fun i j : Fin n => ∑ a, x (i, a) * d (j, a) + if i = j then algebraMap ℂ A c else 0)) = Algebra.adjoin ℂ (Set.range (GlobalTheory.SmoothForms.gelfA fun a b : Fin m => -∑ i, x (i, b) * d (i, a) + if a = b then algebraMap ℂ A c' else 0)) := by
  first | exact @GlobalTheory.Mem.Capelli.adjoin_gelfA_dual_pair | exact GlobalTheory.Mem.Capelli.adjoin_gelfA_dual_pair | (intros; apply GlobalTheory.Mem.Capelli.adjoin_gelfA_dual_pair <;> assumption)
