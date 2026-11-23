import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignConeWeightIndicator
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sign_cone_weight_indicator : ∀ m : ℕ, ∀ (y : (Fin m → SignType) → ℝ) a, PosFam y → gam y a = Set.indicator {a | ∀ e, sdot e a ≤ y e} 1 a := by
  first | exact @GlobalTheory.CompanionTheory.ChainInd.gam_eq_indicator | exact GlobalTheory.CompanionTheory.ChainInd.gam_eq_indicator | (intros; apply GlobalTheory.CompanionTheory.ChainInd.gam_eq_indicator <;> assumption)
