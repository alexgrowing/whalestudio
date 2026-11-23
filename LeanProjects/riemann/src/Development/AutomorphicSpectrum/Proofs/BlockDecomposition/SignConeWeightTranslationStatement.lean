import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignConeWeightTranslation
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sign_cone_weight_translation : ∀ m : ℕ, (∀ y : (Fin m → SignType) → ℝ, Measurable (gam y)) ∧ (∀ (y : (Fin m → SignType) → ℝ) a b, gam (fun e => y e + sdot e b) (a + b) = gam y a) ∧ ∀ (y y' : (Fin m → SignType) → ℝ) e s t a, (∀ e', SLe e e' ∨ SLe e' e → y e' = y' e') → gam (Function.update y e s) a - gam (Function.update y e t) a = gam (Function.update y' e s) a - gam (Function.update y' e t) a := by
  first | exact @GlobalTheory.CompanionTheory.ChainSum.chainSum_rest | exact GlobalTheory.CompanionTheory.ChainSum.chainSum_rest | (intros; apply GlobalTheory.CompanionTheory.ChainSum.chainSum_rest <;> assumption)
