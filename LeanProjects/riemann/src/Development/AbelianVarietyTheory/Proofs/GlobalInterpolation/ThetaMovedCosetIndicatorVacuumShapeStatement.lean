import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaMovedCosetIndicatorVacuumShape
import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_movedCosetIndicator_vacuum_shape : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (cA c : ℕ), X.Ok → A.LaHyp a b S → A.AA ≠ ⊥ → IsSdLat N → IsSdLat N' → 0 < cA → 0 < c → ∃ n : ℕ, n ≠ 0 ∧ n ∣ (halfBO S (per A N N') c).toAddSubgroup.relIndex (per A N N').toAddSubgroup ∧ ∀ x ∈ divLat cA (homAt S N N'), ∀ t ∈ halfAO S (per A N N') (cA * c), t - x ∈ mulLat c (homAt S N N') → ∀ R : Finset (HomE X.E a b), IsReps (per A N N').toAddSubgroup (halfBO S (per A N N') c).toAddSubgroup R → A.thInd S N N' c x = fun z => (n : ℂ)⁻¹ * Wx A (-t) (fun z => ∑ y ∈ R, Wx A y (A.e a b N N') z) z := by
  first | exact @GlobalTheory.MomT.ThShape.thInd_shape | exact GlobalTheory.MomT.ThShape.thInd_shape | (intros; apply GlobalTheory.MomT.ThShape.thInd_shape <;> assumption)
