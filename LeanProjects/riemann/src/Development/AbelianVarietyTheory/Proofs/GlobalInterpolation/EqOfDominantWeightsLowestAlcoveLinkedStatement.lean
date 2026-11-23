import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOfDominantWeightsLowestAlcoveLinked
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_dominantWeights_lowestAlcove_linked : ∀ (p N : ℕ), p.Prime → ∀ (ν μ : Fin N → ℕ), Antitone ν → Antitone μ → (∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0 ∧ μ ⟨0, h⟩ ≤ ν ⟨0, h⟩ ∧ ν ⟨0, h⟩ + (N - 1) ≤ p) → (∀ x : ZMod p, (Finset.univ.filter fun i : Fin N => ((ν i + (N - 1 - i.val) : ℕ) : ZMod p) = x).card = (Finset.univ.filter fun i : Fin N => ((μ i + (N - 1 - i.val) : ℕ) : ZMod p) = x).card) → μ = ν := by
  first | exact @GlobalTheory.Alc.eq_of_shifted_residues_eq | exact GlobalTheory.Alc.eq_of_shifted_residues_eq | (intros; apply GlobalTheory.Alc.eq_of_shifted_residues_eq <;> assumption)
