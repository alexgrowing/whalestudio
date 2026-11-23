import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EpsilonSubOneDvdAinfCoeffZeroOfThetaVanishing
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTeichmullerTiltMinusOnePowDivEnvelope
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.BKGal
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.epsilon_sub_one_dvd_ainf_coeff_zero_of_theta_vanishing : ∀ (l : ℕ) [Fact l.Prime] (ε : OCb l), IsEps ε → ∀ a : Ainf l, (∀ n : ℕ, Per.θ l (WittVector.frobenius^[n] a) = 0) → (ε - 1) ∣ a.coeff 0 := by
  first | exact @GlobalTheory.eps_sub_one_dvd_coeff_zero | exact GlobalTheory.eps_sub_one_dvd_coeff_zero | (intros; apply GlobalTheory.eps_sub_one_dvd_coeff_zero <;> assumption)
