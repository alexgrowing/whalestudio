import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UltrametricDetNormLe
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ultrametric_det_norm_le : ∀ (A : Type) [NormedField A] [IsUltrametricDist A] (I : Type) [Fintype I] [DecidableEq I] (M : Matrix I I A) (r : ℝ), 0 ≤ r → (∀ a b, ‖M a b‖ ≤ r) → ‖M.det‖ ≤ r ^ Fintype.card I := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.norm_det_le_pow_card_of_ultrametric | exact GlobalTheory.CompanionTheory.Ar.Fl.norm_det_le_pow_card_of_ultrametric | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.norm_det_le_pow_card_of_ultrametric <;> assumption)
