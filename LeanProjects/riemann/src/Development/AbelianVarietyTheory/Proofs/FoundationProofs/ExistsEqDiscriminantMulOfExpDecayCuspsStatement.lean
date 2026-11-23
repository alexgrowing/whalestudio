import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEqDiscriminantMulOfExpDecayCusps
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_discriminant_mul_of_expDecay_cusps : ∀ (Γ : Subgroup SL(2, ℤ)) (K : ℤ) (H : ℍ → ℂ), IsMF Γ K H → (∀ x : SL(2, ℤ), (H ∣[K] x) =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im)) → ∃ G : ℍ → ℂ, IsMF Γ (K - 12) G ∧ H = ModularForm.discriminant * G := by
  first | exact @GlobalTheory.exists_eq_discriminant_mul | exact GlobalTheory.exists_eq_discriminant_mul | (intros; apply GlobalTheory.exists_eq_discriminant_mul <;> assumption)
