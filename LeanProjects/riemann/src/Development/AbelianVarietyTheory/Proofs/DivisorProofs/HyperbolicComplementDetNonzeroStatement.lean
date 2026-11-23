import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicComplementDetNonzero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
open scoped Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_complement_det_nonzero : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E), (∀ e, σ (σ e) = e) → ∀ (n n₁ : ℕ) (J : Matrix (Fin n) (Fin n) E) (J₁ : Matrix (Fin n₁) (Fin n₁) E) (x y : Fin n → E) (ι : Matrix (Fin n) (Fin n₁) E), n = n₁ + 2 → (∀ i j, σ (J j i) = -J i j) → form σ J x x = 0 → form σ J y y = 0 → form σ J x y = 1 → (∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) → ιᵀ * J * ι.map σ = J₁ → J₁.det ≠ 0 → Matrix.vecMulVec x (J *ᵥ fun i => σ (y i)) - Matrix.vecMulVec y (J *ᵥ fun i => σ (x i)) + ι * (J₁ᵀ)⁻¹ * (J * ι.map σ)ᵀ = 1 := by
  first | exact @GlobalTheory.PlaneRecon.recon | exact GlobalTheory.PlaneRecon.recon | (intros; apply GlobalTheory.PlaneRecon.recon <;> assumption)
