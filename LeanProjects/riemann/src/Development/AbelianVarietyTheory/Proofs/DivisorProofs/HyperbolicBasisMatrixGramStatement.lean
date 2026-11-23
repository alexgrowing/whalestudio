import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicBasisMatrixGram
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneZeroInsertionLinearApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneEv

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_basis_matrix_gram : ∀ {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (d₁ : ℕ)
    (J : Matrix (Fin (d₁ + 2)) (Fin (d₁ + 2)) E) (J₁ : Matrix (Fin d₁) (Fin d₁) E) (x y : Fin (d₁ + 2) → E)
    (ι : Matrix (Fin (d₁ + 2)) (Fin d₁) E) (Q : Matrix (Fin (d₁ + 2)) (Fin (d₁ + 2)) E),
    (∀ a, σ (σ a) = a) → (∀ i j, σ (J j i) = -J i j) → form σ J x x = 0 → form σ J y y = 0 → form σ J x y = 1 →
    (∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) → ιᵀ * J * ι.map σ = J₁ →
    (∀ r a, Q r (Fin.castAdd 2 a) = ι r a) → (∀ r, Q r (Fin.natAdd d₁ 0) = x r) → (∀ r, Q r (Fin.natAdd d₁ 1) = y r) →
    (∀ a a', (Qᵀ * J * Q.map σ) (Fin.castAdd 2 a) (Fin.castAdd 2 a') = J₁ a a') ∧
      (∀ a t, (Qᵀ * J * Q.map σ) (Fin.castAdd 2 a) (Fin.natAdd d₁ t) = 0) ∧
      (∀ t a, (Qᵀ * J * Q.map σ) (Fin.natAdd d₁ t) (Fin.castAdd 2 a) = 0) ∧
      (Qᵀ * J * Q.map σ) (Fin.natAdd d₁ 0) (Fin.natAdd d₁ 0) = 0 ∧ (Qᵀ * J * Q.map σ) (Fin.natAdd d₁ 1) (Fin.natAdd d₁ 1) = 0 ∧
      (Qᵀ * J * Q.map σ) (Fin.natAdd d₁ 0) (Fin.natAdd d₁ 1) = 1 ∧ (Qᵀ * J * Q.map σ) (Fin.natAdd d₁ 1) (Fin.natAdd d₁ 0) = -1 := by
  first | exact @GlobalTheory.ThK.FrameGram.frame_gram | exact GlobalTheory.ThK.FrameGram.frame_gram | (intros; apply GlobalTheory.ThK.FrameGram.frame_gram <;> assumption)
