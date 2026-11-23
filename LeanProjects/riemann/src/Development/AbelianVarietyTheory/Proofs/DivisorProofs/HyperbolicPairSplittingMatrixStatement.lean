import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPairSplittingMatrix
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_pair_splitting_matrix : ∀ {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (n₁ : ℕ) (J : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) E)
    (J₁ : Matrix (Fin n₁) (Fin n₁) E) (x y : Fin (n₁ + 2) → E) (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) E)
    (P : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) E),
    (∀ a, σ (σ a) = a) → (∀ i j, σ (J j i) = J i j) → J₁.det ≠ 0 → form σ J x x = 0 → form σ J y y = 0 → form σ J x y = 1 →
    (∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) → ιᵀ * J * ι.map σ = J₁ →
    (∀ r i, P r (Fin.castAdd 2 i) = ι r i) → (∀ r, P r (Fin.natAdd n₁ 0) = x r) → (∀ r, P r (Fin.natAdd n₁ 1) = y r) →
    P.det ≠ 0 ∧ (∀ i i', (Pᵀ * J * P.map σ) (Fin.castAdd 2 i) (Fin.castAdd 2 i') = J₁ i i') ∧
      (∀ i t, (Pᵀ * J * P.map σ) (Fin.castAdd 2 i) (Fin.natAdd n₁ t) = 0) ∧
      (∀ t i, (Pᵀ * J * P.map σ) (Fin.natAdd n₁ t) (Fin.castAdd 2 i) = 0) ∧
      (Pᵀ * J * P.map σ) (Fin.natAdd n₁ 0) (Fin.natAdd n₁ 0) = 0 ∧ (Pᵀ * J * P.map σ) (Fin.natAdd n₁ 1) (Fin.natAdd n₁ 1) = 0 ∧
      (Pᵀ * J * P.map σ) (Fin.natAdd n₁ 0) (Fin.natAdd n₁ 1) = 1 ∧ (Pᵀ * J * P.map σ) (Fin.natAdd n₁ 1) (Fin.natAdd n₁ 0) = 1 := by
  first | exact @GlobalTheory.GramAdapted.gram_adapted | exact GlobalTheory.GramAdapted.gram_adapted | (intros; apply GlobalTheory.GramAdapted.gram_adapted <;> assumption)
