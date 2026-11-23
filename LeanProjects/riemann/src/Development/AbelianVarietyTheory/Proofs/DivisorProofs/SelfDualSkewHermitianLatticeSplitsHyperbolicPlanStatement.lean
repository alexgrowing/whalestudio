import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualSkewHermitianLatticeSplitsHyperbolicPlan
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLowLat
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualSkewHermitianLattice_splits_hyperbolicPlane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 → ∀ (n₁ : ℕ) (J : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) E)
    (L : Submodule (𝓞 E) (Fin (n₁ + 2) → E)), (∀ i j, σ (J j i) = -J i j) → L.IsLattice E →
    (∀ y, y ∈ L ↔ ∀ x ∈ L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * form σ J y x))) →
    ∀ x : Fin (n₁ + 2) → E, x ≠ 0 → form σ J x x = 0 →
    ∃ (y : Fin (n₁ + 2) → E) (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) E), form σ J x y = 1 ∧ form σ J y y = 0 ∧
      (∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) ∧
      (∀ (s t : E) (u : Fin n₁ → E), s • x + ι *ᵥ u + t • y = 0 → s = 0 ∧ t = 0 ∧ u = 0) ∧
      ∀ z ∈ L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ L ∧ t • y ∈ L ∧ ι *ᵥ u ∈ L ∧ z = s • x + ι *ᵥ u + t • y := by
  first | exact @GlobalTheory.PlaneSkewSplit.split_global | exact GlobalTheory.PlaneSkewSplit.split_global | (intros; apply GlobalTheory.PlaneSkewSplit.split_global <;> assumption)
