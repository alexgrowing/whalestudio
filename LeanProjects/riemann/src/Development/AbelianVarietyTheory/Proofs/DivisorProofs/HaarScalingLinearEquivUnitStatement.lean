import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarScalingLinearEquivUnit
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCA
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.LeviModulus
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_scaling_linear_equiv_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n₁ : ℕ) (X₁ : Spc F E n₁) (r₁ s₁ : ℕ), B.IsGood σ → X₁.IsHerm σ B r₁ s₁ →
    ∀ [IsTopologicalRing (AE F E)] [LocallyCompactSpace (AE F E)] [MeasurableSpace (Fin n₁ → AE F E)]
      [BorelSpace (Fin n₁ → AE F E)] (l : (AE F E)ˣ) (g₀ : UA σ X₁.J) (L : (Fin n₁ → AE F E) ≃ₜ+ (Fin n₁ → AE F E)),
      (∀ a, L a = cA σ l • (mat g₀ *ᵥ a)) → addEquivAddHaarChar L = absE F E l ^ n₁ := by
  first | exact @GlobalTheory.LeviModulus.CharVec.haarChar_smul_mulVec | exact GlobalTheory.LeviModulus.CharVec.haarChar_smul_mulVec | (intros; apply GlobalTheory.LeviModulus.CharVec.haarChar_smul_mulVec <;> assumption)
