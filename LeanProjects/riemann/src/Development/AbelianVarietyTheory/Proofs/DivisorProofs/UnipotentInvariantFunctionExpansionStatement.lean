import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentInvariantFunctionExpansion
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_invariant_function_expansion : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), HidaSetting σ J X Y L a h →
    ∀ Φ : unipRad σ J (col0 X) → ℂ, (∀ (ν : (ratPts σ J).subgroupOf (unipRad σ J (col0 X))) u, Φ (ν • u) = Φ u) →
    ∀ (μ : Measure (unipRad σ J (col0 X))) (𝓕 : Set (unipRad σ J (col0 X))), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J (col0 X))) 𝓕 μ → μ 𝓕 = 1 →
    ∀ (μ' : Measure (unipRad σ J (col0 X))) (𝓕' : Set (unipRad σ J (col0 X))), μ'.IsHaarMeasure →
      IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J (col0 X))) 𝓕' μ' → μ' 𝓕' = 1 →
    ∫ u in 𝓕, Φ u ∂μ = ∫ u in 𝓕', Φ u ∂μ' := by
  first | exact @GlobalTheory.EisCT.Indep.integral_indep | exact GlobalTheory.EisCT.Indep.integral_indep | (intros; apply GlobalTheory.EisCT.Indep.integral_indep <;> assumption)
