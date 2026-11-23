import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicAutomorphismMeasureScaling
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemImLine

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_automorphism_measure_scaling : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (b : ℕ) (J₁ : Matrix (Fin b) (Fin b) E), J₁.det ≠ 0 → ∀ (l : (AE F E)ˣ) (g₀ : UA σ J₁)
    [IsTopologicalAddGroup (Fin b → AE F E)] [LocallyCompactSpace (Fin b → AE F E)] [MeasurableSpace (Fin b → AE F E)]
    [BorelSpace (Fin b → AE F E)] (A : (Fin b → AE F E) ≃ₜ+ (Fin b → AE F E)),
    (∀ a, A a = l.1 • ((mat g₀⁻¹)ᵀ *ᵥ a)) → addEquivAddHaarChar A = absE F E l ^ b := by
  first | exact @GlobalTheory.LeviModulus.modulus_levi | exact GlobalTheory.LeviModulus.modulus_levi | (intros; apply GlobalTheory.LeviModulus.modulus_levi <;> assumption)
