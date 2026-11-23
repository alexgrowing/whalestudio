import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewSpaceRealEmbedding
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skew_space_real_embedding : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ x y : Fin n → E, form σ X.J x y = 1 →
    ∃ (N : ℕ) (emb : (Fin N → ℝ) → (Fin d → AE F E)) (lam : (Fin d → E) → Fin N → ℝ), Function.Injective lam ∧
      ∀ (w : Fin d → E) (t : Fin N → ℝ),
        B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) (Matrix.vecMulVec (incV F y) (incV F w))
            (Matrix.vecMulVec (incV F x) (emb t))) =
          Complex.exp (2 * Real.pi * Complex.I * ∑ j, (lam w j : ℂ) * (t j : ℂ)) := by
  first | exact @GlobalTheory.RealFreqSnd.injective_real_frequencies_snd | exact GlobalTheory.RealFreqSnd.injective_real_frequencies_snd | (intros; apply GlobalTheory.RealFreqSnd.injective_real_frequencies_snd <;> assumption)
