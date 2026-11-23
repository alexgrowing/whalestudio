import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationTriplePeriodCaseAFourth
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfMemSchA

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evaluation_triple_period_case_a_fourth : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ μ : Measure (AE F E)ˣ, μ.IsHaarMeasure → ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), ∀ C : Set (UA σ G.V.J), IsCompact C →
      ∀ y₀ : Fin b × Fin (b + a') → AF F, ∃ U ∈ 𝓝 y₀, ∃ Gf : (AE F E)ˣ → ℝ, Integrable Gf μ ∧ ∀ k ∈ C, ∀ (l : (AE F E)ˣ), ∀ y ∈ U,
        ‖e (G.M.co.rho B.ψ (shiftA H H' l) (om (k, 1) Ψ)) y‖ * (absE F E l : ℝ) ^ ((b + 2 - a') / 2) ≤ Gf l := by
  first | exact @GlobalTheory.ConeDom.dom | exact GlobalTheory.ConeDom.dom | (intros; apply GlobalTheory.ConeDom.dom <;> assumption)
