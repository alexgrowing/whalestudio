import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerHaarLocalFactorCaseB
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeLin
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_haar_local_factor_case_b : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))), μK.IsHaarMeasure → ∀ f : UA σ G.V'.J → ℂ,
      (∃ U ∈ 𝓝 (1 : UA σ G.V'.J), ∀ g ∈ UAt σ G.V' (evFin F v), ∀ x ∈ U, x ∈ UAt σ G.V' (evFin F v) → f (g * x) = f g) →
      (∀ u ∈ unip σ G.V' H, u ∈ UAt σ G.V' (evFin F v) → ∀ g ∈ UAt σ G.V' (evFin F v), f (u * g) = f g) →
      (∀ t g₀ m, IsLevi H t g₀ m → m ∈ UAt σ G.V' (evFin F v) → g₀ ∈ UAt σ G₁.V' (evFin F v) →
        ∀ g ∈ UAt σ G.V' (evFin F v), f (m * g) = ((absE F E t : ℝ) : ℂ) ^ (b + 1) * f g) →
      ∀ g ∈ UAt σ G.V' (evFin F v), ∫ k, f (k.1 * g) ∂μK = ∫ k, f k.1 ∂μK := by
  first | exact @GlobalTheory.IwKInt.integral_KAt_right_invariant | exact GlobalTheory.IwKInt.integral_KAt_right_invariant | (intros; apply GlobalTheory.IwKInt.integral_KAt_right_invariant <;> assumption)
