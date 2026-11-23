import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationCompactSetBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evaluation_compact_set_bound : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (M₁ : Model σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n d), M₁.IsGood B.ψ → IsEv B M M₁ 1 1 ∅ e →
    ∀ Cc : Set (UA σ X.J), IsCompact Cc → ∀ φ ∈ SB (Fin n × Fin d → Af F),
    ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ (f : SInf F (Fin n × Fin d)) (κ : UA σ X.J) (h : UA σ W.J), κ ∈ Cc →
      ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * (ht h : ℝ) ^ k ∧ ∀ z : Fin n × Fin d → AF F,
        ‖e (om (κ, h) (pureA F f φ)) z‖ ≤
          C * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k * ((1 + ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (z j))) ^ N)⁻¹ ∧
        (e (om (κ, h) (pureA F f φ)) z ≠ 0 → ∀ j (v : Pl F), evFin F v ((m : AF F) * z j) ∈ v.adicCompletionIntegers F) := by
  first | exact @GlobalTheory.ThKTorusBound.major_bound | exact GlobalTheory.ThKTorusBound.major_bound | (intros; apply GlobalTheory.ThKTorusBound.major_bound <;> assumption)
