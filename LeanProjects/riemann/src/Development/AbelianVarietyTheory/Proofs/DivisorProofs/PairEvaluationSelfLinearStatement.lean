import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairEvaluationSelfLinear
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_evaluation_self_linear : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (M₁ : Model σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n d),
    M₁.IsGood B.ψ → IsEv B M M₁ 1 1 ∅ e → ∀ f : Fn F n d →ₗ[ℂ] Fn F n d,
    (∀ (z : Matrix (Fin n) (Fin d) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d), f (M.co.rho B.ψ z Φ) = M₁.co.rho B.ψ z (f Φ)) →
    ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), f Φ = c • e Φ := by
  first | exact @GlobalTheory.ThK.EvChangeUniq.eq_smul_isEv | exact GlobalTheory.ThK.EvChangeUniq.eq_smul_isEv | (intros; apply GlobalTheory.ThK.EvChangeUniq.eq_smul_isEv <;> assumption)
