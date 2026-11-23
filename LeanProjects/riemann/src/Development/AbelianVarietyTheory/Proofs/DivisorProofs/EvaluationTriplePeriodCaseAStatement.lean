import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationTriplePeriodCaseA
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfMemSchA

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evaluation_triple_period_case_a : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ x : UA σ G₁.V.J × UA σ G₁.W.J, ∃ (c : ℂ) (g : UA σ G.V.J × UA σ G.W.J),
      mat g.1 *ᵥ incV F H.x = incV F H.x ∧ mat g.2 *ᵥ incV F H'.y = incV F H'.y ∧
      ∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), om₁ x (e Φ) = c • e (om g Φ) := by
  first | exact @GlobalTheory.ThK.weil_ev_exchange | exact GlobalTheory.ThK.weil_ev_exchange | (intros; apply GlobalTheory.ThK.weil_ev_exchange <;> assumption)
