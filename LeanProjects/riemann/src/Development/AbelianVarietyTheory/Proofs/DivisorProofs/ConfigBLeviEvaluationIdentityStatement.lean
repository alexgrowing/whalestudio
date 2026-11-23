import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLeviEvaluationIdentity
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_b_levi_evaluation_identity : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ g₀ g, IsLevi H 1 g₀ g → ∀ Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))), e' (om' (g, 1) Φ) = om₁' (g₀, 1) (e' Φ) := by
  first | exact @GlobalTheory.ThK.LeviLawB.levi_law | exact GlobalTheory.ThK.LeviLawB.levi_law | (intros; apply GlobalTheory.ThK.LeviLawB.levi_law <;> assumption)
