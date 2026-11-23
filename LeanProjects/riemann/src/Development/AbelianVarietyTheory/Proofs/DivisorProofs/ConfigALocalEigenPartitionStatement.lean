import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalEigenPartition
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_a_local_eigen_partition : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, GlobalTheory.ThK.LemF.IsLocPart G.M G₁.M e ei ev →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ v : Pl F,
    ∀ t h₁ m, IsLevi H' t h₁ m → m ∈ UAt σ G.W (evFin F v) → h₁ ∈ UAt σ G₁.W (evFin F v) →
    ∀ u ∈ unip σ G.W H', u ∈ UAt σ G.W (evFin F v) → ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
      ev v (locOp v (om (1, u * m)) φ) = GlobalTheory.ThK.LemF.fac X.β (((b + 2 : ℕ) : ℝ) / 2) t • locOp v (om₁ (1, h₁)) (ev v φ) := by
  first | exact @GlobalTheory.ThK.LemF.evLocLaw_isoA | exact GlobalTheory.ThK.LemF.evLocLaw_isoA | (intros; apply GlobalTheory.ThK.LemF.evLocLaw_isoA <;> assumption)
