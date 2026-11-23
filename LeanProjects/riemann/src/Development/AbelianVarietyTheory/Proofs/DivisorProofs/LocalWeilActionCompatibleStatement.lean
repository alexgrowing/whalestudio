import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilActionCompatible
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_weil_action_compatible : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E)
    (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (v : Pl F) (g : UA σ X.J) (h : UA σ W.J),
    g ∈ UAt σ X (evFin F v) → h ∈ UAt σ W (evFin F v) → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      locOp v (om (g, 1)) (locOp v (om (1, h)) φ) = locOp v (om (1, h)) (locOp v (om (g, 1)) φ) := by
  first | exact @GlobalTheory.ThK.LemF.locOp_comm | exact GlobalTheory.ThK.LemF.locOp_comm | (intros; apply GlobalTheory.ThK.LemF.locOp_comm <;> assumption)
