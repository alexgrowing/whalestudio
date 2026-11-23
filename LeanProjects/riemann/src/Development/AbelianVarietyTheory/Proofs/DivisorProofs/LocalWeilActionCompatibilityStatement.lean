import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilActionCompatibility
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_weil_action_compatibility : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (v : Pl F) (g : UA σ X.J) (h : UA σ W.J), g ∈ UAt σ X (evFin F v) →
    h ∈ UAt σ W (evFin F v) → ∀ (w : Matrix (Fin n) (Fin d) (AE F E)), ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      locOp v (om (g, h)) (locOp v (M.co.rho B.ψ (partFin v w)) φ) =
        locOp v (M.co.rho B.ψ (partFin v (mat g * w * (mat h)ᵀ))) (locOp v (om (g, h)) φ) := by
  first | exact @GlobalTheory.ThK.LemF.locOp_weil_rho | exact GlobalTheory.ThK.LemF.locOp_weil_rho | (intros; apply GlobalTheory.ThK.LemF.locOp_weil_rho <;> assumption)
