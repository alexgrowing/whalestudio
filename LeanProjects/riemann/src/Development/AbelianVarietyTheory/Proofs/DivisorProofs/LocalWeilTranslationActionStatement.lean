import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilTranslationAction
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_weil_translation_action : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E)
    (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (v : Pl F) (h : UA σ W.J),
    h ∈ UAt σ W (evFin F v) → ∀ z : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) z → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      locOp v (M.co.rho B.ψ z) (locOp v (om (1, h)) φ) = locOp v (om (1, h)) (locOp v (M.co.rho B.ψ (z * (mat h⁻¹)ᵀ)) φ) := by
  first | exact @GlobalTheory.ThK.LemF.RhoConj.rho_om_comm | exact GlobalTheory.ThK.LemF.RhoConj.rho_om_comm | (intros; apply GlobalTheory.ThK.LemF.RhoConj.rho_om_comm <;> assumption)
