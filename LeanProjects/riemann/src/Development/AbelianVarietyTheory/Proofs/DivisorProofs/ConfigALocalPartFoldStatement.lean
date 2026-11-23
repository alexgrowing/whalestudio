import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalPartFold
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_A_local_part_fold : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, IsLocPart G.M G₁.M e ei ev →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ g ∈ UAt σ G.V (evI F), ∀ (w : Matrix (Fin (b + 2)) (Fin (b + 2 + a')) (AE F E)) (f : SInf F (Fin (b + 2) × Fin (b + 2 + a'))),
      locOpInf (om (g, 1)) (locOpInf (G.M.co.rho B.ψ (partInf F w)) f) =
        locOpInf (G.M.co.rho B.ψ (partInf F (actAB (cA σ) ((g, 1) : UA σ G.V.J × UA σ G.W.J) w))) (locOpInf (om (g, 1)) f) := by
  first | exact @GlobalTheory.ThK.LemF.InfMove.weil_moves_rho_inf | exact GlobalTheory.ThK.LemF.InfMove.weil_moves_rho_inf | (intros; apply GlobalTheory.ThK.LemF.InfMove.weil_moves_rho_inf <;> assumption)
