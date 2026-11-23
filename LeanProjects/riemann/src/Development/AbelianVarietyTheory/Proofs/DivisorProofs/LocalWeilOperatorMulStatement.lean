import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilOperatorMul
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocOpInfMul
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_weil_operator_mul : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ p ∈ UAt σ G.V' (evI F), ∀ g ∈ UAt σ G.V' (evI F), ∀ f : SInf F (Fin a' × Fin (a + a')),
      locOpInf (om' (p * g, 1)) f = locOpInf (om' (p, 1)) (locOpInf (om' (g, 1)) f) := by
  first | exact @GlobalTheory.ThK.InfB.locOpInf_mul_V' | exact GlobalTheory.ThK.InfB.locOpInf_mul_V' | (intros; apply GlobalTheory.ThK.InfB.locOpInf_mul_V' <;> assumption)
