import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilOperatorContinuous
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocOpInfMul
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_weil_operator_continuous : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ f : SInf F (Fin a' × Fin (a + a')), ContinuousOn (fun g => locOpInf (om' (g, 1)) f) (UAt σ G.V' (evI F)) := by
  first | exact @GlobalTheory.ThK.WeilCont.weilcont | exact GlobalTheory.ThK.WeilCont.weilcont | (intros; apply GlobalTheory.ThK.WeilCont.weilcont <;> assumption)
