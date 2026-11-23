import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSpanConjugateInvariant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsLeSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_span_conjugate_invariant : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf → ∀ (hσ : ∀ x, σ (σ x) = x) (c : E) (hc : c ≠ 0), σ c = -c →
    ∀ f ∈ thetaSpanV B G X om R Rf ⊔ thetaSpanV' B G X om' R Rf,
    ∀ K : Subgroup (GAd σ (c • G.W.J.map σ)), (∀ x ∈ K, (toGAd hσ G.W.J hc).symm x ∈ KInf σ G.W B.emb) →
      IsAut σ (c • G.W.J.map σ) K (fun x => f ((toGAd hσ G.W.J hc).symm x)) := by
  first | exact @GlobalTheory.ThKSpanAut.isAut_of_mem_thetaSpan_sup | exact GlobalTheory.ThKSpanAut.isAut_of_mem_thetaSpan_sup | (intros; apply GlobalTheory.ThKSpanAut.isAut_of_mem_thetaSpan_sup <;> assumption)
