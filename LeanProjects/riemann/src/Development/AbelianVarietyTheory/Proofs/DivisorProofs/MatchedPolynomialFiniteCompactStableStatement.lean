import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPolynomialFiniteCompactStable
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matched_polynomial_finite_compact_stable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    GlobalTheory.ThK.KP → IsMatched B G X om om' R Rf → ∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' → ∀ k ∈ finK σ G.W B.emb,
      om' (1, k) Φ' ∈ G.M'.So B.ψ B.τ₁ ∧ PolMatch B G X R Rf (om (1, k) Φ) (om' (1, k) Φ') := by
  first | exact @GlobalTheory.ThK.DescB.FinKMatch.translate_matched | exact GlobalTheory.ThK.DescB.FinKMatch.translate_matched | (intros; apply GlobalTheory.ThK.DescB.FinKMatch.translate_matched <;> assumption)
