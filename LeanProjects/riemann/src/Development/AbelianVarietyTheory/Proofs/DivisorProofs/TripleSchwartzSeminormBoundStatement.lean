import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleSchwartzSeminormBound
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOpMemDStep
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_schwartz_seminorm_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), GlobalTheory.FunPr.Hypotheses₂ →
    ∀ (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ K : Subgroup (UA σ G.V.J), IsStab B K → ∀ s : Finset (ℕ × ℕ), ∃ (s' : Finset (ℕ × ℕ)) (C : ℝ), ∀ k ∈ KAt K (evI F),
      ∀ f : SInf F (Fin a × Fin (a + a')),
        (s.sup (schwartzSeminormFamily ℂ (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) ℂ)) (locOpInf (om (k, 1)) f) ≤
          C * (s'.sup (schwartzSeminormFamily ℂ (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) ℂ)) f := by
  first | exact @GlobalTheory.ArchKXPr.locOpInf_unif_bound | exact GlobalTheory.ArchKXPr.locOpInf_unif_bound | (intros; apply GlobalTheory.ArchKXPr.locOpInf_unif_bound <;> assumption)
