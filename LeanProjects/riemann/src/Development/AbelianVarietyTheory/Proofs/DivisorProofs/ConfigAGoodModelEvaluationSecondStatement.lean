import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAGoodModelEvaluationSecond
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
theorem _root_.GlobalTheory.T.stronglyMeasurable_iteratedFDeriv_coneInfInt_shiftA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), GlobalTheory.FunPr.Hypotheses₂ →
    ∀ (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    CfgA B G G₁ H H' → IsTriple B G X om om' → G₁.M.IsGood B.ψ →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ),
      ei ≠ 0 → (∀ v, ev v (G.M.vac v) = G₁.M.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K → ∀ (z : ℕ) (f : SInf F (Fin (b + 2) × Fin (b + 2 + a'))) (n : ℕ) (y : Fin b × Fin (b + a') → mixedEmbedding.mixedSpace F),
      StronglyMeasurable (Function.uncurry fun (k : KAt K (evI F)) (l : idelesAt E (evI F)) =>
        iteratedFDeriv ℝ n (⇑(coneInfInt B G.M om ei (shiftA H H') X.ν z f k.1 l.1)) y) := by
  first | exact @GlobalTheory.ThK.ConeInfDerivMeas.stronglyMeasurable_iteratedFDeriv_coneInfInt | exact GlobalTheory.ThK.ConeInfDerivMeas.stronglyMeasurable_iteratedFDeriv_coneInfInt | (intros; apply GlobalTheory.ThK.ConeInfDerivMeas.stronglyMeasurable_iteratedFDeriv_coneInfInt <;> assumption)
