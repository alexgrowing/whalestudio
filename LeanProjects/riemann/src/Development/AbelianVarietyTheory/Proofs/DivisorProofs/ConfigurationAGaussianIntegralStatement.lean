import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigurationAGaussianIntegral
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOpMemDStep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.ThK.EvAt0.PolD GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.configuration_a_gaussian_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), CfgA B G G₁ H H' → IsTriple B G X om om' →
    ∀ g, GaussD G.M B.emb g → ∀ (y : Fin (b + 2) → AE F E) (z : Fin (b + a') → AE F E),
      ∃ (y₁ : Fin (b + 2) → AE F E) (z₁ : Fin (b + a') → AE F E),
        dOp (coordI G.M (Matrix.vecMulVec y (incV F H'.y) + Matrix.vecMulVec (incV F H.y) (incM F H'.ι *ᵥ z))).1
          (coordI G.M (Matrix.vecMulVec y (incV F H'.y) + Matrix.vecMulVec (incV F H.y) (incM F H'.ι *ᵥ z))).2 g =
        (-Complex.I) • dOp (coordI G.M (Matrix.vecMulVec y₁ (incV F H'.x) + Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z₁))).1
          (coordI G.M (Matrix.vecMulVec y₁ (incV F H'.x) + Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z₁))).2 g := by
  first | exact @GlobalTheory.ThK.VacDualPart.dOp_dual_vac | exact GlobalTheory.ThK.VacDualPart.dOp_dual_vac | (intros; apply GlobalTheory.ThK.VacDualPart.dOp_dual_vac <;> assumption)
