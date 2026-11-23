import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigATripleThetaLift
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InsP

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone GlobalTheory.EvZeroStd
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_A_triple_theta_lift : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ v : B.P,
      (∀ z : Matrix (Fin a') (Fin (b + a')) (AE F E),
        GlobalTheory.FlipMatch.coX (B.τ v) (G.V'.bas v) (G.W.bas v) (incM F (1 : Matrix (Fin a') (Fin a') E) * z * (incM F H'.ι)ᵀ) =
                     GlobalTheory.FlipMatch.coX (B.τ v) (G₁.V'.bas v) (G₁.W.bas v) z * (insP (Fv F v) b a')ᵀ ∧
        GlobalTheory.FlipMatch.coY σ G.V' G.W (B.τ v) (G.V'.bas v) (G.W.bas v)
                     (incM F (1 : Matrix (Fin a') (Fin a') E) * z * (incM F H'.ι)ᵀ) =
          GlobalTheory.FlipMatch.coY σ G₁.V' G₁.W (B.τ v) (G₁.V'.bas v) (G₁.W.bas v) z * (insP (Fv F v) b a')ᵀ) ∧
      ∀ s r : Fin a' → Fv F v, ∃ y : Fin a' → AE F E, At (evFin F v) (Matrix.vecMulVec y (incV F H'.x)) ∧
        GlobalTheory.FlipMatch.coX (B.τ v) (G.V'.bas v) (G.W.bas v) (Matrix.vecMulVec y (incV F H'.x)) =
          Matrix.vecMulVec s (Pi.single 0 1) ∧
        GlobalTheory.FlipMatch.coY σ G.V' G.W (B.τ v) (G.V'.bas v) (G.W.bas v) (Matrix.vecMulVec y (incV F H'.x)) =
          Matrix.vecMulVec r (Pi.single ⟨b + 1, by omega⟩ 1) := by
  first | exact @GlobalTheory.EvZeroCoords.coords_evZero | exact GlobalTheory.EvZeroCoords.coords_evZero | (intros; apply GlobalTheory.EvZeroCoords.coords_evZero <;> assumption)
