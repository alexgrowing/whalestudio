import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriplePairPeriodIdentityCaseATwo
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_pair_period_identity_case_a_two : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    CfgA B G G₁ H H' → IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∃ (m : ℕ) (y : Fin m → Fin (b + 2) → AE F E) (K : ℝ), ∀ l : (AE F E)ˣ, l ∈ idelesAt E (evI F) →
      1 + ‖GlobalTheory.ArchUniq.Coord.coordI G.M (shiftA H H' l)‖ + ∑ w, ‖piInf (B.emb w) (l : AE F E)‖ ≤
        K * (1 + ∑ j, |GlobalTheory.ArchUniq.omega (GlobalTheory.ArchUniq.trP F (Fin (b + 2) × Fin (b + 2 + a')))
          (GlobalTheory.ArchUniq.Coord.coordI G.M (shiftA H H' l))
          (GlobalTheory.ArchUniq.Coord.coordI G.M (Matrix.vecMulVec (y j) (incV F H'.x)))|) := by
  first | exact @GlobalTheory.ConeCoords.main | exact GlobalTheory.ConeCoords.main | (intros; apply GlobalTheory.ConeCoords.main <;> assumption)
