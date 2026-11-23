import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFlipMatchSurjective
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
theorem _root_.GlobalTheory.T.local_flip_match_surjective : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E},
    IsCMExt F E σ → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d), X.J.det ≠ 0 → Y.J.det ≠ 0 →
    ∀ {v : Pl F} (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) (P Q : Matrix (Fin n) (Fin d) (Fv F v)),
      ∃ u : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) u ∧ GlobalTheory.FlipMatch.coX t b c u = P ∧
        GlobalTheory.FlipMatch.coY σ X Y t b c u = Q := by
  first | exact @GlobalTheory.SplitCoords.coords_onto | exact GlobalTheory.SplitCoords.coords_onto | (intros; apply GlobalTheory.SplitCoords.coords_onto <;> assumption)
