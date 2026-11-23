import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationDetOne
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationSplitPlaceSkewHermitianUnitar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlaceSplitsCompletelyNotMemEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNormOneIdeles
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LiftConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strong_approximation_det_one : GlobalTheory.Published.StrongApproxSU → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n : ℕ) (V : Spc F E n) (r s : ℕ), B.IsGood σ → V.IsHerm σ B r s → 2 ≤ n → ∀ v : Pl F, Nonempty (E →ₐ[F] Fv F v) →
    ∀ g : UA σ V.J, (mat g).det = 1 → g ∈ closure {x | ∃ γ ∈ ratU σ V.J, ∃ k ∈ UAt σ V (evFin F v), x = γ * k} := by
  first | exact @GlobalTheory.SplitApprox.strongApprox_split_herm | exact GlobalTheory.SplitApprox.strongApprox_split_herm | (intros; apply GlobalTheory.SplitApprox.strongApprox_split_herm <;> assumption)
