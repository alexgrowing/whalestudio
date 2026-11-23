import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSkewScalarSelfDualAtPlace
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicStabilizerInertPlace
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_skew_scalar_self_dual_at_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (d r s : ℕ) (W : Spc F E d), B.IsGood σ → W.IsSkew σ B r s → ∀ v : Pl F,
    IsEmpty (E →ₐ[F] Fv F v) → ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ ∧ IsSelfDualAt σ (δ • W.Jᵀ) W.L v := by
  first | exact @GlobalTheory.SkewSelfDualInert.skew_isSelfDualAt_inert | exact GlobalTheory.SkewSelfDualInert.skew_isSelfDualAt_inert | (intros; apply GlobalTheory.SkewSelfDualInert.skew_isSelfDualAt_inert <;> assumption)
