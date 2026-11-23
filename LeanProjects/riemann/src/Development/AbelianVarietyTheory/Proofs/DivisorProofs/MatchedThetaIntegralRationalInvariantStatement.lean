import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedThetaIntegralRationalInvariant
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftDef
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LiftConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matched_theta_integral_rational_invariant : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
    ∀ Φ₁' ∈ G.M'.So B.ψ B.τ₁, ∀ (μ : Measure (UA σ G.W.J)) (𝓕 : Set (UA σ G.W.J)) (f : UA σ G.W.J → ℂ),
      ∀ γ ∈ ratU σ G.V'.J, ∀ g, thLift om' Φ₁' μ 𝓕 f (γ * g) = thLift om' Φ₁' μ 𝓕 f g := by
  first | exact @GlobalTheory.ThK.LiftConstLeft.thLift_rat_left | exact GlobalTheory.ThK.LiftConstLeft.thLift_rat_left | (intros; apply GlobalTheory.ThK.LiftConstLeft.thLift_rat_left <;> assumption)
