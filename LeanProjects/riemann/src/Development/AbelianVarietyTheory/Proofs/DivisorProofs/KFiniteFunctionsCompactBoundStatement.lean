import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFiniteFunctionsCompactBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConstAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOfIsSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineToGAdDerivative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDerivativeAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxCompactConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicPlaneConstantTermGrowth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtFoldrLineDer
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.k_finite_functions_compact_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (K : Subgroup (GAd σ J)) (S : Set (GAd σ J)), IsCompact S → (∀ k ∈ S, ∀ k' ∈ K, k * k' ∈ S) →
    ∀ (e : ℕ) (b : Fin e → GAd σ J → ℂ), (∀ j, ContinuousOn (b j) S) →
      (∀ j, ∀ k' ∈ K, ∃ c : Fin e → ℂ, ∀ k ∈ S, b j (k * k') = ∑ l, c l * b l k) →
    ∀ a : GAd σ J → ℂ, (∃ c : Fin e → ℂ, ∀ k ∈ S, a k = ∑ j, c j * b j k) →
      (∀ k ∈ S, ∀ (m : ℕ) (γ : Fin m → ℝ → GAd σ J), (∀ j, GlobalTheory.SiegelSet.IsRealLine σ J (γ j)) → (∀ j s, γ j s ∈ K) →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t : Fin m → ℝ => a (k * (List.ofFn fun j => γ j (t j)).prod)) →
      ∀ l : List (ℝ → GAd σ J), (∀ ζ ∈ l, GlobalTheory.SiegelSet.IsRealLine σ J ζ ∧ ∀ s, ζ s ∈ K) →
        (∃ C : ℝ, ∀ k ∈ S, ‖l.foldr GlobalTheory.SiegelSet.lineDer a k‖ ≤ C) ∧
        ∀ ζ : ℝ → GAd σ J, GlobalTheory.SiegelSet.IsRealLine σ J ζ → (∀ s, ζ s ∈ K) → ∀ k ∈ S,
          DifferentiableAt ℝ (fun t => l.foldr GlobalTheory.SiegelSet.lineDer a (k * ζ t)) 0 := by
  first | exact @GlobalTheory.ThK.KFinCoef.bounded_differentiable_foldr_lineDer | exact GlobalTheory.ThK.KFinCoef.bounded_differentiable_foldr_lineDer | (intros; apply GlobalTheory.ThK.KFinCoef.bounded_differentiable_foldr_lineDer <;> assumption)
