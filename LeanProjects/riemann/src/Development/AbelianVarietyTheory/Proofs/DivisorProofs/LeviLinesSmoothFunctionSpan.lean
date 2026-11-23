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
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC
open GlobalTheory.Orb (archMat)

namespace GlobalTheory.LeviHC.LineLie

theorem lineDer_sum_smul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) (f : GAd σ J → ℂ), GlobalTheory.UAut.IsSm σ J f →
    ∀ (ι : Type) [Fintype ι] (Y : ι → Matrix (Fin n) (Fin n) ℂ) (δ : ι → ℝ → GAd σ J) (c : ι → ℝ) (γ : ℝ → GAd σ J),
      (∀ j, GlobalTheory.LeviHC.IsLineOf σ J τ (Y j) (δ j)) → GlobalTheory.LeviHC.IsLineOf σ J τ (∑ j, c j • Y j) γ →
      GlobalTheory.SiegelSet.lineDer γ f = ∑ j, (c j : ℂ) • GlobalTheory.SiegelSet.lineDer (δ j) f := by
  intro F E _ _ _ _ _ σ h n J hJ w τ f hf ι _ Y δ c γ hδ hγ
  classical
  have hsm : ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (β : ℝ → GAd σ J) (a : ℝ), IsLineOf σ J τ Z β →
      lineDer (fun t => β (t * a)) f = (a : ℂ) • lineDer β f := by
    intro Z β a hβ
    funext g
    have hd := ((differentiable_of_isSm hf (hβ.isRealLine h) g) (0 * a)).hasDerivAt.scomp (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).mul_const a)
    have := hd.deriv
    simp only [zero_mul, one_mul] at this
    simpa [lineDer, Function.comp_def] using this
  have key : ∀ s : Finset ι, (∃ β, IsLineOf σ J τ (∑ j ∈ s, c j • Y j) β) ∧
      ∀ β, IsLineOf σ J τ (∑ j ∈ s, c j • Y j) β → lineDer β f = ∑ j ∈ s, (c j : ℂ) • lineDer (δ j) f := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨exists_isLineOf h hJ (by simp), fun β hβ => ?_⟩
      rw [Finset.sum_empty] at hβ ⊢
      have h0 := hβ.smul 0
      rw [smul_zero] at h0
      rw [hβ.unique h h0, hsm _ _ _ hβ]
      simp
    | insert i s hi ih =>
      obtain ⟨⟨β₀, hβ₀⟩, ih⟩ := ih
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      have h1 := (hδ i).smul (c i)
      refine ⟨exists_isLineOf h hJ ?_, fun β hβ => ?_⟩
      · rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, h1.skew h, hβ₀.skew h,
          add_zero]
      · rw [(lineDer_add_bracket F E σ h n J hJ w τ f hf _ _ _ _ β h1 hβ₀).1 hβ, hsm _ _ _ (hδ i), ih _ hβ₀]
  exact (key Finset.univ).2 γ hγ

end GlobalTheory.LeviHC.LineLie
