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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationsCommuteDistinctPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeApproximationUpwardIdele
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.LeviHC.LineBracket

open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {w : InfinitePlace F}

theorem exists_isLineOf_emb (h : IsCMExt F E σ) {τ' : EmbOver E w} {Z' : Matrix (Fin n) (Fin n) ℂ} {δ : ℝ → GAd σ J}
    (hδ : IsLineOf σ J τ' Z' δ) (τ : EmbOver E w) : ∃ Z, IsLineOf σ J τ Z δ := by
  have hadd := GlobalTheory.SiegelSet.isRealLine_add F E σ h _ J δ (hδ.isRealLine h)
  have hc := GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ h _ J δ (hδ.isRealLine h)
  have h0 : δ 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  obtain ⟨Z, hZ⟩ := GlobalTheory.OneParamMatrix.eq_exp_of_continuous_oneParameter
    (fun t => GlobalTheory.Orb.archMat σ J τ (projArch σ J w (δ t)))
    ((GlobalTheory.Orb.continuous_archMat σ J τ).comp ((continuous_projArch σ J w).comp hc))
    (by simp only [h0, map_one]) (fun s t => by simp only [hadd, map_mul])
  refine ⟨Z, fun t => ⟨projArch σ J w (δ t), ?_, hZ t⟩⟩
  obtain ⟨y, e, -⟩ := hδ t
  rw [e, projArch_embArch_self]

theorem exists_line_bracket : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ γ δ : ℝ → GAd σ J, GlobalTheory.SiegelSet.IsRealLine σ J γ → GlobalTheory.SiegelSet.IsRealLine σ J δ →
      ∃ ε : ℝ → GAd σ J, GlobalTheory.SiegelSet.IsRealLine σ J ε ∧ ∀ f, GlobalTheory.UAut.IsSm σ J f →
        GlobalTheory.SiegelSet.lineDer γ (GlobalTheory.SiegelSet.lineDer δ f) =
          GlobalTheory.SiegelSet.lineDer δ (GlobalTheory.SiegelSet.lineDer γ f) + GlobalTheory.SiegelSet.lineDer ε f := by
  intro F E _ _ _ _ _ σ h n J hJ γ δ ⟨w, τ, X, hX, hγ⟩ ⟨w', τ', Z', _, hδ'⟩
  replace hγ : IsLineOf σ J τ X γ := hγ
  replace hδ' : IsLineOf σ J τ' Z' δ := hδ'
  by_cases hw : w = w'
  · subst hw
    obtain ⟨X', hδ⟩ := exists_isLineOf_emb h hδ' τ
    have hX' := hδ.skew h
    obtain ⟨ε, hε⟩ := exists_isLineOf (τ := τ) (Z := X * X' - X' * X) h hJ (by
      have e1 := eq_neg_of_add_eq_zero_left hX
      have e2 := eq_neg_of_add_eq_zero_left hX'
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.sub_mul, Matrix.mul_assoc,
        Matrix.mul_assoc, e1, e2, Matrix.mul_neg, Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, e2,
        Matrix.mul_sub]
      simp [Matrix.mul_assoc])
    refine ⟨ε, hε.isRealLine h, fun f hf => ?_⟩
    rw [(LineLie.lineDer_add_bracket F E σ h n J hJ w τ f hf X X' γ δ ε hγ hδ).2 hε, add_sub_cancel]
  · have h1 : IsLineOf σ J τ 0 fun _ => 1 := fun t => ⟨1, (map_one _).symm, by
      rw [map_one, smul_zero, NormedSpace.exp_zero]⟩
    refine ⟨fun _ => 1, h1.isRealLine h, fun f hf => ?_⟩
    rw [PlaceComm.lineDer_comm h hw hγ hδ' hf]
    funext g
    simp [GlobalTheory.SiegelSet.lineDer]

end GlobalTheory.LeviHC.LineBracket

end
