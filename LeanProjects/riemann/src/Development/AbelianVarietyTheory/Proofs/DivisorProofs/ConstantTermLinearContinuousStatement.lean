import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermLinearContinuous
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_linear_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E),
      GlobalTheory.SiegelSet.IsWittFrame σ J X Y → ∀ (K : Subgroup (GAd σ J)) (S : Finset (Fin r)) (φ₁ φ₂ : GAd σ J → ℂ) (z : ℂ),
        Continuous φ₁ → Continuous φ₂ → (∀ γ ∈ GlobalTheory.AdelicU.ratPts σ J, ∀ g, φ₁ (γ * g) = φ₁ g) →
        (∀ γ ∈ GlobalTheory.AdelicU.ratPts σ J, ∀ g, φ₂ (γ * g) = φ₂ g) →
        GlobalTheory.StdPar.IsCuspComp σ J X Y S K φ₁ 0 → GlobalTheory.StdPar.IsCuspComp σ J X Y S K φ₂ 0 →
        GlobalTheory.StdPar.IsCuspComp σ J X Y S K (fun g => φ₁ g - z * φ₂ g) 0 := by
  first | exact @GlobalTheory.CuspCompZeroLin.isCuspComp_sub_zero | exact GlobalTheory.CuspCompZeroLin.isCuspComp_sub_zero | (intros; apply GlobalTheory.CuspCompZeroLin.isCuspComp_sub_zero <;> assumption)
