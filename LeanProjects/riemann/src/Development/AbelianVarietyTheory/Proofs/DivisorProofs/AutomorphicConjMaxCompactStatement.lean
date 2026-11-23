import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicConjMaxCompact
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphic_conj_max_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E),
      GlobalTheory.SiegelSet.IsWittFrame σ J X Y → ∀ (K₁ K₂ : Subgroup (GAd σ J)) (a : GAd σ J), a ∈ GlobalTheory.AdelicU.infPts σ J →
        (∀ k, k ∈ K₂ ↔ a * k * a⁻¹ ∈ K₁) → ∀ (S : Finset (Fin r)) (φ : GAd σ J → ℂ),
          GlobalTheory.StdPar.IsCuspComp σ J X Y S K₁ φ 0 → GlobalTheory.StdPar.IsCuspComp σ J X Y S K₂ φ 0 := by
  first | exact @GlobalTheory.StdPar.RealConj.isCuspComp_zero_realConj | exact GlobalTheory.StdPar.RealConj.isCuspComp_zero_realConj | (intros; apply GlobalTheory.StdPar.RealConj.isCuspComp_zero_realConj <;> assumption)
