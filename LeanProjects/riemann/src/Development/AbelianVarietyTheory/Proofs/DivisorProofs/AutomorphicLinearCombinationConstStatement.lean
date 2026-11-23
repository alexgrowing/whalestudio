import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicLinearCombinationConst
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphic_linear_combination_const : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (K : Subgroup (GAd σ J)) (S : Finset (Fin r)) (φ₁ φ₂ a₁ a₂ : GAd σ J → ℂ) (z : ℂ),
        GlobalTheory.StdPar.IsAutOn σ J X Y ∅ K φ₁ → GlobalTheory.StdPar.IsAutOn σ J X Y ∅ K φ₂ →
        GlobalTheory.StdPar.IsCuspComp σ J X Y S K φ₁ a₁ → GlobalTheory.StdPar.IsCuspComp σ J X Y S K φ₂ a₂ →
        GlobalTheory.StdPar.IsCuspComp σ J X Y S K (fun g => φ₁ g - z * φ₂ g) (fun g => a₁ g - z * a₂ g) := by
  first | exact @GlobalTheory.CuspCompLin.isCuspComp_sub | exact GlobalTheory.CuspCompLin.isCuspComp_sub | (intros; apply GlobalTheory.CuspCompLin.isCuspComp_sub <;> assumption)
