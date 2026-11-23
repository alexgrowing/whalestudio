import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicSubScalarMul
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
theorem _root_.GlobalTheory.T.automorphic_sub_scalar_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E) (S : Finset (Fin r)) (K : Subgroup (GAd σ J))
    (φ₁ φ₂ : GAd σ J → ℂ) (z : ℂ), GlobalTheory.StdPar.IsAutOn σ J X Y S K φ₁ → GlobalTheory.StdPar.IsAutOn σ J X Y S K φ₂ →
      GlobalTheory.StdPar.IsAutOn σ J X Y S K (fun g => φ₁ g - z * φ₂ g) := by
  first | exact @GlobalTheory.StdPar.AutLin.isAutOn_sub_smul | exact GlobalTheory.StdPar.AutLin.isAutOn_sub_smul | (intros; apply GlobalTheory.StdPar.AutLin.isAutOn_sub_smul <;> assumption)
