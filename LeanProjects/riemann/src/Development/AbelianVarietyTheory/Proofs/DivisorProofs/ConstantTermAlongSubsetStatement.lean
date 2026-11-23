import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAlongSubset
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
theorem _root_.GlobalTheory.T.constant_term_along_subset : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ φ : GAd σ J → ℂ, Continuous φ → (∀ γ ∈ ratPts σ J, ∀ g, φ (γ * g) = φ g) → ∀ S T : Finset (Fin r), T ⊆ S →
        GlobalTheory.StdPar.IsConstAlong σ J X T φ 0 → GlobalTheory.StdPar.IsConstAlong σ J X S φ 0 := by
  first | exact @GlobalTheory.ConstTrans.isConstAlong_zero_of_subset | exact GlobalTheory.ConstTrans.isConstAlong_zero_of_subset | (intros; apply GlobalTheory.ConstTrans.isConstAlong_zero_of_subset <;> assumption)
