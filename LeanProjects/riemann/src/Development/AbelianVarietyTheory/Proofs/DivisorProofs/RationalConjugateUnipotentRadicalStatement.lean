import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalConjugateUnipotentRadical
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
theorem _root_.GlobalTheory.T.rational_conjugate_unipotent_radical : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n r : ℕ) (J : Matrix (Fin n) (Fin n) E) (γ : GRat σ J) (C₀ C : Matrix (Fin n) (Fin r) E)
    (D D' : Matrix (Fin r) (Fin r) E), D * D' = 1 → D' * D = 1 → (γ.1 : Matrix (Fin n) (Fin n) E) * C₀ = C * D →
      ∀ g ∈ unipRad σ J C₀, ratEmb σ J γ * g * (ratEmb σ J γ)⁻¹ ∈ unipRad σ J C := by
  first | exact @GlobalTheory.CuspConjRad.conj_mem_unipRad | exact GlobalTheory.CuspConjRad.conj_mem_unipRad | (intros; apply GlobalTheory.CuspConjRad.conj_mem_unipRad <;> assumption)
