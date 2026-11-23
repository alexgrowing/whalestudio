import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviCharacterExponentArchimedean
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Definitions.Divisors.GenSubHwOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAThetaLiftCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAThetaLocalFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartInvariantSubmoduleEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviLiftMaximalCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockSpaceStableArchimedeanMaximalCompaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwinerOfCoef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeadMinorMulDiagonal
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_character_exponent_archimedean : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (d d₁ r s i₀ i₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁), IsCMExt F E σ →
    W.IsSkew σ B r s → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ (χ : Chr F E) (m : InfinitePlace F → ℤ), HasExp B.emb χ m →
    ∀ (z : ℝ) (t : (AE F E)ˣ) (h₁ : UA σ W₁.J) (k : UA σ W.J), k ∈ KInf σ W B.emb → IsLevi H' t h₁ k →
      (χ t : ℂ) * (((absE F E t : ℝ) ^ z : ℝ) : ℂ) = ∏ w, piInf (B.emb w) t.1 ^ m w := by
  first | exact @GlobalTheory.ThK.LeviChar.char_levi_KInf | exact GlobalTheory.ThK.LeviChar.char_levi_KInf | (intros; apply GlobalTheory.ThK.LeviChar.char_levi_KInf <;> assumption)
