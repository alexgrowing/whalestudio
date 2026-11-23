import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedRealFrameTwistedCoeffs
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
theorem _root_.GlobalTheory.T.adapted_real_frame_twisted_coeffs : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (d d₁ r s i₀ i₁ R S : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁), IsCMExt F E σ →
    W.IsSkew σ B r s → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ (A : Fin (R + 1)) (w : InfinitePlace F)
    (C : Matrix (Fin d₁) (Formalism.BasicNotions.TH.Ix R S) ℂ), GlobalTheory.ThK.RealK.IsAdapted B.emb w W₁ C →
    ∃ ε φ : Fin d → ℂ, GlobalTheory.ThK.RealK.IsAdapted B.emb w W (GlobalTheory.TwCoef.extFrame A (H'.ι.map (B.emb w).1 * C) ε φ) ∧
      ∀ (t : (AE F E)ˣ) (h₁ : UA σ W₁.J) (k : UA σ W.J), k ∈ KInf σ W B.emb → IsLevi H' t h₁ k →
        (mat k).map (piInf (B.emb w)) *ᵥ ε = piInf (B.emb w) t.1 • ε ∧
        (mat k).map (piInf (B.emb w)) *ᵥ φ = piInf (B.emb w) t.1 • φ := by
  first | exact @GlobalTheory.TwCoefFrame.exists_extFrame_adapted | exact GlobalTheory.TwCoefFrame.exists_extFrame_adapted | (intros; apply GlobalTheory.TwCoefFrame.exists_extFrame_adapted <;> assumption)
