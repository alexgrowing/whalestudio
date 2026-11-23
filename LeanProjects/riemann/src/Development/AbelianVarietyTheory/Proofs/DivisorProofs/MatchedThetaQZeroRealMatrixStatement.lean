import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedThetaQZeroRealMatrix
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
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matched_theta_q_zero_real_matrix : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → G.q = 0 →
    ∀ C : InfinitePlace F → Matrix (Fin (a + a')) (Formalism.BasicNotions.TH.Ix (a + a' - (G.p + G.q)) (G.p + G.q)) ℂ,
      (∀ w, GlobalTheory.ThK.RealK.IsAdapted B.emb w G.W (C w)) →
      ∃ x ∈ lowPartInf B G.M R.p, ∃ ξ : R.Pi →ₗ[ℂ] ℂ, ξ x = 1 ∧
        ∀ k ∈ KInf σ G.W B.emb, ∀ g, GlobalTheory.HwCoef.IsReading B.emb C k g → ∀ f ∈ G.M.Pol B.ψ B.emb, R.p f = x →
          ∀ f₁ : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (1, k)) f f₁ →
            ξ (R.p f₁) = GlobalTheory.HwCoef.hwCoef B a a' G.p g := by
  first | exact @GlobalTheory.LowCoef.exists_low_coef | exact GlobalTheory.LowCoef.exists_low_coef | (intros; apply GlobalTheory.LowCoef.exists_low_coef <;> assumption)
