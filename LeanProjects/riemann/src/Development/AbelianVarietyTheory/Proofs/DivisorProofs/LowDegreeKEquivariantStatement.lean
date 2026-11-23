import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowDegreeKEquivariant
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartCompactStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartFiniteDimensionalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLinePolynomialEquivarianceStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.low_degree_K_equivariant : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
      ∀ k : ℕ, lowDegInf B G.M R.p ≤ k → ∀ S : R.Pi →ₗ[ℂ] R.Pi, KEqOn B G.M om R.p (lowPartInf B G.M R.p) S →
        (∀ x ∈ lowPartInf B G.M R.p, S x ∈ (fockDeg G.M B.ψ B.emb (k + 1)).map R.p) →
          ∀ x ∈ lowPartInf B G.M R.p, S x ∈ (fockDeg G.M B.ψ B.emb k).map R.p := by
  first | exact @GlobalTheory.LowKStep.map_mem_fockDeg_of_succ | exact GlobalTheory.LowKStep.map_mem_fockDeg_of_succ | (intros; apply GlobalTheory.LowKStep.map_mem_fockDeg_of_succ <;> assumption)
