import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDegreeEvenMapLe
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
theorem _root_.GlobalTheory.T.fock_degree_even_map_le : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
      ∀ j : ℕ, (fockDeg G.M B.ψ B.emb (lowDegInf B G.M R.p + 2 * j + 2)).map R.p ≤
        (fockDeg G.M B.ψ B.emb (lowDegInf B G.M R.p + 2 * j)).map R.p ⊔
          Submodule.span ℂ {x : R.Pi | ∃ γ ∈ Lines σ G.W, ∃ f ∈ fockDeg G.M B.ψ B.emb (lowDegInf B G.M R.p + 2 * j),
            ∃ f₁ : SInf F (Fin a × Fin (a + a')), ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ ∧ x = R.p f₁} := by
  first | exact @GlobalTheory.LieGenStep.map_fockDeg_add_two_le | exact GlobalTheory.LieGenStep.map_fockDeg_add_two_le | (intros; apply GlobalTheory.LieGenStep.map_fockDeg_add_two_le <;> assumption)
