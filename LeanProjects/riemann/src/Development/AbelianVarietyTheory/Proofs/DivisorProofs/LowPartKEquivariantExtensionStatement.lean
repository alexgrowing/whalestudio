import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartKEquivariantExtension
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
theorem _root_.GlobalTheory.T.low_part_K_equivariant_extension : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
      ∀ j : ℕ, ∀ S : R.Pi →ₗ[ℂ] R.Pi, KEqOn B G.M om R.p (lowPartInf B G.M R.p) S →
        (∀ x ∈ lowPartInf B G.M R.p, S x ∈ (fockDeg G.M B.ψ B.emb (lowDegInf B G.M R.p + 2 * j)).map R.p ⊔
          Submodule.span ℂ {x : R.Pi | ∃ γ ∈ Lines σ G.W, ∃ f ∈ fockDeg G.M B.ψ B.emb (lowDegInf B G.M R.p + 2 * j),
            ∃ f₁ : SInf F (Fin a × Fin (a + a')), ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ ∧ x = R.p f₁}) →
        ∀ x ∈ lowPartInf B G.M R.p, S x ∈ (fockDeg G.M B.ψ B.emb (lowDegInf B G.M R.p + 2 * j)).map R.p := by
  first | exact @GlobalTheory.DegKeep.map_mem_fockDeg_of_lie | exact GlobalTheory.DegKeep.map_mem_fockDeg_of_lie | (intros; apply GlobalTheory.DegKeep.map_mem_fockDeg_of_lie <;> assumption)
