import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDegreeKFixedReduction
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixPartEqBotOfLt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_degree_k_fixed_reduction : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
      ∀ k : ℕ, ∀ f ∈ fockDeg G.M B.ψ B.emb (fixDeg B G.M om + 2 * k + 2), IsKFix B om f →
        f ∈ fockDeg G.M B.ψ B.emb (fixDeg B G.M om + 2 * k + 1) ⊔ Submodule.span ℂ
          {f₁ | ∃ γ ∈ Lines σ G.W, ∃ g ∈ fockDeg G.M B.ψ B.emb (fixDeg B G.M om + 2 * k + 1), IsKFix B om g ∧
            ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) g f₁} := by
  first | exact @GlobalTheory.EvenStep.even_step | exact GlobalTheory.EvenStep.even_step | (intros; apply GlobalTheory.EvenStep.even_step <;> assumption)
