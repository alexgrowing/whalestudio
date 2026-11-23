import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinEvaluationTripleTorus
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittCharacterConjugateInverse

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_evaluation_triple_torus : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b)
    (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
      ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      ∀ (t : (AE F E)ˣ) (m : UA σ G.W.J), IsLevi (W₁ := G₁.W) H' t 1 m →
        ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))),
          e' (om' (1, m) Ψ) = ((X.α t : ℂ) * (((absE F E t : ℝ) ^ ((b : ℝ) / 2) : ℝ) : ℂ)) • e' Ψ := by
  first | exact @GlobalTheory.ThK.TorusEvB.torus_evB | exact GlobalTheory.ThK.TorusEvB.torus_evB | (intros; apply GlobalTheory.ThK.TorusEvB.torus_evB <;> assumption)
