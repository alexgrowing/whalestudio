import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicLineScalarCharacter
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocOpInfMul
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_line_scalar_character : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ p ∈ UAt σ G.V' (evI F), ∀ t : (AE F E)ˣ, mat p *ᵥ incV F H.x = t.1 • incV F H.x →
      t ∈ idelesAt E (evI F) ∧ ∃ (n m : UA σ G.V'.J) (g₀ : UA σ G₁.V'.J), n ∈ unip σ G.V' H ∧ n ∈ UAt σ G.V' (evI F) ∧
        IsLevi (W₁ := G₁.V') H t g₀ m ∧ m ∈ UAt σ G.V' (evI F) ∧ g₀ ∈ UAt σ G₁.V' (evI F) ∧ p = n * m := by
  first | exact @GlobalTheory.LineStabLevi.stab_line_levi | exact GlobalTheory.LineStabLevi.stab_line_levi | (intros; apply GlobalTheory.LineStabLevi.stab_line_levi <;> assumption)
