import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerFixesIsotropicVector
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeEvFun
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_fixes_isotropic_vector : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (q : UA σ G.V.J), q ∈ UAt σ G.V (evFin F v) → mat q *ᵥ incV F H.x = incV F H.x →
      ∃ u ∈ unip σ G.V H, u ∈ UAt σ G.V (evFin F v) ∧ ∃ (g₀ : UA σ G₁.V.J) (g : UA σ G.V.J), IsLevi H 1 g₀ g ∧
        g ∈ UAt σ G.V (evFin F v) ∧ g₀ ∈ UAt σ G₁.V (evFin F v) ∧ q = u * g := by
  first | exact @GlobalTheory.ThK.LemF.StabDec.stab_decomp | exact GlobalTheory.ThK.LemF.StabDec.stab_decomp | (intros; apply GlobalTheory.ThK.LemF.StabDec.stab_decomp <;> assumption)
