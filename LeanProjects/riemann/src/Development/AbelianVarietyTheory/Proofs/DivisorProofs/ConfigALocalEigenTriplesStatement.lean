import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalEigenTriples
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeEvFun
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_a_local_eigen_triples : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, IsLocPart G.M G₁.M e ei ev →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (l : ((Fin b × Fin (b + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ),
      (∀ g₀ ∈ UAt σ G₁.V (evFin F v), ∀ ψ ∈ SB (Fin b × Fin (b + a') → Fv F v), l (locOp v (om₁ (g₀, 1)) ψ) = l ψ) →
      ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
        (∀ q ∈ UAt σ G.V (evFin F v), mat q *ᵥ incV F H.x = incV F H.x → ∀ x ∈ UAt σ G.V (evFin F v),
          coneEvFun B G H H' om v (ev v) l φ (q * x) = coneEvFun B G H H' om v (ev v) l φ x) ∧
        (∀ g ∈ UAt σ G.V (evFin F v), ∀ x ∈ UAt σ G.V (evFin F v),
          coneEvFun B G H H' om v (ev v) l (locOp v (om (g, 1)) φ) x = coneEvFun B G H H' om v (ev v) l φ (x * g)) ∧
        Continuous (fun x : UAtSub σ G.V (evFin F v) => coneEvFun B G H H' om v (ev v) l φ x.1) := by
  first | exact @GlobalTheory.ThK.EvFunProps.evFunProps | exact GlobalTheory.ThK.EvFunProps.evFunProps | (intros; apply GlobalTheory.ThK.EvFunProps.evFunProps <;> assumption)
