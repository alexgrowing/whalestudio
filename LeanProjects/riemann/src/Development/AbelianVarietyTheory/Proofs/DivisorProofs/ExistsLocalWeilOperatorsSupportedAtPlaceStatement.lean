import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalWeilOperatorsSupportedAtPlace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localWeilOperators_supportedAtPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (Γ : Type) [Group Γ] (j : Γ →* UA σ G.V.J × UA σ G.W.J),
      (∀ g, (j g).1 ∈ UAt σ G.V (evFin F v) ∧ (j g).2 ∈ UAt σ G.W (evFin F v)) →
      ∃ ω : Γ →* Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v)), ∀ g (φ : SB (Fin a × Fin (a + a') → Fv F v))
        (φ₁ : (Fin a × Fin (a + a') → Fv F v) → ℂ),
        Acts (evFin F v) (om (j g)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) φ₁ ↔
          φ₁ = ((ω g φ : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ) := by
  first | exact @GlobalTheory.LocalWeilOps.local_ops | exact GlobalTheory.LocalWeilOps.local_ops | (intros; apply GlobalTheory.LocalWeilOps.local_ops <;> assumption)
