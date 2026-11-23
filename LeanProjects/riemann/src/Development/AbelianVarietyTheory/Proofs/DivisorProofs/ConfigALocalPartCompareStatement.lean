import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalPartCompare
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_A_local_part_compare : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, IsLocPart G.M G₁.M e ei ev →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (l : (AE F E)ˣ) (m : UA σ G.V.J), l ∈ idelesAt E (evI F) → IsLevi (W₁ := G₁.V) H l 1 m → m ∈ UAt σ G.V (evI F) →
      ∀ f : SInf F (Fin (b + 2) × Fin (b + 2 + a')),
        ei (locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' 1))) (locOpInf (om (m, 1)) f)) =
          (((X.ν l : ℂ))⁻¹ * (((absE F E l : ℝ) ^ (((b + a' : ℕ) : ℝ) / 2) : ℝ) : ℂ)) •
            ei (locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' l⁻¹))) f) := by
  first | exact @GlobalTheory.ShiftInfA.evShift_levi | exact GlobalTheory.ShiftInfA.evShift_levi | (intros; apply GlobalTheory.ShiftInfA.evShift_levi <;> assumption)
