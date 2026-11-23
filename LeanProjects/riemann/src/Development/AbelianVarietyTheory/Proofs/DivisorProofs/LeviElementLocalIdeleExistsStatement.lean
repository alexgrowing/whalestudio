import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviElementLocalIdeleExists
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeEvFun
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_element_local_idele_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ v : Pl F,
    ∃ m : (AE F E)ˣ → UA σ G.V.J, ∀ t ∈ idelesAt E (evFin F v),
      IsLevi H t (1 : UA σ G₁.V.J) (m t) ∧ m t ∈ UAt σ G.V (evFin F v) := by
  first | exact @GlobalTheory.PlaneLeviHermAt.exists_isLevi_herm_at | exact GlobalTheory.PlaneLeviHermAt.exists_isLevi_herm_at | (intros; apply GlobalTheory.PlaneLeviHermAt.exists_isLevi_herm_at <;> assumption)
