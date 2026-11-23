import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviTorusMemIdelesAtPlace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_torus_mem_ideles_at_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (v : Pl F) t (h₁ : UA σ G₁.W.J) m, IsLevi H' t h₁ m → m ∈ UAt σ G.W (evFin F v) →
      t ∈ idelesAt E (evFin F v) ∧ Units.map (cA σ : AE F E →* AE F E) t ∈ idelesAt E (evFin F v) := by
  first | exact @GlobalTheory.LeviScalarConjAt.scalar_and_conj_mem_idelesAt_of_isLevi | exact GlobalTheory.LeviScalarConjAt.scalar_and_conj_mem_idelesAt_of_isLevi | (intros; apply GlobalTheory.LeviScalarConjAt.scalar_and_conj_mem_idelesAt_of_isLevi <;> assumption)
