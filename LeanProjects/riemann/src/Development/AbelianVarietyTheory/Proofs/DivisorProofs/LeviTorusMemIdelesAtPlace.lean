import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarMemIdelesAtOfIsLevi

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.LeviScalarConjAt

theorem scalar_and_conj_mem_idelesAt_of_isLevi :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (v : Pl F) t (h₁ : UA σ G₁.W.J) m, IsLevi H' t h₁ m → m ∈ UAt σ G.W (evFin F v) →
      t ∈ idelesAt E (evFin F v) ∧ Units.map (cA σ : AE F E →* AE F E) t ∈ idelesAt E (evFin F v) := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC v t h₁ m hL hm
  have ht : t ∈ idelesAt E (evFin F v) :=
    GlobalTheory.LeviScalarAt.scalar_mem_idelesAt_of_isLevi B H' 0 (b + 1) hC.hH' v t h₁ m hL hm
  refine ⟨ht, ?_⟩
  rw [mem_idelesAt] at ht ⊢
  intro u hu
  have e : ((Units.map (cA σ : AE F E →* AE F E) t : (AE F E)ˣ) : AE F E) - 1 = cA σ ((t : AE F E) - 1) := by
    rw [Units.coe_map, map_sub, map_one]
    rfl
  rw [e, ← map_smul, ht u hu, map_zero]

end GlobalTheory.LeviScalarConjAt
