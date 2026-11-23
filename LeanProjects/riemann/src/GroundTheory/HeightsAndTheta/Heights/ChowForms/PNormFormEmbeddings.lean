import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsNormForm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem NormFormEmbeddings.proof (h : NormFormEval.Statement) : NormFormEmbeddings.Statement := by
  intro K L Ω _ _ _ _ _ _ _ _ _ n η
  have hs : ∀ _ : Fin n, (Set.range (algebraMap K Ω)).Infinite :=
    fun _ => Set.infinite_range_of_injective (algebraMap K Ω).injective
  refine MvPolynomial.funext_set (fun _ => Set.range (algebraMap K Ω)) hs ?_
  intro x hx
  choose u hu using fun m => hx m (Set.mem_univ m)
  obtain rfl : x = algebraMap K Ω ∘ u := funext fun m => (hu m).symm
  have hl : eval (algebraMap K Ω ∘ u) (map (algebraMap K Ω) (normForm K L η)) =
      algebraMap K Ω (eval u (normForm K L η)) := by
    rw [eval_map]
    change _ = algebraMap K Ω (eval₂ (RingHom.id K) u (normForm K L η))
    rw [eval₂_comp_left]
    rfl
  rw [hl, h K L n η u, Algebra.norm_eq_prod_embeddings]
  simp only [map_prod, map_sum, map_mul, eval_X, eval_C, Function.comp_apply]
  refine Finset.prod_congr rfl fun σ _ => Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, Algebra.smul_def]

end GroundTheory.Heights₂.Heights
