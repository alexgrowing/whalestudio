import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TZero

open Finset GlobalTheory.CompanionTheory.CoefId

namespace GlobalTheory.CompanionTheory.CoefId

theorem prod_pairs_add_eq_sum_score {n : ℕ} (z : Fin n → ℂ) :
    ∏ p ∈ prs n, (z p.1 + z p.2) = ∑ T ∈ (prs n).powerset, ∏ a, z a ^ score T a := by
  have h1 : ∀ (S : Finset (Fin n × Fin n)) (f : Fin n × Fin n → Fin n),
      ∏ p ∈ S, z (f p) = ∏ a, z a ^ (S.filter fun p => f p = a).card := by
    intro S f
    rw [← Finset.prod_fiberwise_of_maps_to (g := f) (t := univ) (fun _ _ => mem_univ _)]
    refine prod_congr rfl fun a _ => ?_
    rw [prod_congr rfl (fun p hp => by rw [(mem_filter.1 hp).2]), prod_const]
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [h1 T Prod.fst, h1 (prs n \ T) Prod.snd, ← prod_mul_distrib]
  refine prod_congr rfl fun a _ => ?_
  have : score T a = (((T.filter fun p => p.1 = a).card + ((prs n \ T).filter fun p => p.2 = a).card : ℕ) : ℤ) := by
    simp [score]
  rw [this, zpow_natCast, pow_add]

end GlobalTheory.CompanionTheory.CoefId
