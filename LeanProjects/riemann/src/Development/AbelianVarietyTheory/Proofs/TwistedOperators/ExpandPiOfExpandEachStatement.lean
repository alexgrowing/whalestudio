import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpandPiOfExpandEach
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_sum_prod_of_expansion_in_each_coordinate : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} (K : ∀ i, Set (X i)) (m : ι → ℕ)
    (k : ∀ i, Fin (m i) → X i) (hk : ∀ i j, k i j ∈ K i) (c : ∀ i, Fin (m i) → X i → ℂ)
    (f : (∀ i, X i) → ℂ)
    (hf : ∀ i (g : ∀ i, X i), (∀ i, g i ∈ K i) → f g = ∑ j, f (Function.update g i (k i j)) * c i j (g i))
    (g : ∀ i, X i) (hg : ∀ i, g i ∈ K i), f g = ∑ J : (∀ i, Fin (m i)), f (fun i => k i (J i)) * ∏ i, c i (J i) (g i) := by
  first | exact @GlobalTheory.expand_pi_of_expand_each | exact GlobalTheory.expand_pi_of_expand_each | (intros; apply GlobalTheory.expand_pi_of_expand_each <;> assumption)
