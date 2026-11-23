import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.module_finite_quotient_maximal_pow : ∀ {K A : Type} [Field K] [CommRing A] [Algebra K A] [IsNoetherianRing A] (m : Ideal A), Module.Finite K (A ⧸ m) → ∀ k : ℕ, Module.Finite K (A ⧸ m ^ k) := by
  intro K A _ _ _ _ m hm k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pow_zero, Ideal.one_eq_top]
    infer_instance
  have hle : m ^ k ≤ m := Ideal.pow_le_self (Nat.pos_iff_ne_zero.mp hk)
  let f : (A ⧸ m ^ k) →ₐ[K] A ⧸ m := Ideal.Quotient.factorₐ K hle
  have hsurj : Function.Surjective f := Ideal.Quotient.factor_surjective hle
  refine Module.finite_of_surjective_of_ker_le_nilradical f hsurj ?_ ?_
  · intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have ha : a ∈ m := by
      rw [RingHom.mem_ker] at hx
      have : Ideal.Quotient.mk m a = 0 := hx
      exact Ideal.Quotient.eq_zero_iff_mem.mp this
    refine ⟨k, ?_⟩
    rw [← map_pow, Ideal.zero_eq_bot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow ha k
  · exact IsNoetherian.noetherian _
