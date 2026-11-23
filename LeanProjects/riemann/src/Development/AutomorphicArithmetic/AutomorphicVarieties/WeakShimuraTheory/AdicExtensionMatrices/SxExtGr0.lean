import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.WPresMaximalIdealGrZeroEqSupSpanMonomials
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoExt

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxExtGr0 :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (W : WPres Λ X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ [IsCO Λ (W.gr 0)] (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (f f' : W.gr 0 →ₐ[Λ] R'), (∀ (b : W.gr 0) (n : W.σ →₀ ℕ), Finsupp.weight W.wt n = 0 → ((b : W.A) : R) = (n.prod fun s k => W.z s ^ k) → f b = f' b) → f = f' := by
  intro Λ _ _ _ _ X _ _ _ _ R _ _ _ W hz _ R' _ _ _ f f' h
  obtain ⟨-, u, hu, hm⟩ := UpperTheory.V.Alg.wPres_maximalIdeal_gr_zero_eq_sup_span_monomials Λ X R W hz
  have hloc : ∀ g : W.gr 0 →ₐ[Λ] R', ∀ x ∈ maximalIdeal (W.gr 0), g x ∈ maximalIdeal R' := fun g x hx => by
    rw [← res_eq_zero_iff Λ, res_map, res_eq_zero_iff]
    exact hx
  refine UpperTheory.V.Alg.co_ext Λ (W.gr 0) Λ R' (maximalIdeal R') (Algebra.ofId Λ (W.gr 0)) (u : Set (W.gr 0)) ?_ ?_ f f'
    ⟨1, fun x hx => ?_⟩ (Subsingleton.elim _ _) fun s hs => ?_
  · intro b hb
    show b ∈ maximalIdeal (W.gr 0)
    rw [hm]
    exact Ideal.mem_sup_right (Ideal.subset_span hb)
  · refine le_trans (hm.trans (sup_comm _ _)).le ?_
    exact le_sup_left
  · rw [pow_one] at hx
    exact ⟨hloc f x hx, hloc f' x hx⟩
  · obtain ⟨n, -, hn, hb⟩ := hu s hs
    exact h s n hn hb
