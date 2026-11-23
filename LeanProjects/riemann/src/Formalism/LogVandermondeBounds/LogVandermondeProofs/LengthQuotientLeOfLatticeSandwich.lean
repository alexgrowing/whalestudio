import Mathlib

namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts

open Module IsLocalRing

set_option maxHeartbeats 800000

section

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {M : Type} [AddCommGroup M] [Module R M]

theorem length_quot_le_of_pow_smul (ϖ : R) (hϖ : Irreducible ϖ) (N : Type) [AddCommGroup N]
    [Module R N] [Module.Free R N] [Module.Finite R N] (T : Submodule R N) (e : ℕ)
    (hT : ∀ x : N, ϖ ^ e • x ∈ T) :
    Module.length R (N ⧸ T) ≤ (e * Module.finrank R N : ℕ) := by
  classical
  obtain ⟨r, hr⟩ : ∃ r, r = Module.finrank R N := ⟨_, rfl⟩
  have b : Basis (Fin (Module.finrank R N)) R N := Module.finBasis R N
  have hmax : IsLocalRing.maximalIdeal R = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hI : ∀ x ∈ IsLocalRing.maximalIdeal R ^ e, ∀ n : N, x • n ∈ T := by
    intro x hx n
    rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
    obtain ⟨y, rfl⟩ := hx
    rw [mul_smul]
    exact hT _
  let comp : Fin (Module.finrank R N) → (R ⧸ IsLocalRing.maximalIdeal R ^ e) →ₗ[R] N ⧸ T := fun i =>
    (IsLocalRing.maximalIdeal R ^ e).liftQ (LinearMap.toSpanSingleton R (N ⧸ T) (T.mkQ (b i)))
      (fun x hx => by
        rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← map_smul, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero]
        exact hI x hx (b i))
  let ψ : (Fin (Module.finrank R N) → R ⧸ IsLocalRing.maximalIdeal R ^ e) →ₗ[R] N ⧸ T :=
    ∑ i, (comp i).comp (LinearMap.proj i)
  have hsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective T q
    refine ⟨fun i => Submodule.Quotient.mk (b.repr n i), ?_⟩
    simp only [ψ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, comp,
      Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply]
    calc ∑ i, (b.repr n i) • T.mkQ (b i) = T.mkQ (∑ i, (b.repr n i) • b i) := by
          rw [map_sum]; simp only [map_smul]
      _ = Submodule.Quotient.mk n := by rw [b.sum_repr]; rfl
  have hlen := Module.length_le_of_surjective ψ hsurj
  rw [Module.length_pi, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal] at hlen
  refine hlen.trans (le_of_eq ?_)
  rw [ENat.card_eq_coe_fintype_card, Fintype.card_fin]
  push_cast
  ring

end

end Formalism.LogVandermondeBounds.product_first_zeroth_parts
