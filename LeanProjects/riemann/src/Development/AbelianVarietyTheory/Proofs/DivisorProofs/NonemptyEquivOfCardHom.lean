import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.HomCount

theorem card_ker_eq (R : Type) [Ring R] (X M : Type) [AddCommGroup X] [Module R X]
    [AddCommGroup M] [Module R M] (Y : Submodule R X) :
    Nat.card {f : X →ₗ[R] M // LinearMap.ker f = Y}
      = Nat.card {g : (X ⧸ Y) →ₗ[R] M // LinearMap.ker g = ⊥} := by
  refine Nat.card_congr
    { toFun := fun f => ⟨Y.liftQ f.1 f.2.ge, Submodule.ker_liftQ_eq_bot _ _ _ f.2.le⟩
      invFun := fun g => ⟨g.1 ∘ₗ Y.mkQ, by
        rw [LinearMap.ker_comp, g.2]
        exact Y.ker_mkQ⟩
      left_inv := fun f => Subtype.ext (Y.liftQ_mkQ _ _)
      right_inv := fun g => Subtype.ext ?_ }
  apply Submodule.linearMap_qext
  exact Y.liftQ_mkQ _ _

theorem finite_hom (R : Type) [Ring R] (X M : Type) [AddCommGroup X] [Module R X] [Finite X]
    [AddCommGroup M] [Module R M] [Finite M] : Finite (X →ₗ[R] M) :=
  Finite.of_injective (fun f : X →ₗ[R] M => (f : X → M)) DFunLike.coe_injective

theorem card_hom_eq_sum (R : Type) [Ring R] (X M : Type) [AddCommGroup X] [Module R X] [Finite X]
    [AddCommGroup M] [Module R M] [Finite M] [Fintype (Submodule R X)] :
    Nat.card (X →ₗ[R] M)
      = ∑ Y : Submodule R X, Nat.card {f : X →ₗ[R] M // LinearMap.ker f = Y} := by
  haveI := finite_hom R X M
  rw [← Nat.card_sigma]
  exact Nat.card_congr (Equiv.sigmaFiberEquiv (fun f : X →ₗ[R] M => LinearMap.ker f)).symm

theorem card_inj_eq (R : Type) [Ring R] (M N : Type) [AddCommGroup M] [Module R M] [Finite M]
    [AddCommGroup N] [Module R N] [Finite N]
    (h : ∀ (X : Type) [AddCommGroup X] [Module R X] [Finite X],
      Nat.card (X →ₗ[R] M) = Nat.card (X →ₗ[R] N)) (n : ℕ) :
    ∀ (X : Type) [AddCommGroup X] [Module R X] [Finite X], Nat.card X = n →
      Nat.card {f : X →ₗ[R] M // LinearMap.ker f = ⊥}
        = Nat.card {f : X →ₗ[R] N // LinearMap.ker f = ⊥} := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X _ _ _ hX
    haveI : Finite (Submodule R X) :=
      Finite.of_injective (fun Y : Submodule R X => (Y : Set X)) SetLike.coe_injective
    letI : Fintype (Submodule R X) := Fintype.ofFinite _
    have h1 := h X
    rw [card_hom_eq_sum, card_hom_eq_sum,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ (⊥ : Submodule R X)),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ (⊥ : Submodule R X))] at h1
    have h2 : ∑ Y ∈ Finset.univ.erase (⊥ : Submodule R X),
          Nat.card {f : X →ₗ[R] M // LinearMap.ker f = Y}
        = ∑ Y ∈ Finset.univ.erase (⊥ : Submodule R X),
          Nat.card {f : X →ₗ[R] N // LinearMap.ker f = Y} := by
      refine Finset.sum_congr rfl fun Y hY => ?_
      have hY' : Y ≠ ⊥ := Finset.ne_of_mem_erase hY
      rw [card_ker_eq R X M, card_ker_eq R X N]
      haveI : Finite (X ⧸ Y) := Finite.of_surjective _ Y.mkQ_surjective
      refine ih (Nat.card (X ⧸ Y)) ?_ (X ⧸ Y) rfl
      rw [← hX]
      refine lt_of_le_of_ne (Nat.card_le_card_of_surjective _ Y.mkQ_surjective) fun he => hY' ?_
      have hb : Function.Bijective Y.mkQ :=
        (Function.Surjective.bijective_of_nat_card_le Y.mkQ_surjective he.ge)
      rw [← Y.ker_mkQ]
      exact LinearMap.ker_eq_bot.2 hb.1
    omega

theorem nonempty_equiv_of_card_hom :
    ∀ (R : Type) [Ring R] (M N : Type) [AddCommGroup M] [Module R M] [Finite M] [AddCommGroup N] [Module R N] [Finite N], (∀ (X : Type) [AddCommGroup X] [Module R X] [Finite X], Nat.card (X →ₗ[R] M) = Nat.card (X →ₗ[R] N)) → Nonempty (M ≃ₗ[R] N) := by
  intro R _ M N _ _ _ _ _ _ h
  haveI := finite_hom R M M
  haveI := finite_hom R N N
  have h1 := card_inj_eq R M N h _ M rfl
  have h2 := card_inj_eq R M N h _ N rfl
  haveI : Nonempty {f : M →ₗ[R] M // LinearMap.ker f = ⊥} := ⟨⟨LinearMap.id, LinearMap.ker_id⟩⟩
  haveI : Nonempty {f : N →ₗ[R] N // LinearMap.ker f = ⊥} := ⟨⟨LinearMap.id, LinearMap.ker_id⟩⟩
  have p1 : 0 < Nat.card {f : M →ₗ[R] N // LinearMap.ker f = ⊥} := h1 ▸ Nat.card_pos
  have p2 : 0 < Nat.card {f : N →ₗ[R] M // LinearMap.ker f = ⊥} := h2 ▸ Nat.card_pos
  obtain ⟨⟨f, hf⟩⟩ := (Nat.card_pos_iff.1 p1).1
  obtain ⟨⟨g, hg⟩⟩ := (Nat.card_pos_iff.1 p2).1
  rw [LinearMap.ker_eq_bot] at hf hg
  have hb : Function.Bijective f :=
    hf.bijective_of_nat_card_le (Nat.card_le_card_of_injective _ hg)
  exact ⟨LinearEquiv.ofBijective f hb⟩

end GlobalTheory.HomCount
