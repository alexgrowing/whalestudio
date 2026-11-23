import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.ChainRows
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.CompanionTheory.InertiaEigenvalues

theorem finrank_along_relation : ∀ (k : Type) [Field k] (H M N Q : Type) [AddCommGroup H] [Module k H] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N] [AddCommGroup Q] [Module k Q] [Module.Finite k M] [Module.Finite k N] (a : H →ₗ[k] M) (b : M →ₗ[k] N) (R : Submodule k (N × Q)), Function.Injective a → LinearMap.range a = LinearMap.ker b → (∀ n, ∃ q, (n, q) ∈ R) → (∀ q, ∃ n, (n, q) ∈ R) → (∀ q, (0, q) ∈ R → q = 0) → (∀ n, (n, 0) ∈ R ↔ n ∈ LinearMap.range b) → Module.Finite k Q ∧ finrank k Q + finrank k M = finrank k H + finrank k N := by
  intro k _ H M N Q _ _ _ _ _ _ _ _ _ _ a b R hinj hex hN hQ h0 hb
  let p1 : R →ₗ[k] N := (LinearMap.fst k N Q).comp R.subtype
  let p2 : R →ₗ[k] Q := (LinearMap.snd k N Q).comp R.subtype
  have p1bij : Function.Bijective p1 := by
    constructor
    · rw [injective_iff_map_eq_zero]
      rintro ⟨⟨n, q⟩, hr⟩ h
      have hn : n = 0 := h
      subst hn
      have hq : q = 0 := h0 q hr
      subst hq
      rfl
    · intro n
      obtain ⟨q, hq⟩ := hN n
      exact ⟨⟨(n, q), hq⟩, rfl⟩
  let e : R ≃ₗ[k] N := LinearEquiv.ofBijective p1 p1bij
  let δ : N →ₗ[k] Q := p2.comp e.symm.toLinearMap
  have hδ : ∀ x : R, δ (p1 x) = p2 x := by
    intro x
    have h : e.symm (p1 x) = x := e.symm_apply_apply x
    show p2 (e.symm (p1 x)) = p2 x
    rw [h]
  have hsurj : Function.Surjective δ := by
    intro q
    obtain ⟨n, hn⟩ := hQ q
    exact ⟨n, hδ ⟨(n, q), hn⟩⟩
  have hker : LinearMap.ker δ = LinearMap.range b := by
    ext n
    rw [LinearMap.mem_ker, ← hb n]
    obtain ⟨q, hq⟩ := hN n
    have h1 : δ n = q := hδ ⟨(n, q), hq⟩
    rw [h1]
    constructor
    · rintro rfl
      exact hq
    · intro h
      have h2 : ((n, q) - (n, 0) : N × Q) ∈ R := R.sub_mem hq h
      have h3 : ((n, q) - (n, 0) : N × Q) = (0, q) := by simp
      rw [h3] at h2
      exact h0 q h2
  refine ⟨Module.Finite.of_surjective δ hsurj, ?_⟩
  have e1 := LinearMap.finrank_range_add_finrank_ker δ
  have e2 := LinearMap.finrank_range_add_finrank_ker b
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, hker] at e1
  rw [← hex] at e2
  have e3 : finrank k (LinearMap.range a) = finrank k H := LinearMap.finrank_range_of_inj hinj
  rw [e3] at e2
  omega

end GlobalTheory.CompanionTheory.InertiaEigenvalues
