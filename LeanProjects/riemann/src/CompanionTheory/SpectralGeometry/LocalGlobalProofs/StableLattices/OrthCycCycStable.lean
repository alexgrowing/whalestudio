import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.LowKType

open CompanionTheory.D.LK CompanionTheory.D.DSIC Formalism.REAL

theorem orthCyc_cyc_stable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (v : V) (a b : Fin n) {x : V} (hx : x ∈ Cyc E v) :
    E a b x ∈ Cyc E v := by
  obtain ⟨t, rfl⟩ := hx
  refine ⟨FreeAlgebra.ι ℂ (a, b) * t, ?_⟩
  simp [ev]

theorem orthCyc : CompanionTheory.D.LK.OrthCyc := by
  intro n ε V _ _ E μ v u _ hU hL h1 hu hvu m hm
  obtain ⟨S, hS, hSst, hmS⟩ := hL m
  set W : Submodule ℂ V := S ⊓ Cyc E v with hW
  haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le (inf_le_left : W ≤ S)
  have hWst : ∀ a b, ε a = ε b → ∀ x ∈ W, E a b x ∈ W := fun a b hab x hx =>
    ⟨hSst a b hab x hx.1, orthCyc_cyc_stable E v a b hx.2⟩
  have hOst : ∀ a b, ε a = ε b → ∀ x ∈ Wᗮ, E a b x ∈ Wᗮ := by
    intro a b hab x hx
    rw [Submodule.mem_orthogonal] at hx ⊢
    intro w hw
    rw [← hU b a hab.symm]
    exact hx _ (hWst b a hab.symm w hw)
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.exists_add_mem_mem_orthogonal (K := W) u
  have key : ∀ a b, ε a = ε b → ∀ c : ℂ, E a b u = c • u → E a b p = c • p := by
    intro a b hab c hc
    have h : E a b p - c • p ∈ W ⊓ Wᗮ := by
      refine ⟨W.sub_mem (hWst a b hab p hp) (W.smul_mem c hp), ?_⟩
      have : E a b p - c • p = c • q - E a b q := by
        rw [hpq, map_add, smul_add] at hc
        rw [sub_eq_sub_iff_add_eq_add, hc, add_comm]
      rw [this]
      exact Wᗮ.sub_mem (Wᗮ.smul_mem c hq) (hOst a b hab q hq)
    rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot, sub_eq_zero] at h
    exact h
  have hpH : KHighest ε E μ p := by
    refine ⟨fun a => key a a rfl _ (hu.1 a), fun a b hab hε => ?_⟩
    have := key a b hε 0 (by rw [zero_smul]; exact hu.2 a b hab hε)
    simpa using this
  obtain ⟨c, hc⟩ := h1 p hp.2 hpH
  have hq' := (Submodule.mem_orthogonal W q).1 hq
  have hpu : ⟪p, u⟫_ℂ = 0 := by rw [hc, inner_smul_left, hvu, mul_zero]
  have hp0 : p = 0 := by
    rw [hpq, inner_add_right, hq' p hp, add_zero] at hpu
    exact inner_self_eq_zero.1 hpu
  rw [hpq, hp0, zero_add]
  exact hq' m ⟨hmS, hm⟩

end GlobalTheory.CompanionTheory.LowKType
