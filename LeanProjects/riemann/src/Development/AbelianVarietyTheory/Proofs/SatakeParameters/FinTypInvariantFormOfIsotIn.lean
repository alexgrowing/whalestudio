import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConjSubConjSub
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
open Formalism.BasicNotions Formalism.L2 Formalism.L2.NG Formalism.AUTREP Formalism.IndefR.principalLevelFrame

namespace GlobalTheory

theorem finTyp_invariant_form_of_isotIn : ∀ (D : D7) (n : ℕ) (A : Type) [AddCommGroup A] [Module ℂ A] (ρ : GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A) (B : A → A → ℂ), (∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ c : ℂ, B x (y + c • z) = B x y + c * B x z) → (∀ x ∈ C, ∀ y ∈ C, B x y = starRingEnd ℂ (B y x)) → (∀ x ∈ C, x ≠ 0 → 0 < (B x x).re) → (∀ h, ∀ x ∈ C, ρ h x ∈ C) → (∀ h, ∀ x ∈ C, ∀ y ∈ C, B (ρ h x) (ρ h y) = B x y) → ∀ π : FinTyp D.host.E n, isotIn (D := D) ρ C π ≠ ⊥ → ∃ B' : π.S → π.S → ℂ, (∀ x y z (c : ℂ), B' x (y + c • z) = B' x y + c * B' x z) ∧ (∀ x y, B' x y = starRingEnd ℂ (B' y x)) ∧ (∀ x, x ≠ 0 → 0 < (B' x x).re) ∧ ∀ h (x y x' y' : π.S), (x' : GAf D.host.E n → ℂ) = rt D.host.E n h x → (y' : GAf D.host.E n → ℂ) = rt D.host.E n h y → B' x' y' = B' x y := by
  intro D n A _ _ ρ C B hlin hherm hpos _hstab hinv π hne

  obtain ⟨Φ, ⟨hΦe, hΦC⟩, hΦne⟩ : ∃ Φ : π.S →ₗ[ℂ] A, (IsEqvA ρ π Φ ∧ LinearMap.range Φ ≤ C) ∧ LinearMap.range Φ ≠ ⊥ := by
    by_contra hcon
    push_neg at hcon
    apply hne
    unfold isotIn
    refine iSup_eq_bot.2 fun Φ => iSup_eq_bot.2 fun hΦ => hcon Φ hΦ
  have hmemC : ∀ x : π.S, Φ x ∈ C := fun x => hΦC (LinearMap.mem_range_self Φ x)

  let S' : Submodule ℂ (GAf D.host.E n → ℂ) := (LinearMap.ker Φ).map π.S.subtype
  have hS'le : S' ≤ π.S := by
    rintro f ⟨k, _, rfl⟩
    exact k.2
  have hS'st : ∀ h, ∀ f ∈ S', rt D.host.E n h f ∈ S' := by
    rintro h f ⟨k, hk, rfl⟩
    refine ⟨⟨rt D.host.E n h k, π.stable h k k.2⟩, ?_, rfl⟩
    have hk' : Φ k = 0 := hk
    show Φ _ = 0
    rw [hΦe h k, hk', map_zero]
  have hinj : ∀ x : π.S, Φ x = 0 → x = 0 := by
    intro x hx
    rcases π.irr S' hS'le hS'st with h0 | hall
    · have : (x : GAf D.host.E n → ℂ) ∈ S' := ⟨x, hx, rfl⟩
      rw [h0, Submodule.mem_bot] at this
      exact Subtype.ext this
    · exfalso
      apply hΦne
      rw [eq_bot_iff]
      rintro a ⟨y, rfl⟩
      have : (y : GAf D.host.E n → ℂ) ∈ S' := by rw [hall]; exact y.2
      obtain ⟨k, hk, hky⟩ := this
      have : k = y := Subtype.ext hky
      subst this
      have hk' : Φ k = 0 := hk
      exact (Submodule.mem_bot ℂ).2 hk'
  refine ⟨fun x y => B (Φ x) (Φ y), ?_, ?_, ?_, ?_⟩
  · intro x y z c
    simp only [map_add, map_smul]
    exact hlin _ (hmemC x) _ (hmemC y) _ (hmemC z) c
  · intro x y
    exact hherm _ (hmemC x) _ (hmemC y)
  · intro x hx
    exact hpos _ (hmemC x) (fun h0 => hx (hinj x h0))
  · intro h x y x' y' hx hy
    have ex : x' = ⟨rt D.host.E n h x, π.stable h x x.2⟩ := Subtype.ext hx
    have ey : y' = ⟨rt D.host.E n h y, π.stable h y y.2⟩ := Subtype.ext hy
    simp only
    rw [ex, ey, hΦe h x, hΦe h y]
    exact hinv h _ (hmemC x) _ (hmemC y)

end GlobalTheory
