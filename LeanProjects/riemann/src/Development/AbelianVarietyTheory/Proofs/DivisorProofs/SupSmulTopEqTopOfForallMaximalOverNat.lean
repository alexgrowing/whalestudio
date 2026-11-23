import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory

theorem sup_smul_top_eq_top_of_maximal {E : Type} [Field E] [NumberField E] {X : Type} [AddCommGroup X] [Module (𝓞 E) X]
    (N : Submodule (𝓞 E) X) (n : ℕ) (hn : 0 < n)
    (h : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → N ⊔ 𝔮 • (⊤ : Submodule (𝓞 E) X) = ⊤) :
    N ⊔ Ideal.span {(n : 𝓞 E)} • (⊤ : Submodule (𝓞 E) X) = ⊤ := by
  have hn0 : (n : 𝓞 E) ≠ 0 := by exact_mod_cast hn.ne'
  suffices key : ∀ I : Ideal (𝓞 E), Ideal.span {(n : 𝓞 E)} ≤ I → N ⊔ I • (⊤ : Submodule (𝓞 E) X) = ⊤ from
    key _ le_rfl
  intro I
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    intro hI
    exfalso
    apply hn0
    have : (n : 𝓞 E) ∈ (0 : Ideal (𝓞 E)) := hI (Ideal.mem_span_singleton_self _)
    simpa using this
  | h₂ x hx =>
    intro _
    rw [Ideal.isUnit_iff.mp hx, Submodule.top_smul, sup_top_eq]
  | h₃ a p ha hp ih =>
    intro hI
    have hpI : (p : Ideal (𝓞 E)).IsPrime := Ideal.isPrime_of_prime hp
    have hpmax : p.IsMaximal := hpI.isMaximal hp.ne_zero
    have hnpa : (n : 𝓞 E) ∈ p * a := hI (Ideal.mem_span_singleton_self _)
    have hnp : (n : 𝓞 E) ∈ p := (Ideal.mul_le_left : p * a ≤ p) hnpa
    have h1 := h p hpmax hnp
    have h2 := ih (hI.trans (Ideal.mul_le_right : p * a ≤ a))
    apply top_unique
    calc (⊤ : Submodule (𝓞 E) X) = N ⊔ p • (N ⊔ a • ⊤) := by rw [h2, h1]
      _ = N ⊔ (p • N ⊔ p • a • ⊤) := by rw [Submodule.smul_sup]
      _ ≤ N ⊔ (p * a) • ⊤ := by
        rw [Submodule.mul_smul, ← sup_assoc]
        exact sup_le_sup_right (sup_le le_rfl (Submodule.smul_le_right)) _

end GlobalTheory
