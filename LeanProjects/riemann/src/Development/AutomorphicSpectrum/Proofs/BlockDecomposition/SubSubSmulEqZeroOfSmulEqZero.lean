import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.TwistedUnit

theorem sub_sub_smul_eq_zero_of_smul_eq_zero {Λ N : Type} [CommRing Λ] [AddCommGroup N]
    [Module Λ N] [Module.Flat Λ N] (γ : N →ₗ[Λ] N) (c μ : Λ)
    (h : ∀ x, ∃ x', γ x - x - c • x = μ • x') (z : N) (hz : μ • z = 0) :
    γ z - z - c • z = 0 := by
  obtain ⟨k, a, y, hx, hf⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := Λ) (M := N)
    (f := fun _ : Fin 1 => μ) (x := fun _ : Fin 1 => z) (by simpa using hz)
  choose d hd using h
  have hz' : z = ∑ j, a 0 j • y j := hx 0
  have h0 : ∀ j, μ * a 0 j = 0 := fun j => by simpa using hf j
  have hlin : ∀ j, a 0 j • (γ (y j) - y j - c • y j) = 0 := by
    intro j
    rw [hd, smul_smul, mul_comm, h0, zero_smul]
  have hsum : γ z - z - c • z = ∑ j, a 0 j • (γ (y j) - y j - c • y j) := by
    conv_lhs => rw [hz']
    simp only [map_sum, map_smul, Finset.smul_sum, smul_sub, Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => smul_comm _ _ _)
  rw [hsum]
  exact Finset.sum_eq_zero (fun j _ => hlin j)

theorem smul_eq_zero_of_fixed {Λ N : Type} [CommRing Λ] [AddCommGroup N] [Module Λ N]
    [Module.Flat Λ N] (γ : N →ₗ[Λ] N) (c w ξ μ : Λ) (hμ : μ = c * w * ξ) (hξ : IsNilpotent ξ)
    (h : ∀ x, ∃ x', γ x - x - c • x = μ • x') (x : N) (hx : γ x = x) : μ • x = 0 := by
  have hE := sub_sub_smul_eq_zero_of_smul_eq_zero γ c μ h
  have R : ∀ n : ℕ, ∀ x, (w * ξ) • (γ x - x) = 0 → ∃ u, μ • (x - ξ ^ n • u) = 0 := by
    intro n
    induction n with
    | zero => exact fun x _ => ⟨x, by simp⟩
    | succ n ih =>
      intro x hx
      obtain ⟨x', hx'⟩ := h x
      have h1 : μ • (x + (w * ξ) • x') = 0 := by
        have : μ • (x + (w * ξ) • x') = (w * ξ) • (γ x - x) := by
          subst hμ
          linear_combination (norm := module) -(w * ξ) • hx'
        rw [this, hx]
      have h2 := hE _ h1
      simp only [map_add, map_smul] at h2
      have hM : (w * ξ) • (γ x' - x') = 0 := by
        subst hμ
        linear_combination (norm := module) h2 - hx'
      obtain ⟨u, hu⟩ := ih x' hM
      refine ⟨-w • u, ?_⟩
      have : μ • (x - ξ ^ (n + 1) • (-w • u))
          = μ • (x + (w * ξ) • x') - (w * ξ) • (μ • (x' - ξ ^ n • u)) := by
        module
      rw [this, h1, hu]
      simp
  obtain ⟨n, hn⟩ := hξ
  obtain ⟨u, hu⟩ := R n x (by simp [hx])
  simpa [hn] using hu

theorem exists_mem_smul_top {Λ N : Type} [CommRing Λ] [AddCommGroup N] [Module Λ N]
    (γ : N →ₗ[Λ] N) (c μ : Λ) (h : ∀ x, ∃ x', γ x - x - c • x = μ • x') (𝔞 : Ideal Λ) (x : N)
    (hx : x ∈ 𝔞 • (⊤ : Submodule Λ N)) :
    ∃ x₁ ∈ 𝔞 • (⊤ : Submodule Λ N), γ x - x - c • x = μ • x₁ := by
  induction hx using Submodule.smul_induction_on' with
  | smul a ha n hn =>
    obtain ⟨n', hn'⟩ := h n
    refine ⟨a • n', Submodule.smul_mem_smul ha trivial, ?_⟩
    rw [map_smul]
    linear_combination (norm := module) a • hn'
  | add x hx y hy ihx ihy =>
    obtain ⟨x₁, hx₁, e₁⟩ := ihx
    obtain ⟨y₁, hy₁, e₂⟩ := ihy
    refine ⟨x₁ + y₁, Submodule.add_mem _ hx₁ hy₁, ?_⟩
    rw [map_add]
    linear_combination (norm := module) e₁ + e₂

theorem exists_sub_eq_smul {Λ N : Type} [CommRing Λ] [AddCommGroup N] [Module Λ N]
    (γ : N →ₗ[Λ] N) (c w ξ μ : Λ) (hμ : μ = c * w * ξ) (hξ : IsNilpotent ξ)
    (h : ∀ x, ∃ x', γ x - x - c • x = μ • x') (𝔞 : Ideal Λ) (x : N)
    (hx : x ∈ 𝔞 • (⊤ : Submodule Λ N)) :
    ∃ y ∈ (Ideal.span {ξ} * 𝔞) • (⊤ : Submodule Λ N), γ y - y = μ • x := by
  obtain ⟨n, hn⟩ := hξ
  have P : ∀ m k : ℕ, m + k = n → ∀ x ∈ 𝔞 • (⊤ : Submodule Λ N),
      ∃ y ∈ (Ideal.span {ξ} * 𝔞) • (⊤ : Submodule Λ N), γ y - y = (μ * ξ ^ k) • x := by
    intro m
    induction m with
    | zero =>
      intro k hk x _
      have : ξ ^ k = 0 := by
        rw [show k = n by omega, hn]
      exact ⟨0, Submodule.zero_mem _, by simp [this]⟩
    | succ m ih =>
      intro k hk x hx
      obtain ⟨x₁, hx₁, e⟩ := exists_mem_smul_top γ c μ h 𝔞 x hx
      obtain ⟨y', hy', e'⟩ := ih (k + 1) (by omega) (w • x₁)
        (Submodule.smul_of_tower_mem _ w hx₁)
      have hξx : ξ • x ∈ (Ideal.span {ξ} * 𝔞) • (⊤ : Submodule Λ N) := by
        rw [Submodule.mul_smul]
        exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self ξ) hx
      refine ⟨(w * ξ ^ k) • (ξ • x) - y',
        Submodule.sub_mem _ (Submodule.smul_of_tower_mem _ _ hξx) hy', ?_⟩
      simp only [map_sub, map_smul]
      subst hμ
      linear_combination (norm := module) (w * ξ ^ (k + 1)) • e - e'
  simpa using P n 0 rfl x hx

theorem twisted_bijective_up_to :
    ∀ {Λ N : Type} [CommRing Λ] [AddCommGroup N] [Module Λ N] [Module.Flat Λ N]
      (γ : N →ₗ[Λ] N) (c w ξ μ : Λ), μ = c * w * ξ → IsNilpotent ξ →
      (∀ x, ∃ x', γ x - x - c • x = μ • x') →
      (∀ x, γ x = x → μ • x = 0) ∧ ∀ (𝔞 : Ideal Λ), ∀ x ∈ 𝔞 • (⊤ : Submodule Λ N),
        ∃ y ∈ (Ideal.span {ξ} * 𝔞) • (⊤ : Submodule Λ N), γ y - y = μ • x := by
  intro Λ N _ _ _ _ γ c w ξ μ hμ hξ h
  exact ⟨smul_eq_zero_of_fixed γ c w ξ μ hμ hξ h,
    fun 𝔞 x hx => exists_sub_eq_smul γ c w ξ μ hμ hξ h 𝔞 x hx⟩

end GlobalTheory.CompanionTheory.TwistedUnit
