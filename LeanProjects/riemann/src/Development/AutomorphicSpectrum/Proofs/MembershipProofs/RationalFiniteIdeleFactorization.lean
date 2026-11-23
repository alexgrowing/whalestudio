import Mathlib
import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.LaEqSqrtSmulLam

noncomputable section

namespace GlobalTheory.CompanionTheory.FinHeis.LawLine

open GlobalTheory.CompanionTheory.FinHeis

variable {X M : Type} [AddCommGroup X] [AddCommGroup M] [Module ℂ M]

theorem c_mul_swap (S : Sys X M) (x y : X) : S.c x y * S.c y x = 1 := by
  have h := S.c_self (x + y)
  rw [S.c_add_left, S.c_add_right, S.c_add_right, S.c_self, S.c_self] at h
  simpa using h

theorem rho_comm (S : Sys X M) (x y : X) (v : M) :
    S.rho x (S.rho y v) = S.c x y ^ 2 • S.rho y (S.rho x v) := by
  rw [S.9 x y v, S.9 y x v, smul_smul, add_comm y x]
  congr 1
  have h := GlobalTheory.CompanionTheory.FinHeis.LawLine.c_mul_swap S x y
  calc S.c x y = S.c x y * (S.c x y * S.c y x) := by rw [h, mul_one]
    _ = S.c x y ^ 2 * S.c y x := by ring

theorem orth (S : Sys X M) (al : X → ℂ) (Γ : AddSubgroup X) (φ φ' : M) (x : X)
    (hΓ : SelfDual S Γ) (hal : IsSemi S al Γ) (hφ : Law S al Γ φ) (hφ' : Law S al Γ φ')
    (hx : x ∉ Γ) : S.B φ' (S.rho x φ) = 0 := by
  have hΓ₀ : ∀ y, y ∈ Γ ↔ ∀ γ ∈ Γ, S.c γ y ^ 2 = 1 := hΓ
  obtain ⟨hal₁, -⟩ : (∀ y ∈ Γ, al y = 1 ∨ al y = -1) ∧
      ∀ y ∈ Γ, ∀ z ∈ Γ, al (y + z) = al y * al z * S.c y z := hal
  have hφ₀ : ∀ γ ∈ Γ, S.rho γ φ = (al γ)⁻¹ • φ := hφ
  have hφ₀' : ∀ γ ∈ Γ, S.rho γ φ' = (al γ)⁻¹ • φ' := hφ'
  have hnot : ¬ ∀ γ ∈ Γ, S.c γ x ^ 2 = 1 := fun h => hx ((hΓ₀ x).2 h)
  push_neg at hnot
  obtain ⟨γ, hγ, hcx⟩ := hnot
  have hinv := S.12 γ φ' (S.rho x φ)
  rw [hφ₀' γ hγ, GlobalTheory.CompanionTheory.FinHeis.LawLine.rho_comm S γ x φ, hφ₀ γ hγ] at hinv
  simp only [LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul] at hinv
  have hunit : (starRingEnd ℂ) (al γ)⁻¹ * (al γ)⁻¹ = 1 := by
    rcases hal₁ γ hγ with h1 | h1 <;> simp [h1]
  have hzero : (S.c γ x ^ 2 - 1) * S.B φ' (S.rho x φ) = 0 := by
    linear_combination hinv - (S.c γ x ^ 2 * S.B φ' (S.rho x φ)) * hunit
  rcases mul_eq_zero.1 hzero with h | h
  · exact absurd (sub_eq_zero.1 h) hcx
  · exact h

theorem law_line {X M : Type} [AddCommGroup X] [AddCommGroup M] [Module ℂ M] (S : Sys X M)
    (al : X → ℂ) (Γ : AddSubgroup X) (φ φ' : M) (hΓ : SelfDual S Γ) (hal : IsSemi S al Γ)
    (hφ : Law S al Γ φ) (hc : Cyclic S φ) (hφ' : Law S al Γ φ') : ∃ a : ℂ, φ' = a • φ := by
  have hφ₀ : ∀ γ ∈ Γ, S.rho γ φ = (al γ)⁻¹ • φ := hφ
  have hφ₀' : ∀ γ ∈ Γ, S.rho γ φ' = (al γ)⁻¹ • φ' := hφ'
  have hc₀ : Submodule.span ℂ (Set.range fun x => S.rho x φ) = ⊤ := hc
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a = S.B φ φ' / S.B φ φ := ⟨_, rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : M, ψ = φ' - a • φ := ⟨_, rfl⟩
  have hψeig : ∀ γ ∈ Γ, S.rho γ ψ = (al γ)⁻¹ • ψ := by
    intro γ hγ
    rw [hψ, map_sub, map_smul, hφ₀' γ hγ, hφ₀ γ hγ, smul_sub, smul_comm (al γ)⁻¹ a φ]
  have hBφψ : S.B φ ψ = 0 := by
    by_cases h0 : φ = 0
    · rw [h0, map_zero, LinearMap.zero_apply]
    · have hpos := S.11 φ h0
      have hne : S.B φ φ ≠ 0 := fun h => by
        rw [h, Complex.zero_re] at hpos
        exact lt_irrefl _ hpos
      rw [hψ, map_sub, map_smul, smul_eq_mul, ha, div_mul_cancel₀ _ hne, sub_self]
  have hall : ∀ x, S.B ψ (S.rho x φ) = 0 := by
    intro x
    by_cases hx : x ∈ Γ
    · rw [hφ₀ x hx, map_smul, smul_eq_mul, ← S.10 φ ψ, hBφψ, map_zero, mul_zero]
    · exact GlobalTheory.CompanionTheory.FinHeis.LawLine.orth S al Γ φ ψ x hΓ hal hφ hψeig hx
  have hker : Submodule.span ℂ (Set.range fun x => S.rho x φ) ≤ LinearMap.ker (S.B ψ) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    exact hall x
  have hmem : ψ ∈ Submodule.span ℂ (Set.range fun x => S.rho x φ) := by
    rw [hc₀]
    exact Submodule.mem_top
  have hψψ : S.B ψ ψ = 0 := LinearMap.mem_ker.1 (hker hmem)
  have hψ0 : ψ = 0 := by
    by_contra hne
    have hpos := S.11 ψ hne
    rw [hψψ, Complex.zero_re] at hpos
    exact lt_irrefl _ hpos
  refine ⟨a, ?_⟩
  rw [hψ] at hψ0
  exact sub_eq_zero.1 hψ0

end GlobalTheory.CompanionTheory.FinHeis.LawLine
