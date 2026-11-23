import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeGramScalarAlmostAll
open HeckeCharacterZeroLocus.SiegelWeilU
open scoped Matrix

namespace GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry

open GlobalTheory.CompanionTheory.SW.QuasiRefl

section Form

variable {A : Type} [CommRing A] {N : ℕ} {τ : A →+* A} {H : Matrix (Fin N) (Fin N) A}

theorem hform_add_fst (x x' y : Fin N → A) :
    hform τ H (x + x') y = hform τ H x y + hform τ H x' y := by
  have h : (τ ∘ (x + x')) = τ ∘ x + τ ∘ x' := by
    funext i
    simp
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot, h, add_dotProduct]

theorem hform_add_snd (x y y' : Fin N → A) :
    hform τ H x (y + y') = hform τ H x y + hform τ H x y' := by
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot, Matrix.mulVec_add, dotProduct_add]

theorem hform_sub_fst (x x' y : Fin N → A) :
    hform τ H (x - x') y = hform τ H x y - hform τ H x' y := by
  have h : (τ ∘ (x - x')) = τ ∘ x - τ ∘ x' := by
    funext i
    simp
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot, h, sub_dotProduct]

theorem hform_sub_snd (x y y' : Fin N → A) :
    hform τ H x (y - y') = hform τ H x y - hform τ H x y' := by
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot, Matrix.mulVec_sub, dotProduct_sub]

theorem hform_unitary {g : GL (Fin N) A} (hg : g ∈ UJ τ H) (x y : Fin N → A) :
    hform τ H ((g : Matrix (Fin N) (Fin N) A) *ᵥ x) ((g : Matrix (Fin N) (Fin N) A) *ᵥ y) =
      hform τ H x y := by
  rw [hform_mulVec']
  have hg' : cT τ (g : Matrix (Fin N) (Fin N) A) * H * (g : Matrix (Fin N) (Fin N) A) = H := hg
  rw [hg']

theorem carry (hτ : ∀ y, τ (τ y) = y)
    (hcar : ∀ p β : A, IsUnit β → τ β = β → ∃ ε z : A, ε * τ ε = 1 ∧ (β - τ ε * p) * z = 1)
    (hH : ∀ i j, τ (H j i) = H i j) (x y : Fin N → A)
    (hxy : hform τ H x x = hform τ H y y) (hβ : IsUnit (hform τ H x x)) :
    ∃ g ∈ UJ τ H, (g : Matrix (Fin N) (Fin N) A) *ᵥ x = y ∧
      ∀ z, hform τ H x z = 0 → hform τ H y z = 0 → (g : Matrix (Fin N) (Fin N) A) *ᵥ z = z := by
  have hfix : τ (hform τ H x x) = hform τ H x x := hform_conj_symm hτ hH x x
  obtain ⟨ε, z, hε, hz⟩ := hcar (hform τ H y x) (hform τ H x x) hβ hfix
  exact exists_unitary_carry A τ hτ N H hH x y ε hxy hβ hε ⟨⟨_, z, hz, (mul_comm z _).trans hz⟩, rfl⟩

theorem exists_hyperbolic_partner (hτ : ∀ y, τ (τ y) = y) (h2 : IsUnit (2 : A))
    {Hi : Matrix (Fin N) (Fin N) A} (hHi : H * Hi = 1) (hH : ∀ i j, τ (H j i) = H i j)
    (y a : Fin N → A) (hyy : hform τ H y y = 0) (hay : ∑ k, a k * y k = 1) :
    ∃ y₁ : Fin N → A, hform τ H y₁ y₁ = 0 ∧ hform τ H y y₁ = 1 := by
  have hyw : hform τ H y (Hi *ᵥ (τ ∘ a)) = 1 := by
    rw [hform_eq_dot, Matrix.mulVec_mulVec, hHi, Matrix.one_mulVec]
    have h : (τ ∘ y) ⬝ᵥ (τ ∘ a) = τ (∑ k, a k * y k) := by
      simp only [dotProduct, Function.comp_apply, map_sum, map_mul]
      exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
    rw [h, hay, map_one]
  have hwy : hform τ H (Hi *ᵥ (τ ∘ a)) y = 1 := by
    rw [← hform_conj_symm hτ hH y (Hi *ᵥ (τ ∘ a)), hyw, map_one]
  have hww : τ (hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a))) =
      hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a)) := hform_conj_symm hτ hH _ _
  have ht2 : 2 * (↑h2.unit⁻¹ : A) = 1 := h2.mul_val_inv
  have hτt : τ (↑h2.unit⁻¹ : A) = ↑h2.unit⁻¹ := by
    have h1 : τ (↑h2.unit⁻¹ : A) * 2 = 1 := by
      have h := congrArg τ ht2
      rw [map_mul, map_one, map_ofNat] at h
      rw [mul_comm]
      exact h
    calc τ (↑h2.unit⁻¹ : A) = τ (↑h2.unit⁻¹ : A) * (2 * ↑h2.unit⁻¹) := by rw [ht2, mul_one]
      _ = (τ (↑h2.unit⁻¹ : A) * 2) * ↑h2.unit⁻¹ := by ring
      _ = ↑h2.unit⁻¹ := by rw [h1, one_mul]
  have hτc : τ ((↑h2.unit⁻¹ : A) * hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a))) =
      (↑h2.unit⁻¹ : A) * hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a)) := by
    rw [map_mul, hτt, hww]
  refine ⟨Hi *ᵥ (τ ∘ a) - ((↑h2.unit⁻¹ : A) * hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a))) • y, ?_, ?_⟩
  · rw [hform_sub_left, hform_sub_right, hform_sub_right, hyy, hwy, hyw, hτc]
    linear_combination (-1 : A) * hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a)) * ht2
  · rw [hform_sub_right, hyw, hyy, mul_zero, sub_zero]

end Form

theorem exists_unitary_carry_primitive :
    ∀ (A : Type) [CommRing A] (τ : A →+* A), (∀ y, τ (τ y) = y) → IsUnit (2 : A) →
    (∀ p β : A, IsUnit β → τ β = β → ∃ ε z : A, ε * τ ε = 1 ∧ (β - τ ε * p) * z = 1) →
    ∀ (N : ℕ) (H Hi : Matrix (Fin N) (Fin N) A), H * Hi = 1 → (∀ i j, τ (H j i) = H i j) →
    ∀ e f y a : Fin N → A, hform τ H e e = 0 → hform τ H f f = 0 → hform τ H e f = 1 →
    hform τ H y y = 0 → ∑ k, a k * y k = 1 →
    ∃ g ∈ UJ τ H, (g : Matrix (Fin N) (Fin N) A) *ᵥ e = y := by
  intro A _ τ hτ h2 hcar N H Hi hHi hH e f y a hee hff hef hyy hay
  obtain ⟨y₁, hy₁, hyy₁⟩ := exists_hyperbolic_partner hτ h2 hHi hH y a hyy hay
  have hfe : hform τ H f e = 1 := by rw [← hform_conj_symm hτ hH e f, hef, map_one]
  have hy₁y : hform τ H y₁ y = 1 := by rw [← hform_conj_symm hτ hH y y₁, hyy₁, map_one]
  have hx1 : hform τ H (e + f) (e + f) = 2 := by
    rw [hform_add_fst, hform_add_snd, hform_add_snd, hee, hef, hfe, hff]
    norm_num
  have hy1 : hform τ H (y + y₁) (y + y₁) = 2 := by
    rw [hform_add_fst, hform_add_snd, hform_add_snd, hyy, hyy₁, hy₁y, hy₁]
    norm_num
  obtain ⟨g₁, hg₁, hg₁x, -⟩ := carry hτ hcar hH (e + f) (y + y₁) (by rw [hx1, hy1]) (by rw [hx1]; exact h2)
  have hvv : hform τ H ((g₁ : Matrix (Fin N) (Fin N) A) *ᵥ (e - f)) ((g₁ : Matrix (Fin N) (Fin N) A) *ᵥ (e - f)) = -2 := by
    rw [hform_unitary hg₁, hform_sub_fst, hform_sub_snd, hform_sub_snd, hee, hef, hfe, hff]
    ring
  have hyy' : hform τ H (y - y₁) (y - y₁) = -2 := by
    rw [hform_sub_fst, hform_sub_snd, hform_sub_snd, hyy, hyy₁, hy₁y, hy₁]
    ring
  have h2' : IsUnit (-2 : A) := h2.neg
  obtain ⟨g₂, hg₂, hg₂v, hfix⟩ := carry hτ hcar hH ((g₁ : Matrix (Fin N) (Fin N) A) *ᵥ (e - f)) (y - y₁)
    (by rw [hvv, hyy']) (by rw [hvv]; exact h2')
  have hperp1 : hform τ H ((g₁ : Matrix (Fin N) (Fin N) A) *ᵥ (e - f)) (y + y₁) = 0 := by
    rw [← hg₁x, hform_unitary hg₁, hform_sub_fst, hform_add_snd, hform_add_snd, hee, hef, hfe, hff]
    ring
  have hperp2 : hform τ H (y - y₁) (y + y₁) = 0 := by
    rw [hform_sub_fst, hform_add_snd, hform_add_snd, hyy, hyy₁, hy₁y, hy₁]
    ring
  have hfix' := hfix (y + y₁) hperp1 hperp2
  refine ⟨g₂ * g₁, mul_mem hg₂ hg₁, ?_⟩
  have hsum : ((g₂ * g₁ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) *ᵥ (e + f) = y + y₁ := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hg₁x, hfix']
  have hdiff : ((g₂ * g₁ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) *ᵥ (e - f) = y - y₁ := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hg₂v]
  have key : (2 : A) • (((g₂ * g₁ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) *ᵥ e) = (2 : A) • y := by
    have h : ((g₂ * g₁ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) *ᵥ ((e + f) + (e - f)) = (y + y₁) + (y - y₁) := by
      rw [Matrix.mulVec_add, hsum, hdiff]
    have he : (e + f) + (e - f) = (2 : A) • e := by
      rw [two_smul]
      abel
    have hy : (y + y₁) + (y - y₁) = (2 : A) • y := by
      rw [two_smul]
      abel
    rw [he, Matrix.mulVec_smul, hy] at h
    exact h
  have h3 := congrArg (fun z => (↑h2.unit⁻¹ : A) • z) key
  simp only [smul_smul, h2.val_inv_mul, one_smul] at h3
  exact h3

end GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry
