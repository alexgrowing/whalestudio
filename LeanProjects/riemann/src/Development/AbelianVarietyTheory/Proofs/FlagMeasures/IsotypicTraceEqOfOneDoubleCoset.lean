import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.OneDoubleCoset

variable {G : Type} [Group G] [Fintype G]

omit [Fintype G] in
theorem isClass_mul_comm {φ : G → ℂ} (hφ : IsClass φ) (x y : G) : φ (x * y) = φ (y * x) := by
  have := hφ (y * x) x
  rw [← this]; congr 1; group

theorem coset_sum_mem (K : Subgroup G) (l : K →* ℂˣ) (φ : G → ℂ) (b : K) :
    ∑ a : K, (((l a)⁻¹ : ℂˣ) : ℂ) * φ (a * b) =
      (l b : ℂ) * ∑ a : K, (((l a)⁻¹ : ℂˣ) : ℂ) * φ a := by
  rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulRight b⁻¹)]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Equiv.coe_mulRight, map_mul, map_inv, mul_inv_rev, inv_inv, Units.val_mul,
    Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, inv_mul_cancel, mul_one]

theorem coset_sum_eq_zero (K : Subgroup G) (l : K →* ℂˣ) {φ : G → ℂ} (hφ : IsClass φ) (h : G)
    (a₀ a₁ : K) (e : (a₁ : G) = h⁻¹ * a₀ * h) (ne : l a₁ ≠ l a₀) :
    ∑ a : K, (((l a)⁻¹ : ℂˣ) : ℂ) * φ (a * h) = 0 := by
  set F := ∑ a : K, (((l a)⁻¹ : ℂˣ) : ℂ) * φ (a * h) with hF
  have key : F = ((l a₁ * (l a₀)⁻¹ : ℂˣ) : ℂ) * F := by
    conv_lhs => rw [hF, ← Equiv.sum_comp ((Equiv.mulRight a₀).trans (Equiv.mulLeft a₁⁻¹))]
    rw [hF, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have h1 : φ (((a₁⁻¹ * (c * a₀) : K) : G) * h) = φ (c * h) := by
      rw [← hφ (c * h) (a₁ : G)⁻¹]
      congr 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc]
      congr 2
      rw [e]; group
    simp only [Equiv.trans_apply, Equiv.coe_mulRight, Equiv.coe_mulLeft]
    rw [h1]
    simp only [map_mul, map_inv, mul_inv_rev, inv_inv, Units.val_mul]
    ring
  by_contra hne
  apply ne
  have : ((l a₁ * (l a₀)⁻¹ : ℂˣ) : ℂ) = 1 := by
    have h2 : (((l a₁ * (l a₀)⁻¹ : ℂˣ) : ℂ) - 1) * F = 0 := by rw [sub_mul, ← key]; ring
    exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hne)
  exact mul_inv_eq_one.1 (Units.val_eq_one.1 this)

theorem sum_indicator (H₁ H₂ : Subgroup G) :
    ∑ b : H₂, (if (b : G) ∈ H₁ then (1 : ℂ) else 0) =
      ((Finset.univ.filter fun g : G => g ∈ H₁ ∧ g ∈ H₂).card : ℂ) := by
  rw [Finset.sum_boole]
  congr 1
  refine Finset.card_bij (fun b _ => (b : G)) ?_ ?_ ?_
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact ⟨hb, b.2⟩
  · intro a _ b _ h
    exact Subtype.ext h
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    exact ⟨⟨g, hg.2⟩, by simpa using hg.1, rfl⟩

theorem double_sum (H₁ H₂ : Subgroup G) (l₁ : H₁ →* ℂˣ) (l₂ : H₂ →* ℂˣ)
    (hag : ∀ (a : H₁) (b : H₂), (a : G) = b → l₁ a = l₂ b)
    (hM : ∀ h ∈ H₂, h ∉ H₁ → ∃ a a' : H₁, (a' : G) = h⁻¹ * a * h ∧ l₁ a' ≠ l₁ a)
    {φ : G → ℂ} (hφ : IsClass φ) :
    ∑ b : H₂, ∑ a : H₁, (((l₂ b)⁻¹ : ℂˣ) : ℂ) * ((((l₁ a)⁻¹ : ℂˣ) : ℂ) * φ (a * b)) =
      ((Finset.univ.filter fun g : G => g ∈ H₁ ∧ g ∈ H₂).card : ℂ) *
        ∑ a : H₁, (((l₁ a)⁻¹ : ℂˣ) : ℂ) * φ a := by
  rw [← sum_indicator, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.mul_sum]
  split_ifs with hb
  · have := coset_sum_mem H₁ l₁ φ ⟨b, hb⟩
    simp only at this
    rw [this, hag ⟨b, hb⟩ b rfl, ← mul_assoc, Units.inv_mul]
  · obtain ⟨a₀, a₁, e, ne⟩ := hM b b.2 hb
    rw [coset_sum_eq_zero H₁ l₁ hφ b a₀ a₁ e ne]; simp

theorem isotypic_trace_eq : ∀ (G : Type) [Group G] [Fintype G] (H H₁ H₂ : Subgroup G) (l₁ : H₁ →* ℂˣ) (l₂ : H₂ →* ℂˣ), H₁ ≤ H → H₂ ≤ H → Nat.card H₁ = Nat.card H₂ → (∀ (a : H₁) (b : H₂), (a : G) = b → l₁ a = l₂ b) → (∀ h ∈ H, h ∉ H₁ → ∃ a a' : H₁, (a' : G) = h⁻¹ * a * h ∧ l₁ a' ≠ l₁ a) → (∀ h ∈ H, h ∉ H₂ → ∃ b b' : H₂, (b' : G) = h⁻¹ * b * h ∧ l₂ b' ≠ l₂ b) → ∀ φ : G → ℂ, IsClass φ → (Nat.card H₁ : ℂ)⁻¹ * ∑ a : H₁, ((l₁ a)⁻¹ : ℂˣ) * φ a = (Nat.card H₂ : ℂ)⁻¹ * ∑ b : H₂, ((l₂ b)⁻¹ : ℂˣ) * φ b := by
  intro G _ _ H H₁ H₂ l₁ l₂ h1 h2 hc hag hM1 hM2 φ hφ
  have e1 := double_sum H₁ H₂ l₁ l₂ hag (fun h hh => hM1 h (h2 hh)) hφ
  have e2 := double_sum H₂ H₁ l₂ l₁ (fun b a e => (hag a b e.symm).symm)
    (fun h hh => hM2 h (h1 hh)) hφ
  have hf : (Finset.univ.filter fun g : G => g ∈ H₂ ∧ g ∈ H₁) =
      (Finset.univ.filter fun g : G => g ∈ H₁ ∧ g ∈ H₂) :=
    Finset.filter_congr fun g _ => and_comm
  rw [hf, Finset.sum_comm] at e2
  have hN : ((Finset.univ.filter fun g : G => g ∈ H₁ ∧ g ∈ H₂).card : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Finset.card_ne_zero]
    exact ⟨1, by simp⟩
  rw [hc]
  congr 1
  apply mul_left_cancel₀ hN
  rw [← e1, ← e2]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [isClass_mul_comm hφ (a : G) b]; ring

end GlobalTheory.GLm.OneDoubleCoset
