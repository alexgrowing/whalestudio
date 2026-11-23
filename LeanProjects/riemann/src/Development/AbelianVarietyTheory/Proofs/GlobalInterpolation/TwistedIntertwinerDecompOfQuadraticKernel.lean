import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN

open Formalism.MainNotions.N

namespace GlobalTheory

private theorem exists_intertwiner_decomp_of_kernel_intertwines {Γ k : Type} [Group Γ] [Field k] [CharZero k] {n : ℕ}
    (P Q : Γ → Matrix (Fin n) (Fin n) k) (hP : ∀ a b, P (a * b) = P a * P b)
    (hQ : ∀ a b, Q (a * b) = Q a * Q b) (c : Γ → k) (hc : ∀ a b, c (a * b) = c a * c b)
    (hcc : ∀ a, c a * c a = 1) (S : Subgroup Γ) (η : Γ →* ℤˣ) (X : Matrix (Fin n) (Fin n) k)
    (hX : ∀ g ∈ S, η g = 1 → P g * X = c g • (X * Q g)) :
    ∃ X₁ X₂ : Matrix (Fin n) (Fin n) k, X = X₁ + X₂ ∧ (∀ g ∈ S, P g * X₁ = c g • (X₁ * Q g)) ∧
      (∀ g ∈ S, P g * X₂ = (c g * ((η g : ℤ) : k)) • (X₂ * Q g)) := by
  by_cases h : ∀ s ∈ S, η s = 1
  · refine ⟨X, 0, by simp, fun g hg => hX g hg (h g hg), fun g _ => by simp⟩
  push Not at h
  obtain ⟨s, hs, hs1⟩ := h
  have hsm : η s = -1 := (Int.units_eq_one_or _).resolve_left hs1
  have hc1 : c 1 = 1 := by
    have h := hc 1 1
    rw [one_mul] at h
    rw [h]
    exact hcc 1
  have hcinv : ∀ a, c a⁻¹ = c a := by
    intro a
    calc c a⁻¹ = c a⁻¹ * (c a * c a) := by rw [hcc, mul_one]
      _ = c (a⁻¹ * a) * c a := by rw [hc]; ring
      _ = c a := by rw [inv_mul_cancel, hc1, one_mul]
  have hX' : ∀ t ∈ S, η t = 1 → ∀ M, P t * (X * M) = c t • (X * (Q t * M)) := by
    intro t ht het M
    rw [← Matrix.mul_assoc, hX t ht het, Matrix.smul_mul, Matrix.mul_assoc]
  set Y := c s • (P s * X * Q s⁻¹) with hY
  have key1 : ∀ g ∈ S, η g = 1 → P g * Y = c g • (Y * Q g) := by
    intro g hg he
    have ht : s⁻¹ * g * s ∈ S := S.mul_mem (S.mul_mem (S.inv_mem hs) hg) hs
    have het : η (s⁻¹ * g * s) = 1 := by simp [he]
    have hPgs : ∀ M, P g * (P s * M) = P s * (P (s⁻¹ * g * s) * M) := by
      intro M
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hP, ← hP]
      congr 2
      group
    have hQt : Q (s⁻¹ * g * s) * Q s⁻¹ = Q s⁻¹ * Q g := by
      rw [← hQ, ← hQ]
      congr 1
      group
    have hct : c (s⁻¹ * g * s) = c g := by
      rw [hc, hc, hcinv]
      calc c s * c g * c s = c g * (c s * c s) := by ring
        _ = c g := by rw [hcc, mul_one]
    simp only [hY, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hPgs, hX' _ ht het, hQt, hct,
      smul_smul, mul_comm]
  have key2 : ∀ g ∈ S, η g = -1 → P g * X = c g • (Y * Q g) ∧ P g * Y = c g • (X * Q g) := by
    intro g hg he
    have hu : s⁻¹ * g ∈ S := S.mul_mem (S.inv_mem hs) hg
    have heu : η (s⁻¹ * g) = 1 := by simp [he, hsm]
    have hv : g * s ∈ S := S.mul_mem hg hs
    have hev : η (g * s) = 1 := by simp [he, hsm]
    constructor
    · have hPg : P g = P s * P (s⁻¹ * g) := by
        rw [← hP]
        congr 1
        group
      have hQu : Q (s⁻¹ * g) = Q s⁻¹ * Q g := by
        rw [← hQ]
      have hcu : c (s⁻¹ * g) = c s * c g := by rw [hc, hcinv]
      have e1 : P g * X = P s * (P (s⁻¹ * g) * (X * 1)) := by
        rw [hPg, Matrix.mul_one, Matrix.mul_assoc]
      rw [e1, hX' _ hu heu, Matrix.mul_one, hQu, hcu]
      simp only [hY, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, smul_smul, mul_comm]
    · have hPv : ∀ M, P g * (P s * M) = P (g * s) * M := by
        intro M
        rw [← Matrix.mul_assoc, ← hP]
      have hQv : Q (g * s) * Q s⁻¹ = Q g := by
        rw [← hQ]
        congr 1
        group
      have hcv : c (g * s) = c g * c s := hc g s
      simp only [hY, Matrix.mul_smul, Matrix.mul_assoc, hPv, hX' _ hv hev, hQv, hcv,
        smul_smul]
      congr 1
      calc c s * (c g * c s) = c g * (c s * c s) := by ring
        _ = c g := by rw [hcc, mul_one]
  refine ⟨(2 : k)⁻¹ • (X + Y), (2 : k)⁻¹ • (X - Y), by module, ?_, ?_⟩
  · intro g hg
    rcases Int.units_eq_one_or (η g) with he | he
    · simp only [Matrix.mul_smul, Matrix.mul_add, Matrix.smul_mul, Matrix.add_mul, hX g hg he, key1 g hg he]
      module
    · obtain ⟨a1, a2⟩ := key2 g hg he
      simp only [Matrix.mul_smul, Matrix.mul_add, Matrix.smul_mul, Matrix.add_mul, a1, a2]
      module
  · intro g hg
    rcases Int.units_eq_one_or (η g) with he | he
    · simp only [Matrix.mul_smul, Matrix.mul_sub, Matrix.smul_mul, Matrix.sub_mul, hX g hg he, key1 g hg he,
        he, Units.val_one, Int.cast_one, mul_one]
      module
    · obtain ⟨a1, a2⟩ := key2 g hg he
      simp only [Matrix.mul_smul, Matrix.mul_sub, Matrix.smul_mul, Matrix.sub_mul, a1, a2, he, Units.val_neg,
        Units.val_one, Int.cast_neg, Int.cast_one, mul_neg, mul_one]
      module

theorem twistedIntertwiner_decomp_of_quadraticKernel :
    ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (n : ℕ) (σ σ' : Γ →* GL (Fin n) k) (S : Subgroup Γ) (χ η : Γ →* ℤˣ) (X : Matrix (Fin n) (Fin n) k), (∀ g ∈ S, η g = 1 → ((σ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X = ((χ g : ℤ) : k) • (X * ((σ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) → ∃ X₁ X₂ : Matrix (Fin n) (Fin n) k, X = X₁ + X₂ ∧ (∀ g ∈ S, ((σ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X₁ = ((χ g : ℤ) : k) • (X₁ * ((σ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) ∧ (∀ g ∈ S, ((σ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X₂ = (((χ * η) g : ℤ) : k) • (X₂ * ((σ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) := by
  intro Γ k _ _ _ n σ σ' S χ η X hX
  obtain ⟨X₁, X₂, hsum, h₁, h₂⟩ := exists_intertwiner_decomp_of_kernel_intertwines (fun g => ((σ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))
    (fun g => ((σ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (fun a b => by simp [map_mul])
    (fun a b => by simp [map_mul]) (fun g => ((χ g : ℤ) : k)) (fun a b => by simp [map_mul])
    (fun a => by rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp) S η X hX
  refine ⟨X₁, X₂, hsum, h₁, fun g hg => ?_⟩
  rw [h₂ g hg]
  simp [MonoidHom.mul_apply, Units.val_mul, Int.cast_mul]

end GlobalTheory
