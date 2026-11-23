import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

theorem unit_conj_form_props {p : ℕ} [Fact p.Prime] (G : HTGroup p) (β Y c : G.Cˣ) (s : ℚ) (hβ : sh G β = β)
    (h0 : (Y : G.C) * β * sh G Y = algebraMap ℚ G.C s * β)
    (h1 : ((c : G.C) * Y * ((c⁻¹ : G.Cˣ) : G.C)) * β * sh G ((c : G.C) * Y * ((c⁻¹ : G.Cˣ) : G.C)) =
      algebraMap ℚ G.C s * β) :
    IsUnit (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) ∧
    Commute (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) (Y : G.C) ∧
    (β : G.C) * sh G (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) *
      ((β⁻¹ : G.Cˣ) : G.C) = ((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C) := by
  have shm : ∀ x z : G.C, sh G (x * z) = sh G z * sh G x := fun x z => by simp [sh]
  have shs : ∀ x : G.C, sh G (sh G x) = x := G.star_star
  have sh1 : sh G 1 = 1 := sh_one_eq G
  set u : G.C := ((c⁻¹ : G.Cˣ) : G.C) with hu
  set bi : G.C := ((β⁻¹ : G.Cˣ) : G.C) with hbi_def
  set S : G.C := algebraMap ℚ G.C s with hS
  have hA : ∀ r : G.C, u * ((c : G.C) * r) = r := fun r => by rw [← mul_assoc, hu, Units.inv_mul, one_mul]
  have hB : sh G (c : G.C) * sh G u = 1 := by rw [← shm, hu, Units.inv_mul, sh1]
  have hB' : ∀ r : G.C, sh G (c : G.C) * (sh G u * r) = r := fun r => by rw [← mul_assoc, hB, one_mul]
  have hC : ∀ r : G.C, (β : G.C) * (bi * r) = r := fun r => by rw [← mul_assoc, hbi_def, Units.mul_inv, one_mul]
  have hC' : ∀ r : G.C, bi * ((β : G.C) * r) = r := fun r => by rw [← mul_assoc, hbi_def, Units.inv_mul, one_mul]
  have hD : (β : G.C) * bi = 1 := by rw [hbi_def, Units.mul_inv]
  set shYi : G.C := sh G ((Y⁻¹ : G.Cˣ) : G.C) with hshYi
  have hE : ∀ r : G.C, sh G (Y : G.C) * (shYi * r) = r := fun r => by
    rw [← mul_assoc, hshYi, ← shm, Units.inv_mul, sh1, one_mul]
  have hE1 : sh G (Y : G.C) * shYi = 1 := by rw [hshYi, ← shm, Units.inv_mul, sh1]
  refine ⟨?_, ?_, ?_⟩
  · have hshu : IsUnit (sh G u) := ⟨⟨sh G u, sh G (c : G.C), by rw [← shm, hu, Units.mul_inv, sh1], hB⟩, rfl⟩
    exact (((Units.isUnit _).mul (Units.isUnit β)).mul hshu).mul (Units.isUnit _)
  · have h2 : (Y : G.C) * (u * β * sh G u) * sh G Y = S * (u * β * sh G u) := by
      calc (Y : G.C) * (u * β * sh G u) * sh G Y
          = u * (((c : G.C) * Y * u) * β * sh G ((c : G.C) * Y * u)) * sh G u := by
            simp only [shm, mul_assoc, hA, hB, hB', mul_one]
        _ = S * (u * β * sh G u) := by
            rw [h1, hS, ← mul_assoc, ← Algebra.commutes s u]; simp only [mul_assoc]
    have e1 : (Y : G.C) * (u * β * sh G u * bi) = S * ((u * β * sh G u) * (shYi * bi)) := by
      calc (Y : G.C) * (u * β * sh G u * bi) = ((Y : G.C) * (u * β * sh G u) * sh G Y) * (shYi * bi) := by
            simp only [mul_assoc, hE]
        _ = _ := by rw [h2, mul_assoc]
    have eY : (Y : G.C) = S * ((β : G.C) * (shYi * bi)) := by
      calc (Y : G.C) = ((Y : G.C) * β * sh G Y) * (shYi * bi) := by
            simp only [mul_assoc, hE, hD, mul_one]
        _ = _ := by rw [h0, mul_assoc]
    have e2 : (u * β * sh G u * bi) * (Y : G.C) = S * ((u * β * sh G u) * (shYi * bi)) := by
      rw [eY]
      calc u * β * sh G u * bi * (S * ((β : G.C) * (shYi * bi)))
          = (u * β * sh G u) * (bi * S * ((β : G.C) * (shYi * bi))) := by simp only [mul_assoc]
        _ = (u * β * sh G u) * (S * (bi * ((β : G.C) * (shYi * bi)))) := by
            rw [hS, ← Algebra.commutes s bi]; simp only [mul_assoc]
        _ = _ := by rw [hC', ← mul_assoc, ← mul_assoc, ← Algebra.commutes s, hS]; simp only [mul_assoc]
    exact e2.trans e1.symm
  · have hbi : sh G bi = bi := by
      have h3 : sh G (β : G.C) * sh G bi = 1 := by rw [← shm, hbi_def, Units.inv_mul, sh1]
      rw [hβ] at h3
      calc sh G bi = (bi * β) * sh G bi := by rw [hbi_def, Units.inv_mul, one_mul]
        _ = bi := by rw [mul_assoc, h3, mul_one]
    simp only [shm, shs, hβ, hbi, mul_assoc, hC]

theorem grp_conj_unit_props : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), sh G β = β → ∀ (y y₀ : grp G β) (c : G.Cˣ),
    (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C) →
    (y : G.Cˣ × ℚˣ).2 = (y₀ : G.Cˣ × ℚˣ).2 →
    IsUnit (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) ∧ Commute (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∧
    (β : G.C) * sh G (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) * ((β⁻¹ : G.Cˣ) : G.C) = (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) := by
  intro p _ G β hβ y y₀ c hy hs
  have h0 : (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * β * sh G ((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) =
      algebraMap ℚ G.C ((y₀ : G.Cˣ × ℚˣ).2 : ℚ) * β := y₀.2.1
  have h1 : (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * β * sh G ((y : G.Cˣ × ℚˣ).1 : G.Cˣ) =
      algebraMap ℚ G.C ((y : G.Cˣ × ℚˣ).2 : ℚ) * β := y.2.1
  rw [hy, hs] at h1
  exact unit_conj_form_props G β _ c _ hβ h0 h1

end GlobalTheory
