import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx

theorem grp_similitude_herm : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ)
    (y : grp G β), ((toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ))ᴴ * herm G v β *
      (toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) = (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℂ)) • herm G v β := by
  intro p _ G v β y
  obtain ⟨⟨u, s⟩, hy, _⟩ := y
  change (u : G.C) * β * sh G u = algebraMap ℚ G.C s * β at hy
  have hV : ((toV G v β ⟨(u, s), hy, ‹_›⟩ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) = G.psi v (u : G.C) := rfl
  rw [hV]
  change (G.psi v (u : G.C))ᴴ * (G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) * G.psi v (u : G.C) =
    ((s : ℚ) : ℂ) • (G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C))
  have hgu : IsUnit (G.gram v).det := isUnit_iff_ne_zero.mpr (G.gram_det v)
  have hgg : G.gram v * (G.gram v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  have hgg' : (G.gram v)⁻¹ * G.gram v = 1 := Matrix.nonsing_inv_mul _ hgu
  have hH : ∀ x : G.C, (G.psi v x)ᴴ = G.gram v * G.psi v (sh G x) * (G.gram v)⁻¹ := by
    intro x
    have e : G.psi v (sh G x) = (G.gram v)⁻¹ * (G.psi v x)ᴴ * G.gram v := G.psi_star v x
    rw [e, ← mul_assoc, ← mul_assoc, hgg, one_mul, mul_assoc, hgg, mul_one]

  have hu : sh G (u : G.C) * ((β⁻¹ : G.Cˣ) : G.C) * u =
      algebraMap ℚ G.C (s : ℚ) * ((β⁻¹ : G.Cˣ) : G.C) := by
    apply (Units.mul_right_inj (u * β)).mp
    rw [Units.val_mul, ← Algebra.smul_def]
    calc (u : G.C) * β * (sh G (u : G.C) * ((β⁻¹ : G.Cˣ) : G.C) * u)
        = ((u : G.C) * β * sh G (u : G.C)) * ((β⁻¹ : G.Cˣ) : G.C) * u := by
          simp only [mul_assoc]
      _ = (s : ℚ) • ((β : G.C) * ((β⁻¹ : G.Cˣ) : G.C) * u) := by
          rw [hy, ← Algebra.smul_def]; simp only [smul_mul_assoc]
      _ = (s : ℚ) • ((u : G.C) * β * ((β⁻¹ : G.Cˣ) : G.C)) := by
          rw [Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [mul_smul_comm, mul_assoc]
  rw [hH]
  calc G.gram v * G.psi v (sh G (u : G.C)) * (G.gram v)⁻¹ * (G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) *
        G.psi v (u : G.C)
      = G.gram v * (G.psi v (sh G (u : G.C)) * ((G.gram v)⁻¹ * G.gram v) *
          G.psi v ((β⁻¹ : G.Cˣ) : G.C) * G.psi v (u : G.C)) := by simp only [mul_assoc]
    _ = G.gram v * G.psi v (sh G (u : G.C) * ((β⁻¹ : G.Cˣ) : G.C) * u) := by
        rw [hgg', mul_one, map_mul, map_mul]
    _ = G.gram v * (((s : ℚ) : ℚ) • G.psi v ((β⁻¹ : G.Cˣ) : G.C)) := by
        rw [hu, map_mul, RingHom.map_rat_algebraMap, ← Algebra.smul_def]
    _ = _ := by rw [mul_smul_comm, Rat.cast_smul_eq_qsmul]

end GlobalTheory.LKCx
