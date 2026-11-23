import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory

theorem isSemisimpleRing_of_posForm_adjoint_closed :
    ∀ (r : ℕ) (Q : Matrix (Fin r) (Fin r) ℂ) (S : Subalgebra ℂ (Matrix (Fin r) (Fin r) ℂ)), Q.IsHermitian →
      (∀ z : Fin r → ℂ, z ≠ 0 → 0 < (star z ⬝ᵥ (Q *ᵥ z)).re) →
      (∀ x ∈ S, ∃ y ∈ S, Q * y = xᴴ * Q) → IsSemisimpleRing S := by
  intro r Q S hQ hpos hadj
  have hnd : ∀ w : Fin r → ℂ, star w ⬝ᵥ (Q *ᵥ w) = 0 → w = 0 := by
    intro w hw
    by_contra hne
    have := hpos w hne
    rw [hw] at this
    simp at this
  have key : ∀ (b : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ),
      star (b *ᵥ w) ⬝ᵥ (Q *ᵥ (b *ᵥ w)) = star w ⬝ᵥ ((bᴴ * Q * b) *ᵥ w) := by
    intro b w
    simp only [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have step : ∀ b : Matrix (Fin r) (Fin r) ℂ, Q * b = bᴴ * Q →
      ∀ w : Fin r → ℂ, (b * b) *ᵥ w = 0 → b *ᵥ w = 0 := by
    intro b hb w hw
    apply hnd
    rw [key, show bᴴ * Q * b = Q * (b * b) by rw [← hb, Matrix.mul_assoc], ← Matrix.mulVec_mulVec, hw,
      Matrix.mulVec_zero, dotProduct_zero]
  haveI : IsArtinianRing S := IsArtinianRing.of_finite ℂ _
  rw [IsArtinianRing.isSemisimpleRing_iff_jacobson, eq_bot_iff]
  intro x hx
  rw [Ideal.mem_bot]
  obtain ⟨y, hyS, hy⟩ := hadj x.1 x.2
  let y' : S := ⟨y, hyS⟩
  have hyx : y' * x ∈ Ring.jacobson S := Ideal.mul_mem_left _ _ hx
  obtain ⟨n, hn⟩ : IsNilpotent (Ring.jacobson S) := IsSemiprimaryRing.isNilpotent
  have h1 : (y' * x) ^ n = 0 := by
    have := Ideal.pow_mem_pow hyx n
    rw [hn] at this
    simpa using this
  have h2 : (y * x.1) ^ n = 0 := by simpa [y'] using congrArg Subtype.val h1
  have hsa : Q * (y * x.1) = (y * x.1)ᴴ * Q := by
    have e1 : yᴴ * Q = Q * x.1 := by
      have := congrArg Matrix.conjTranspose hy
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hQ.eq,
        Matrix.conjTranspose_conjTranspose] at this
      exact this
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, e1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hy]
  have hz : ∀ m : ℕ, (y * x.1) ^ (m + 1) = 0 → y * x.1 = 0 := by
    intro m
    induction m with
    | zero => intro h; simpa using h
    | succ m ih =>
      intro hm
      apply ih
      rw [Matrix.ext_iff_mulVec]
      intro v
      have e2 : ((y * x.1) * (y * x.1)) *ᵥ ((y * x.1) ^ m *ᵥ v) = 0 := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, ← pow_succ', ← pow_succ', hm, Matrix.zero_mulVec]
      rw [Matrix.zero_mulVec, pow_succ', ← Matrix.mulVec_mulVec]
      exact step _ hsa _ e2
  have ha : y * x.1 = 0 := hz n (by rw [pow_succ, h2, zero_mul])
  apply Subtype.ext
  rw [Matrix.ext_iff_mulVec]
  intro w
  rw [ZeroMemClass.coe_zero, Matrix.zero_mulVec]
  apply hnd
  rw [key, ← hy, Matrix.mul_assoc, ha, Matrix.mul_zero, Matrix.zero_mulVec, dotProduct_zero]

end GlobalTheory
