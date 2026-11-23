import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvenThetaTwoTorsionBasicProperties
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta.Double

variable {Λ : AddSubgroup ℂ}

theorem exists_evenTheta_translate_mul_sq_comb (h : IsLat Λ) {t s : ℂ} (ht : t ∉ Λ) (h2 : 2 * t ∈ Λ) (hs : s ∉ Λ) :
    ∃ α γ : ℂ, ∀ w, GL3Theta.th0 Λ t (w + s) * GL3Theta.th0 Λ t (w - s) =
      α * GL3Theta.th0 Λ t w ^ 2 + γ * sgStar Λ w ^ 2 := by
  have hs0 := (h.sg_eq_zero s).not.2 hs
  have ht0 := (h.sg_eq_zero t).not.2 ht
  set E : ℂ → ℂ := fun u => Complex.exp (-(Real.pi : ℂ) * u * (starRingEnd ℂ) t / (area Λ : ℂ) -
    (Real.pi : ℂ) * t * (starRingEnd ℂ) t / (2 * (area Λ : ℂ))) with hE
  set K : ℂ := Complex.exp ((Real.pi : ℂ) * t * (starRingEnd ℂ) t / (area Λ : ℂ)) with hK
  set c : ℂ := U1 Λ t (sgStar Λ) 0 with hc
  have hθ : ∀ u, GL3Theta.th0 Λ t u = sgStar Λ (u + t) * E u * c⁻¹ := fun u => rfl
  refine ⟨-sgStar Λ s ^ 2 * (wpF Λ t - wpF Λ s),
    -sgStar Λ s ^ 2 * c⁻¹ ^ 2 * K / sgStar Λ t ^ 2, fun w => ?_⟩
  have e1 : E (w + s) * E (w - s) = E w ^ 2 := by
    simp only [hE]
    rw [sq, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  have e2 : sgStar Λ (w + 2 * t) * E w ^ 2 = -K * sgStar Λ w := by
    have hl := h.sg_law h2 w
    rw [if_neg (by simpa using ht)] at hl
    rw [show -K * sgStar Λ w = (-1 * sgStar Λ w) * K by ring, ← hl]
    simp only [U1, hE, hK]
    rw [mul_assoc (sgStar Λ _), sq, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    simp only [map_mul, map_ofNat]
    ring
  have e3 := h.sqTh_sub hs ht (w + t)
  rw [sqTh, sqTh, show t + (w + t) = w + 2 * t by ring, show t - (w + t) = -w by ring,
    show s + (w + t) = w + s + t by ring, show s - (w + t) = -(w - s + t) by ring,
    h.sg_neg, h.sg_neg, div_eq_iff (pow_ne_zero 2 hs0)] at e3
  rw [hθ, hθ, hθ]
  linear_combination (sgStar Λ (w + s + t) * sgStar Λ (w - s + t) * c⁻¹ ^ 2) * e1 -
    (E w ^ 2 * c⁻¹ ^ 2) * e3 +
    (sgStar Λ s ^ 2 * c⁻¹ ^ 2 * sgStar Λ w / sgStar Λ t ^ 2) * e2

theorem evenTheta_double_translate_mul : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → ∀ s, s ∉ Λ → ∀ z, U1 Λ s (sgStar Λ) 0 ^ 2 * (U1 Λ (2 * s) (GL3Theta.th0 Λ t₀) z * GL3Theta.th0 Λ t₀ z) = U1 Λ s (sgStar Λ) 0 ^ 2 * U1 Λ s (GL3Theta.th0 Λ t₀) 0 ^ 2 * U1 Λ s (GL3Theta.th0 Λ t₀) z ^ 2 + (U1 Λ (2 * s) (GL3Theta.th0 Λ t₀) 0 - U1 Λ s (GL3Theta.th0 Λ t₀) 0 ^ 4) * U1 Λ s (sgStar Λ) z ^ 2 := by
  intro Λ h t ht h2 s hs z
  obtain ⟨α, γ, hp⟩ := exists_evenTheta_translate_mul_sq_comb h ht h2 hs
  obtain ⟨-, h1, hev, -⟩ := evenThetaTwoTorsion_basic_properties Λ h t ht h2
  have hα : α = GL3Theta.th0 Λ t s ^ 2 := by
    have := hp 0
    rw [zero_add, zero_sub, hev, h1, (h.sg_eq_zero 0).2 Λ.zero_mem] at this
    linear_combination -this
  set F : ℂ → ℂ := fun u => Complex.exp (-(Real.pi : ℂ) * u * (starRingEnd ℂ) s / (area Λ : ℂ) -
    (Real.pi : ℂ) * s * (starRingEnd ℂ) s / (2 * (area Λ : ℂ))) with hF
  have hU : ∀ (G : ℂ → ℂ) u, U1 Λ s G u = G (u + s) * F u := fun _ _ => rfl
  have hU2 : ∀ (G : ℂ → ℂ) u, U1 Λ (2 * s) G u = G (u + s + s) * (F u ^ 2 * F 0 ^ 2) := by
    intro G u
    simp only [U1, hF]
    rw [sq, sq, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    · ring
    · simp only [map_mul, map_ofNat]
      ring
  have p1 := hp (z + s)
  have p0 := hp (0 + s)
  rw [add_sub_cancel_right, hα] at p1 p0
  rw [h1] at p0
  simp only [hU, hU2]
  simp only [zero_add] at p0 ⊢
  linear_combination (sgStar Λ s ^ 2 * F 0 ^ 4 * F z ^ 2) * p1 -
    (F 0 ^ 4 * F z ^ 2 * sgStar Λ (z + s) ^ 2) * p0

end GlobalTheory.EvenTheta.Double
