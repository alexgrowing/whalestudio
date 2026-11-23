import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFourierGau

open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

namespace GlobalTheory.RealWeil.PosDet

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem det_left {p : Matrix ι ι ℂ} (pp : p * p = p) (g : Matrix ι ι ℂ) :
    (p * g + (1 - p)).det = (p * g * p + (1 - p)).det := by
  have pp' : ∀ x, p * (p * x) = p * x := fun x => by rw [← mul_assoc, pp]
  have e : p * g + (1 - p) = (1 + p * (g * (1 - p))) * (p * g * p + (1 - p)) := by
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, pp, pp', one_mul, mul_one]; abel
  have e2 : g * (1 - p) * p = 0 := by
    simp only [mul_sub, sub_mul, mul_assoc, pp, one_mul, mul_one, sub_self]
  rw [e, det_mul, det_one_add_mul_comm, e2, add_zero, det_one, one_mul]

theorem det_right {p : Matrix ι ι ℂ} (pp : p * p = p) (g : Matrix ι ι ℂ) :
    (g * p + (1 - p)).det = (p * g * p + (1 - p)).det := by
  have pp' : ∀ x, p * (p * x) = p * x := fun x => by rw [← mul_assoc, pp]
  have e : g * p + (1 - p) = (p * g * p + (1 - p)) * (1 + ((1 - p) * g) * p) := by
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, pp, pp', one_mul, mul_one]; abel
  have e2 : p * ((1 - p) * g) = 0 := by
    simp only [mul_sub, sub_mul, pp', one_mul, sub_self]
  rw [e, det_mul, det_one_add_mul_comm, e2, add_zero, det_one, mul_one]

theorem det_compl {p : Matrix ι ι ℂ} (pp : p * p = p) {g h : Matrix ι ι ℂ} (hg : h * g = 1) :
    (p + (1 - p) * g * (1 - p)).det = (p * h + (1 - p)).det * g.det := by
  have qq : (1 - p) * (1 - p) = 1 - p := by
    simp only [mul_sub, sub_mul, pp, one_mul, mul_one]; abel
  have := det_left qq g
  rw [sub_sub_cancel] at this
  rw [add_comm p, ← this, ← det_mul, add_mul, mul_assoc p, hg, mul_one, add_comm]

theorem det_sign {p : Matrix ι ι ℂ} (pp : p * p = p) : (p - (1 - p)).det * (p - (1 - p)).det = 1 := by
  have : (p - (1 - p)) * (p - (1 - p)) = 1 := by
    simp only [mul_sub, sub_mul, pp, one_mul, mul_one]; abel
  rw [← det_mul, this, det_one]

theorem half_add_self (X : Matrix ι ι ℂ) : (1 / 2 : ℂ) • (X + X) = X := by module

theorem half_eq {p : Matrix ι ι ℂ} (pp : p * p = p) {g h : Matrix ι ι ℂ} (hg : h * g = 1) :
    (1 / 2 : ℂ) • (1 + (p - (1 - p)) * h * (p - (1 - p)) * g) =
      (p - (1 - p)) * h * (p * g * p - (1 - p) * g * (1 - p)) := by
  have pp' : ∀ x, p * (p * x) = p * x := fun x => by rw [← mul_assoc, pp]
  have hg' : ∀ x, h * (g * x) = x := fun x => by rw [← mul_assoc, hg, one_mul]
  rw [← half_add_self ((p - (1 - p)) * h * (p * g * p - (1 - p) * g * (1 - p)))]
  congr 1
  simp only [mul_sub, sub_mul, mul_assoc, pp, hg, hg', one_mul, mul_one]; abel

theorem det_diag {p : Matrix ι ι ℂ} (pp : p * p = p) (a : Matrix ι ι ℂ) {g h : Matrix ι ι ℂ} (hg : h * g = 1) :
    (p * a * p - (1 - p) * g * (1 - p)).det =
      (p - (1 - p)).det * (p * a + (1 - p)).det * ((p * h + (1 - p)).det * g.det) := by
  have pp' : ∀ x, p * (p * x) = p * x := fun x => by rw [← mul_assoc, pp]
  rw [← det_compl pp hg, det_left pp a, ← det_mul, ← det_mul]
  congr 1
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, pp, pp', one_mul, mul_one]; abel

theorem det_block {p : Matrix ι ι ℂ} (pp : p * p = p) {g₁ h₁ g₂ h₂ : Matrix ι ι ℂ} (hg₁ : h₁ * g₁ = 1)
    (hg₂ : h₂ * g₂ = 1) :
    (fromBlocks (p * g₁ * p - (1 - p) * g₁ * (1 - p)) (p * g₂) (-((1 - p) * g₁))
      (p * g₂ * p - (1 - p) * g₂ * (1 - p))).det =
      g₁.det * g₂.det * ((p * h₁ + (1 - p)).det * (p * g₂ + (1 - p)).det * (p * (h₂ * g₁) + (1 - p)).det) := by
  have pp' : ∀ x, p * (p * x) = p * x := fun x => by rw [← mul_assoc, pp]
  have gh : g₂ * h₂ = 1 := mul_eq_one_comm.1 hg₂
  have gh' : ∀ x, g₂ * (h₂ * x) = x := fun x => by rw [← mul_assoc, gh, one_mul]
  have hσ : fromBlocks p (1 - p) (1 - p) p * fromBlocks p (1 - p) (1 - p) p = 1 := by
    rw [fromBlocks_multiply, ← fromBlocks_one]
    congr 1 <;> (simp only [mul_sub, sub_mul, pp, one_mul, mul_one]; abel)
  have e : fromBlocks p (1 - p) (1 - p) p *
      fromBlocks (p * g₁ * p - (1 - p) * g₁ * (1 - p)) (p * g₂) (-((1 - p) * g₁))
      (p * g₂ * p - (1 - p) * g₂ * (1 - p)) * fromBlocks p (1 - p) (1 - p) p =
      fromBlocks ((p - (1 - p)) * g₂ * (h₂ * g₁ * p + (1 - p))) (p * g₂ * p - (1 - p) * g₁ * (1 - p)) 0
        (p * g₂ * p - (1 - p) * g₁ * (1 - p)) := by
    rw [fromBlocks_multiply, fromBlocks_multiply]
    congr 1 <;> (simp only [mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, mul_assoc, pp, pp', gh', one_mul, mul_one]; abel)
  have d := congrArg det e
  have dσ := congrArg det hσ
  rw [det_mul, det_one] at dσ
  rw [det_mul, det_mul, det_fromBlocks_zero₂₁, det_diag pp g₂ hg₁, det_mul, det_mul, det_right pp,
    ← det_left pp, mul_right_comm, dσ, one_mul] at d
  rw [d]
  linear_combination (g₁.det * g₂.det * ((p * h₁ + (1 - p)).det * (p * g₂ + (1 - p)).det *
    (p * (h₂ * g₁) + (1 - p)).det)) * det_sign pp

theorem detPlus_identities : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (s : Matrix ι ι ℂ), sᴴ = s → s * s = 1 →
    (∀ g : Matrix ι ι ℂ, gᴴ * s * g = s → dP s g⁻¹ = star (dP s g) ∧
      ((1 / 2 : ℂ) • (1 + gᴴ * g)).det = dP s g * dP s g⁻¹) ∧
    ∀ g₁ g₂ : Matrix ι ι ℂ, g₁ᴴ * s * g₁ = s → g₂ᴴ * s * g₂ = s →
      (Matrix.fromBlocks ((1 / 2 : ℂ) • (1 + g₁ᴴ * g₁)) ((1 / 2 : ℂ) • (g₁ᴴ * (1 + s) * g₂))
        ((1 / 2 : ℂ) • (g₂ᴴ * (1 - s) * g₁)) ((1 / 2 : ℂ) • (1 + g₂ᴴ * g₂))).det =
        dP s g₁⁻¹ * dP s g₂ * dP s (g₂⁻¹ * g₁) := by
  intro ι _ _ s hs ss
  obtain ⟨p, hp⟩ : ∃ p : Matrix ι ι ℂ, p = (1 / 2 : ℂ) • (1 + s) := ⟨_, rfl⟩
  have pp : p * p = p := by
    rw [hp]
    simp only [smul_mul_smul_comm, mul_add, add_mul, ss, one_mul, mul_one]
    module
  have pp' : ∀ x, p * (p * x) = p * x := fun x => by rw [← mul_assoc, pp]
  have hpH : pᴴ = p := by
    rw [hp, conjTranspose_smul, conjTranspose_add, conjTranspose_one, hs]; simp
  have hsp : s = p - (1 - p) := by rw [hp]; module
  have hd : ∀ g, dP s g = (p * g + (1 - p)).det := fun g => by
    unfold dP
    rw [hp, smul_mul_assoc]
    congr 1
    module
  have key : ∀ g : Matrix ι ι ℂ, gᴴ * s * g = s → g⁻¹ * g = 1 ∧ gᴴ = s * g⁻¹ * s := fun g hg => by
    have h1 : s * gᴴ * s * g = 1 := by rw [mul_assoc s, mul_assoc s, hg, ss]
    rw [inv_eq_left_inv h1]
    refine ⟨h1, ?_⟩
    simp only [← mul_assoc, ss, one_mul]
    rw [mul_assoc, ss, mul_one]
  have ds := det_sign pp
  simp only [hd]
  refine ⟨fun g hg => ?_, fun g₁ g₂ hg₁ hg₂ => ?_⟩
  · obtain ⟨h1, h2⟩ := key g hg
    generalize g⁻¹ = h at h1 h2
    have dh := congrArg det h1
    rw [det_mul, det_one] at dh
    constructor
    · rw [← det_conjTranspose, conjTranspose_add, conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hpH, h2]
      have : s * h * s * p + (1 - p) = s * (h * p + (1 - p)) * s := by
        rw [hsp]
        simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, pp, pp', one_mul, mul_one]; abel
      rw [this, det_mul, det_mul, det_right pp, ← det_left pp, hsp, mul_right_comm, ds, one_mul]
    · rw [h2, hsp, half_eq pp h1, det_mul, det_mul, det_diag pp g h1]
      linear_combination ((p * g + (1 - p)).det * (p * h + (1 - p)).det) * (h.det * g.det) * ds +
        ((p * g + (1 - p)).det * (p * h + (1 - p)).det) * dh
  · obtain ⟨a1, a2⟩ := key g₁ hg₁
    obtain ⟨b1, b2⟩ := key g₂ hg₂
    generalize g₁⁻¹ = h₁ at a1 a2
    generalize g₂⁻¹ = h₂ at b1 b2
    have da := congrArg det a1
    have db := congrArg det b1
    rw [det_mul, det_one] at da db
    have e : Matrix.fromBlocks ((1 / 2 : ℂ) • (1 + g₁ᴴ * g₁)) ((1 / 2 : ℂ) • (g₁ᴴ * (1 + s) * g₂))
        ((1 / 2 : ℂ) • (g₂ᴴ * (1 - s) * g₁)) ((1 / 2 : ℂ) • (1 + g₂ᴴ * g₂)) =
        fromBlocks (s * h₁) 0 0 (s * h₂) *
          fromBlocks (p * g₁ * p - (1 - p) * g₁ * (1 - p)) (p * g₂) (-((1 - p) * g₁))
            (p * g₂ * p - (1 - p) * g₂ * (1 - p)) := by
      rw [fromBlocks_multiply, a2, b2, hsp, half_eq pp a1, half_eq pp b1]
      simp only [Matrix.zero_mul, add_zero, zero_add]
      congr 1
      · rw [← half_add_self ((p - (1 - p)) * h₁ * (p * g₂))]
        congr 1
        simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, pp', one_mul, mul_one]; abel
      · rw [← half_add_self ((p - (1 - p)) * h₂ * (-((1 - p) * g₁)))]
        congr 1
        simp only [mul_sub, sub_mul, mul_neg, mul_assoc, pp', one_mul, mul_one]; abel
    rw [e, det_mul, det_fromBlocks_zero₂₁, det_block pp a1 b1, det_mul, det_mul, hsp]
    generalize (p * h₁ + (1 - p)).det * (p * g₂ + (1 - p)).det * (p * (h₂ * g₁) + (1 - p)).det = T
    linear_combination T * (h₁.det * g₁.det) * (h₂.det * g₂.det) * ds + T * (h₂.det * g₂.det) * da + T * db

end GlobalTheory.RealWeil.PosDet
