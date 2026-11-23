import Mathlib

namespace GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi

open Matrix

noncomputable section

set_option linter.unusedSectionVars false

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def leftInv (H : Matrix ι ι ℂ) (B : Matrix ι κ ℂ) : Matrix κ ι ℂ := (Bᴴ * H * B)⁻¹ * Bᴴ * H

def leviSec (H : Matrix ι ι ℂ) (B : Matrix ι κ ℂ) (m : Matrix κ κ ℂ) : Matrix ι ι ℂ :=
  1 - B * leftInv H B + B * m * leftInv H B

def leviProj (H : Matrix ι ι ℂ) (B : Matrix ι κ ℂ) (g : Matrix ι ι ℂ) : Matrix κ κ ℂ :=
  leftInv H B * g * B

section Forms

variable {κ' : Type*} [Fintype κ']

theorem sesq_mul (H : Matrix ι ι ℂ) (M : Matrix ι κ ℂ) (N : Matrix ι κ' ℂ) (c : κ → ℂ)
    (d : κ' → ℂ) : star c ⬝ᵥ ((Mᴴ * H * N) *ᵥ d) = star (M *ᵥ c) ⬝ᵥ (H *ᵥ (N *ᵥ d)) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

theorem ext_sesq {M N : Matrix κ κ ℂ}
    (h : ∀ c d : κ → ℂ, star c ⬝ᵥ (M *ᵥ d) = star c ⬝ᵥ (N *ᵥ d)) : M = N := by
  rw [ext_iff_mulVec]
  intro d
  funext i
  have := h (Pi.single i 1) d
  simpa [dotProduct, Pi.single_apply] using this

theorem ip_swap {H : Matrix ι ι ℂ} (hH : Hᴴ = H) (a b : ι → ℂ) :
    star b ⬝ᵥ (H *ᵥ a) = star (star a ⬝ᵥ (H *ᵥ b)) := by
  rw [← star_dotProduct, star_mulVec, ← dotProduct_mulVec, hH]

theorem ip_unitary {H g : Matrix ι ι ℂ} (hg : gᴴ * H * g = H) (a b : ι → ℂ) :
    star (g *ᵥ a) ⬝ᵥ (H *ᵥ (g *ᵥ b)) = star a ⬝ᵥ (H *ᵥ b) := by
  rw [← sesq_mul, hg]

end Forms

section Section

variable {H : Matrix ι ι ℂ} {B : Matrix ι κ ℂ}

theorem leftInv_mul (hG : IsUnit (Bᴴ * H * B).det) : leftInv H B * B = 1 := by
  have := nonsing_inv_mul _ hG
  unfold leftInv
  simp only [Matrix.mul_assoc] at this ⊢
  exact this

theorem leftInv_mul_mul (hG : IsUnit (Bᴴ * H * B).det) {α : Type*} (N : Matrix κ α ℂ) :
    leftInv H B * (B * N) = N := by
  rw [← Matrix.mul_assoc, leftInv_mul hG, Matrix.one_mul]

theorem gram_mul_leftInv (hG : IsUnit (Bᴴ * H * B).det) :
    Bᴴ * H * B * leftInv H B = Bᴴ * H := by
  unfold leftInv
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hG, Matrix.one_mul]

theorem leftInv_mulVec_eq_zero {X : ι → ℂ} (hBX : Bᴴ *ᵥ (H *ᵥ X) = 0) : leftInv H B *ᵥ X = 0 := by
  simp only [leftInv, ← mulVec_mulVec, hBX, mulVec_zero]

theorem leviSec_mul (hG : IsUnit (Bᴴ * H * B).det) (m m' : Matrix κ κ ℂ) :
    leviSec H B (m * m') = leviSec H B m * leviSec H B m' := by
  unfold leviSec
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one, Matrix.mul_assoc, leftInv_mul_mul hG]
  abel

theorem leviSec_one : leviSec H B 1 = 1 := by
  simp [leviSec]

theorem leviProj_leviSec (hG : IsUnit (Bᴴ * H * B).det) (m : Matrix κ κ ℂ) :
    leviProj H B (leviSec H B m) = m := by
  have h2 := leftInv_mul hG (H := H) (B := B)
  unfold leviProj leviSec
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one, Matrix.mul_assoc, leftInv_mul_mul hG, h2]
  abel

theorem leviSec_mulVec_of {X : ι → ℂ} (hBX : Bᴴ *ᵥ (H *ᵥ X) = 0) (m : Matrix κ κ ℂ) :
    leviSec H B m *ᵥ X = X := by
  have hAX := leftInv_mulVec_eq_zero hBX
  simp only [leviSec, add_mulVec, sub_mulVec, Matrix.one_mulVec, ← mulVec_mulVec, hAX, mulVec_zero,
    sub_zero, add_zero]

theorem leviSec_mul_B (hG : IsUnit (Bᴴ * H * B).det) (m : Matrix κ κ ℂ) :
    leviSec H B m * B = B * m := by
  have h2 := leftInv_mul hG (H := H) (B := B)
  unfold leviSec
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]
  abel

theorem leviSection_unitary_identity (hH : Hᴴ = H) (hG : IsUnit (Bᴴ * H * B).det) (m : Matrix κ κ ℂ)
    (hm : mᴴ * (Bᴴ * H * B) * m = Bᴴ * H * B) :
    (leviSec H B m)ᴴ * H * leviSec H B m =
      (1 - B * leftInv H B)ᴴ * (H * (1 - B * leftInv H B)) +
        (leftInv H B)ᴴ * (Bᴴ * (H * (B * leftInv H B))) := by
  have K : Bᴴ * (H * (1 - B * leftInv H B)) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc H, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, gram_mul_leftInv hG, sub_self]
  have K' : ∀ N : Matrix κ ι ℂ, (1 - B * leftInv H B)ᴴ * (H * (B * N)) = 0 := by
    intro N
    have := congrArg conjTranspose K
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hH, conjTranspose_zero]
      at this
    rw [← Matrix.mul_assoc H, ← Matrix.mul_assoc, ← Matrix.mul_assoc, this, Matrix.zero_mul]
  have hmx : ∀ N : Matrix κ ι ℂ, mᴴ * (Bᴴ * (H * (B * (m * N)))) = Bᴴ * (H * (B * N)) := by
    intro N
    have := congrArg (· * N) hm
    simp only [Matrix.mul_assoc] at this
    exact this
  unfold leviSec
  rw [conjTranspose_add, conjTranspose_mul, conjTranspose_mul]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, K, K', hmx, Matrix.mul_zero,
    add_zero, zero_add]

theorem leviSec_unitary (hH : Hᴴ = H) (hG : IsUnit (Bᴴ * H * B).det) (m : Matrix κ κ ℂ)
    (hm : mᴴ * (Bᴴ * H * B) * m = Bᴴ * H * B) :
    (leviSec H B m)ᴴ * H * leviSec H B m = H := by
  have e1 := leviSection_unitary_identity hH hG 1 (by simp)
  rw [leviSec_one, conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at e1
  rw [leviSection_unitary_identity hH hG m hm, ← e1]

end Section

section Projection

variable {H : Matrix ι ι ℂ} {B : Matrix ι κ ℂ} {X Y : ι → ℂ}

theorem ip_B_left (hBX : Bᴴ *ᵥ (H *ᵥ X) = 0) (c : κ → ℂ) :
    star (B *ᵥ c) ⬝ᵥ (H *ᵥ X) = 0 := by
  rw [star_mulVec, ← dotProduct_mulVec, hBX, dotProduct_zero]

theorem ip_B_right (hH : Hᴴ = H) (hBX : Bᴴ *ᵥ (H *ᵥ X) = 0) (c : κ → ℂ) :
    star X ⬝ᵥ (H *ᵥ (B *ᵥ c)) = 0 := by
  rw [ip_swap hH, ip_B_left hBX, star_zero]

theorem eq_decomp (hH : Hᴴ = H) (hG : IsUnit (Bᴴ * H * B).det) (hBX : Bᴴ *ᵥ (H *ᵥ X) = 0)
    (hBY : Bᴴ *ᵥ (H *ᵥ Y) = 0) (hXX : star X ⬝ᵥ (H *ᵥ X) = 0) (hYY : star Y ⬝ᵥ (H *ᵥ Y) = 0)
    (hXY : star X ⬝ᵥ (H *ᵥ Y) = 1) (hspan : ∀ z, ∃ (a b : ℂ) (c : κ → ℂ), z = a • X + b • Y + B *ᵥ c)
    (z : ι → ℂ) :
    z = (star Y ⬝ᵥ (H *ᵥ z)) • X + (star X ⬝ᵥ (H *ᵥ z)) • Y + B *ᵥ (leftInv H B *ᵥ z) := by
  obtain ⟨a, b, c, rfl⟩ := hspan z
  have hYX : star Y ⬝ᵥ (H *ᵥ X) = 1 := by rw [ip_swap hH, hXY, star_one]
  have hAX := leftInv_mulVec_eq_zero hBX
  have hAY := leftInv_mulVec_eq_zero hBY
  have h2 := leftInv_mul hG (H := H) (B := B)
  simp only [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul, hYX, hYY, hXX,
    hXY, ip_B_right hH hBX, ip_B_right hH hBY, hAX, hAY, smul_zero, zero_add, mul_one, mul_zero,
    add_zero]
  rw [show leftInv H B *ᵥ (B *ᵥ c) = c by rw [mulVec_mulVec, h2, one_mulVec]]

variable (hH : Hᴴ = H) (hG : IsUnit (Bᴴ * H * B).det) (hBX : Bᴴ *ᵥ (H *ᵥ X) = 0)
    (hBY : Bᴴ *ᵥ (H *ᵥ Y) = 0) (hXX : star X ⬝ᵥ (H *ᵥ X) = 0) (hYY : star Y ⬝ᵥ (H *ᵥ Y) = 0)
    (hXY : star X ⬝ᵥ (H *ᵥ Y) = 1) (hspan : ∀ z, ∃ (a b : ℂ) (c : κ → ℂ), z = a • X + b • Y + B *ᵥ c)
include hH hG hBX hBY hXX hYY hXY hspan

theorem mulVec_leftInv_of (z : ι → ℂ) (hz : star X ⬝ᵥ (H *ᵥ z) = 0) :
    B *ᵥ (leftInv H B *ᵥ z) = z - (star Y ⬝ᵥ (H *ᵥ z)) • X := by
  have := eq_decomp hH hG hBX hBY hXX hYY hXY hspan z
  rw [hz, zero_smul, add_zero] at this
  rw [eq_sub_iff_add_eq, add_comm]
  exact this.symm

theorem ip_X_unitary_B {g : Matrix ι ι ℂ} (hg : gᴴ * H * g = H) (hgX : g *ᵥ X = X) (c : κ → ℂ) :
    star X ⬝ᵥ (H *ᵥ (g *ᵥ (B *ᵥ c))) = 0 := by
  conv_lhs => rw [← hgX]
  rw [ip_unitary hg, ip_B_right hH hBX]

theorem leviProj_mul {g g' : Matrix ι ι ℂ} (hg : gᴴ * H * g = H) (hgX : g *ᵥ X = X)
    (hg' : g'ᴴ * H * g' = H) (hgX' : g' *ᵥ X = X) :
    leviProj H B (g * g') = leviProj H B g * leviProj H B g' := by
  rw [ext_iff_mulVec]
  intro c
  have hAX := leftInv_mulVec_eq_zero hBX
  have e := mulVec_leftInv_of hH hG hBX hBY hXX hYY hXY hspan (g' *ᵥ (B *ᵥ c))
    (ip_X_unitary_B hH hG hBX hBY hXX hYY hXY hspan hg' hgX' c)
  simp only [leviProj, ← mulVec_mulVec]
  rw [e, mulVec_sub, mulVec_smul, hgX, mulVec_sub, mulVec_smul, hAX, smul_zero, sub_zero]

theorem leviProj_unitary {g : Matrix ι ι ℂ} (hg : gᴴ * H * g = H) (hgX : g *ᵥ X = X) :
    (leviProj H B g)ᴴ * (Bᴴ * H * B) * leviProj H B g = Bᴴ * H * B := by
  apply ext_sesq
  intro c d
  have ec := mulVec_leftInv_of hH hG hBX hBY hXX hYY hXY hspan (g *ᵥ (B *ᵥ c))
    (ip_X_unitary_B hH hG hBX hBY hXX hYY hXY hspan hg hgX c)
  have ed := mulVec_leftInv_of hH hG hBX hBY hXX hYY hXY hspan (g *ᵥ (B *ᵥ d))
    (ip_X_unitary_B hH hG hBX hBY hXX hYY hXY hspan hg hgX d)
  have h1 : star (g *ᵥ (B *ᵥ c)) ⬝ᵥ (H *ᵥ X) = 0 := by
    conv_lhs => rw [← hgX]
    rw [ip_unitary hg, ip_B_left hBX]
  have h2 := ip_X_unitary_B hH hG hBX hBY hXX hYY hXY hspan hg hgX d
  rw [sesq_mul, sesq_mul, sesq_mul]
  simp only [leviProj, ← mulVec_mulVec]
  rw [ec, ed]
  simp only [star_sub, star_smul, mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub,
    smul_dotProduct, dotProduct_smul, h1, h2, hXX, smul_zero, sub_zero, smul_eq_mul]
  rw [ip_unitary hg]
  simp only [mul_zero, sub_zero]

theorem leviProj_eq_one_iff {g : Matrix ι ι ℂ} (hg : gᴴ * H * g = H) (hgX : g *ᵥ X = X) :
    leviProj H B g = 1 ↔
      ∀ z : ι → ℂ, star X ⬝ᵥ (H *ᵥ z) = 0 → ∃ c : ℂ, g *ᵥ z = z + c • X := by
  have hAX := leftInv_mulVec_eq_zero hBX
  constructor
  · intro h1 z hz
    set u := leftInv H B *ᵥ z with hu
    have e1 : z = (star Y ⬝ᵥ (H *ᵥ z)) • X + B *ᵥ u := by
      rw [hu, mulVec_leftInv_of hH hG hBX hBY hXX hYY hXY hspan z hz]
      abel
    have e2 := mulVec_leftInv_of hH hG hBX hBY hXX hYY hXY hspan (g *ᵥ (B *ᵥ u))
      (ip_X_unitary_B hH hG hBX hBY hXX hYY hXY hspan hg hgX u)
    have e3 : leftInv H B *ᵥ (g *ᵥ (B *ᵥ u)) = u := by
      rw [mulVec_mulVec, mulVec_mulVec]
      change leviProj H B g *ᵥ u = u
      rw [h1, one_mulVec]
    rw [e3, eq_sub_iff_add_eq] at e2
    refine ⟨star Y ⬝ᵥ (H *ᵥ (g *ᵥ (B *ᵥ u))), ?_⟩
    conv_lhs => rw [e1]
    rw [mulVec_add, mulVec_smul, hgX]
    conv_rhs => rw [e1]
    rw [add_assoc, e2]
  · intro h1
    rw [ext_iff_mulVec]
    intro d
    obtain ⟨c, hc⟩ := h1 (B *ᵥ d) (ip_B_right hH hBX d)
    simp only [leviProj, ← mulVec_mulVec]
    rw [hc, mulVec_add, mulVec_smul, hAX, smul_zero, add_zero, mulVec_mulVec, leftInv_mul hG,
      one_mulVec]

theorem eq_leviSec {G : Matrix ι ι ℂ} {m : Matrix κ κ ℂ} (hGX : G *ᵥ X = X) (hGY : G *ᵥ Y = Y)
    (hGB : G * B = B * m) : G = leviSec H B m := by
  rw [ext_iff_mulVec]
  intro z
  rw [eq_decomp hH hG hBX hBY hXX hYY hXY hspan z]
  simp only [mulVec_add, mulVec_smul, hGX, hGY, leviSec_mulVec_of hBX, leviSec_mulVec_of hBY,
    mulVec_mulVec, ← Matrix.mul_assoc, hGB, leviSec_mul_B hG]

end Projection

end

end GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
