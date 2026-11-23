import Mathlib

open Matrix

noncomputable section

namespace PI.AmpRootCommon

variable {n : ℕ}

theorem det_unitri {u : Matrix (Fin n) (Fin n) ℂ} (hu : u.BlockTriangular id) (hud : ∀ i, u i i = 1) :
    u.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular hu]; simp [hud]

theorem isUnit_unitri {u : Matrix (Fin n) (Fin n) ℂ} (hu : u.BlockTriangular id) (hud : ∀ i, u i i = 1) :
    IsUnit u.det := by
  rw [det_unitri hu hud]; exact isUnit_one

theorem inv_upper {u : Matrix (Fin n) (Fin n) ℂ} (hu : u.BlockTriangular id) (hud : ∀ i, u i i = 1) :
    u⁻¹.BlockTriangular id := by
  have : Invertible u := Matrix.invertibleOfIsUnitDet u (isUnit_unitri hu hud)
  exact Matrix.blockTriangular_inv_of_blockTriangular hu

theorem inv_superdiag {u : Matrix (Fin n) (Fin n) ℂ} (hu : u.BlockTriangular id) (hud : ∀ i, u i i = 1)
    (m1 m : Fin n) (hm : m1.val + 1 = m.val) : u⁻¹ m1 m = - u m1 m := by
  have hdet := isUnit_unitri hu hud
  have hw := inv_upper hu hud
  have hne : m1 ≠ m := fun e => by rw [e] at hm; omega
  have h1 : (u⁻¹ * u) m1 m = 0 := by
    rw [Matrix.nonsing_inv_mul _ hdet, Matrix.one_apply, if_neg hne]
  have h2 : (u⁻¹ * u) m1 m1 = 1 := by
    rw [Matrix.nonsing_inv_mul _ hdet, Matrix.one_apply, if_pos rfl]
  rw [Matrix.mul_apply, Finset.sum_eq_single m1] at h2
  · rw [Matrix.mul_apply, Finset.sum_eq_add m1 m hne] at h1
    · rw [hud] at h2 h1
      rw [mul_one] at h2
      rw [h2, one_mul] at h1
      linear_combination h1
    · intro c _ hc
      by_cases hlt : c.val < m1.val
      · rw [hw (show id c < id m1 from hlt), zero_mul]
      · have : m.val < c.val := by
          have h3 : c.val ≠ m1.val := fun e => hc.1 (Fin.ext e)
          have h4 : c.val ≠ m.val := fun e => hc.2 (Fin.ext e)
          omega
        rw [hu (show id m < id c from this), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb
    by_cases hlt : b.val < m1.val
    · rw [hw (show id b < id m1 from hlt), zero_mul]
    · have : m1.val < b.val := by
        have h3 : b.val ≠ m1.val := fun e => hb (Fin.ext e)
        omega
      rw [hu (show id m1 < id b from this), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

section Rel

variable {Z u u' : Matrix (Fin n) (Fin n) ℂ} {σ : Fin n → Fin n} {ζ : Fin n → ℂ}

theorem Z_row (hZ : ∀ i j, Z i j = if j = σ i then ζ i else 0) (i b : Fin n) (hb : b ≠ σ i) : Z i b = 0 := by
  rw [hZ, if_neg hb]

theorem Z_col (hσ : ∀ i, σ (σ i) = i) (hZ : ∀ i j, Z i j = if j = σ i then ζ i else 0) (a j : Fin n)
    (ha : a ≠ σ j) : Z a j = 0 := by
  rw [hZ, if_neg]; intro e; apply ha; rw [e, hσ]

theorem Z_at (hZ : ∀ i j, Z i j = if j = σ i then ζ i else 0) (i : Fin n) : Z i (σ i) = ζ i := by
  rw [hZ, if_pos rfl]

theorem Z_at' (hσ : ∀ i, σ (σ i) = i) (hZ : ∀ i j, Z i j = if j = σ i then ζ i else 0) (j : Fin n) :
    Z (σ j) j = ζ (σ j) := by
  rw [hZ, if_pos (hσ j).symm]

theorem relA (hσ : ∀ i, σ (σ i) = i) (hZ : ∀ i j, Z i j = if j = σ i then ζ i else 0)
    (hu : u.BlockTriangular id) (hud : ∀ i, u i i = 1) (hrel : uᴴ * Z * u' = Z) (i j : Fin n) :
    ζ i * u' (σ i) j = star (u⁻¹ (σ j) i) * ζ (σ j) := by
  have hdet := isUnit_unitri hu hud
  have hZu : Z * u' = (u⁻¹)ᴴ * Z := by
    calc Z * u' = ((u⁻¹)ᴴ * uᴴ) * Z * u' := by
          rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.conjTranspose_one, Matrix.one_mul]
      _ = (u⁻¹)ᴴ * (uᴴ * Z * u') := by simp only [Matrix.mul_assoc]
      _ = (u⁻¹)ᴴ * Z := by rw [hrel]
  have h := congrFun (congrFun hZu i) j
  rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (σ i), Finset.sum_eq_single (σ j)] at h
  · rw [Z_at hZ, Z_at' hσ hZ, Matrix.conjTranspose_apply] at h
    exact h
  · intro a _ ha; rw [Z_col hσ hZ a j ha, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb; rw [Z_row hZ i b hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem relB (hσ : ∀ i, σ (σ i) = i) (hZ : ∀ i j, Z i j = if j = σ i then ζ i else 0)
    (hu' : u'.BlockTriangular id) (hud' : ∀ i, u' i i = 1) (hrel : uᴴ * Z * u' = Z) (i j : Fin n) :
    star (u (σ j) i) * ζ (σ j) = ζ i * u'⁻¹ (σ i) j := by
  have hdet := isUnit_unitri hu' hud'
  have hZu : uᴴ * Z = Z * u'⁻¹ := by
    calc uᴴ * Z = uᴴ * Z * (u' * u'⁻¹) := by rw [Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = (uᴴ * Z * u') * u'⁻¹ := by simp only [Matrix.mul_assoc]
      _ = Z * u'⁻¹ := by rw [hrel]
  have h := congrFun (congrFun hZu i) j
  rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (σ j), Finset.sum_eq_single (σ i)] at h
  · rw [Z_at hZ, Z_at' hσ hZ, Matrix.conjTranspose_apply] at h
    exact h
  · intro b _ hb; rw [Z_row hZ i b hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro a _ ha; rw [Z_col hσ hZ a j ha, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem super_same (hσ : ∀ i, σ (σ i) = i) (hZ : ∀ i j, Z i j = if j = σ i then ζ i else 0)
    (hζ : ∀ i, ζ i ≠ 0) (hu : u.BlockTriangular id) (hud : ∀ i, u i i = 1) (hrel : uᴴ * Z * u' = Z)
    (i i1 : Fin n) (h1 : (σ i1).val + 1 = (σ i).val) (h2 : ζ (σ i1) = - ζ (σ i)) :
    u' i i1 = star (u (σ i1) (σ i)) := by
  have h := relA hσ hZ hu hud hrel (σ i) i1
  rw [hσ, inv_superdiag hu hud (σ i1) (σ i) h1, h2, star_neg] at h
  apply mul_left_cancel₀ (hζ (σ i))
  linear_combination h

theorem super_diff (hσ : ∀ i, σ (σ i) = i) (hZ : ∀ i j, Z i j = if j = σ i then ζ i else 0)
    (hζ : ∀ i, ζ i ≠ 0) (hu : u.BlockTriangular id) (hud : ∀ i, u i i = 1)
    (hu' : u'.BlockTriangular id) (hud' : ∀ i, u' i i = 1) (hrel : uᴴ * Z * u' = Z)
    (i i1 : Fin n) (hlt : (σ i).val < (σ i1).val) : u' i i1 = 0 ∧ u i i1 = 0 := by
  constructor
  · have h := relA hσ hZ hu hud hrel (σ i) i1
    rw [hσ, inv_upper hu hud (show id (σ i) < id (σ i1) from hlt), star_zero, zero_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (hζ _)
  · have h := relB hσ hZ hu' hud' hrel i1 (σ i)
    rw [hσ, inv_upper hu' hud' (show id (σ i) < id (σ i1) from hlt), mul_zero] at h
    have := (mul_eq_zero.mp h).resolve_right (hζ _)
    exact star_eq_zero.mp this

end Rel

section Sum

variable {m : ℕ}

def tau (σ : Fin (m + 1) → Fin (m + 1)) (i : Fin m) : Fin m :=
  if h : (σ i.succ).val + 1 = (σ i.castSucc).val then ⟨(σ i.succ).val, by have := (σ i.castSucc).isLt; omega⟩
  else i

theorem tau_val {σ : Fin (m + 1) → Fin (m + 1)} {i : Fin m} (h : (σ i.succ).val + 1 = (σ i.castSucc).val) :
    (tau σ i).val = (σ i.succ).val := by
  simp [tau, h]

theorem tau_neg {σ : Fin (m + 1) → Fin (m + 1)} {i : Fin m} (h : ¬ (σ i.succ).val + 1 = (σ i.castSucc).val) :
    tau σ i = i := by
  simp [tau, h]

theorem tau_cs {σ : Fin (m + 1) → Fin (m + 1)} {i : Fin m} (h : (σ i.succ).val + 1 = (σ i.castSucc).val) :
    (tau σ i).castSucc = σ i.succ := by
  apply Fin.ext; rw [Fin.val_castSucc, tau_val h]

theorem tau_succ {σ : Fin (m + 1) → Fin (m + 1)} {i : Fin m} (h : (σ i.succ).val + 1 = (σ i.castSucc).val) :
    (tau σ i).succ = σ i.castSucc := by
  apply Fin.ext; rw [Fin.val_succ, tau_val h, h]

theorem superdiagPairing_adjacent {σ : Fin (m + 1) → Fin (m + 1)} (hσ : ∀ i, σ (σ i) = i) {i : Fin m}
    (h : (σ i.succ).val + 1 = (σ i.castSucc).val) :
    (σ (tau σ i).succ).val + 1 = (σ (tau σ i).castSucc).val := by
  rw [tau_succ h, tau_cs h, hσ, hσ, Fin.val_castSucc, Fin.val_succ]

theorem tau_invol {σ : Fin (m + 1) → Fin (m + 1)} (hσ : ∀ i, σ (σ i) = i) : Function.Involutive (tau σ) := by
  intro i
  by_cases h : (σ i.succ).val + 1 = (σ i.castSucc).val
  · apply Fin.ext
    rw [tau_val (superdiagPairing_adjacent hσ h), tau_succ h, hσ, Fin.val_castSucc]
  · rw [tau_neg h, tau_neg h]

theorem sum_super {Z u u' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ} {σ : Fin (m + 1) → Fin (m + 1)}
    {ζ : Fin (m + 1) → ℂ} (hσ : ∀ i, σ (σ i) = i) (hZ : ∀ i j, Z i j = if j = σ i then ζ i else 0)
    (hζ : ∀ i, ζ i ≠ 0)
    (hadj : ∀ i i1 : Fin (m + 1), i1.val = i.val + 1 →
      ((σ i1).val + 1 = (σ i).val ∧ ζ (σ i1) = - ζ (σ i)) ∨ (σ i).val < (σ i1).val)
    (hu : u.BlockTriangular id) (hud : ∀ i, u i i = 1)
    (hu' : u'.BlockTriangular id) (hud' : ∀ i, u' i i = 1) (hrel : uᴴ * Z * u' = Z) :
    ∑ i : Fin m, u' i.castSucc i.succ = star (∑ i : Fin m, u i.castSucc i.succ) := by
  rw [star_sum]
  have hterm : ∀ i : Fin m, u' i.castSucc i.succ = star (u (tau σ i).castSucc (tau σ i).succ) := by
    intro i
    rcases hadj i.castSucc i.succ (by simp) with ⟨h1, h2⟩ | hlt
    · rw [tau_cs h1, tau_succ h1]
      exact super_same hσ hZ hζ hu hud hrel _ _ h1 h2
    · have hn : ¬ (σ i.succ).val + 1 = (σ i.castSucc).val := by omega
      rw [tau_neg hn]
      obtain ⟨e1, e2⟩ := super_diff hσ hZ hζ hu hud hu' hud' hrel _ _ hlt
      rw [e1, e2, star_zero]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  exact Equiv.sum_comp (Function.Involutive.toPerm (tau σ) (tau_invol hσ))
    (fun i => star (u i.castSucc i.succ))

end Sum

end PI.AmpRootCommon
