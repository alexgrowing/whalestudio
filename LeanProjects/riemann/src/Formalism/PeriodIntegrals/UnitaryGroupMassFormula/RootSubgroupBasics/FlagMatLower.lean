import Formalism.SharpRestriction.CuspSpanNormBounds.RootMeasBig

open Matrix

noncomputable section

namespace PI.AmpRootCommon

open Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

def hτ (k r : ℕ) (i : ℕ) : ℕ := if r ≤ i ∧ i ≤ r + k then i else 2 * r + k - i

def hs (k r : ℕ) (i : ℕ) : ℂ := if i = r + k then -1 else 1

theorem Hpk_apply (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = hτ k r i.val then hs k r i.val else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, hτ, hs, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hτ_lt (i : ℕ) (hi : i < 2 * r + k + 1) : hτ k r i < 2 * r + k + 1 := by
  unfold hτ
  split_ifs <;> omega

theorem hτ_hτ (i : ℕ) (hi : i < 2 * r + k + 1) : hτ k r (hτ k r i) = i := by
  unfold hτ
  split_ifs <;> omega

theorem hs_hτ (i : ℕ) (hi : i < 2 * r + k + 1) : hs k r (hτ k r i) = hs k r i := by
  unfold hs hτ
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hs_sq (i : ℕ) : hs k r i * hs k r i = 1 := by
  unfold hs
  split_ifs <;> norm_num

theorem Hpk_mul_self : Hpk k r * Hpk k r = 1 := by
  ext i j
  have hi := i.isLt
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨hτ k r i.val, hτ_lt i.val hi⟩ : Fin (2 * r + k + 1))]
  · rw [Hpk_apply, Hpk_apply, Matrix.one_apply]
    show (if hτ k r i.val = hτ k r i.val then hs k r i.val else 0) *
      (if j.val = hτ k r (hτ k r i.val) then hs k r (hτ k r i.val) else 0) = if i = j then 1 else 0
    rw [if_pos rfl, hτ_hτ i.val hi, hs_hτ i.val hi]
    by_cases hij : i = j
    · rw [if_pos (congrArg Fin.val hij).symm, if_pos hij, hs_sq]
    · rw [if_neg (fun h => hij (Fin.ext h.symm)), if_neg hij, mul_zero]
  · intro l _ hl
    rw [Hpk_apply, if_neg (fun h => hl (Fin.ext h)), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem uh_left {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, Hpk_mul_self]

theorem uh_inv_mul {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g (Matrix.isUnit_det_of_left_inverse (uh_left hg))

theorem uh_mul_inv {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse (uh_left hg))

def Fm (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) ℂ :=
  Matrix.of fun i b => fvec k r z b i

theorem zhat_eq (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Zhat k r z z' g = (Fm k r z)ᴴ * (Hpk k r * g) * Fm k r z' := by
  ext a b
  simp only [Zhat, herm, Fm, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, dotProduct,
    Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact Finset.sum_comm

theorem flagMat_lower {z : Fin (2 * r + k + 1) → ℂ} {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ Nset k r) (i j : Fin (r + 1)) (hji : j ≤ i) : flagMat k r z a i j = if i = j then 1 else 0 := by
  have hji' : j.val ≤ i.val := hji
  have hcol : ∀ (c d : Fin (2 * r + k + 1)), (a *ᵥ Pi.single c (1 : ℂ)) d = a d c := by
    intro c d
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  simp only [flagMat]
  by_cases hi : i.val < r
  · rw [dif_pos hi]
    have hj : j.val < r := lt_of_le_of_lt hji' hi
    have hf : fvec k r z j = bvec (eI k r ⟨j.val, hj⟩) := by
      unfold fvec
      rw [dif_pos hj]
    rw [hf]
    unfold bvec
    rw [hcol, ha.2.1 ⟨j.val, hj⟩ (eI k r ⟨i.val, hi⟩) hji']
    by_cases hij : i = j
    · subst hij
      simp
    · rw [if_neg hij, if_neg]
      intro h
      apply hij
      have h' := congrArg Fin.val h
      exact Fin.ext h'
  · rw [dif_neg hi]

theorem flagMat_upper {z : Fin (2 * r + k + 1) → ℂ} {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ Nset k r) : (flagMat k r z a).BlockTriangular id := by
  intro i j hij
  have hij' : j < i := hij
  rw [flagMat_lower ha i j (le_of_lt hij'), if_neg (ne_of_gt hij')]

theorem flagMat_diag {z : Fin (2 * r + k + 1) → ℂ} {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ Nset k r) (i : Fin (r + 1)) : flagMat k r z a i i = 1 := by
  rw [flagMat_lower ha i i le_rfl, if_pos rfl]

theorem mul_Fm {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ Nset k r) :
    a * Fm k r z = Fm k r z * flagMat k r z a := by
  ext i b
  have hF1 : ∀ c : Fin r, fvec k r z (Fin.castSucc c) = bvec (eI k r c) := by
    intro c
    unfold fvec
    rw [dif_pos (show (Fin.castSucc c).val < r from c.isLt)]
    rfl
  have hF2 : fvec k r z (Fin.last r) = z := by
    unfold fvec
    rw [dif_neg (show ¬ (Fin.last r).val < r from lt_irrefl r)]
  have hM1 : ∀ c : Fin r, flagMat k r z a (Fin.castSucc c) b = (a *ᵥ fvec k r z b) (eI k r c) := by
    intro c
    simp only [flagMat]
    rw [dif_pos (show (Fin.castSucc c).val < r from c.isLt)]
    rfl
  have hM2 : flagMat k r z a (Fin.last r) b = if Fin.last r = b then 1 else 0 := by
    simp only [flagMat]
    rw [dif_neg (show ¬ (Fin.last r).val < r from lt_irrefl r)]
  have hL : (a * Fm k r z) i b = (a *ᵥ fvec k r z b) i := by
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fm, Matrix.of_apply]
  rw [hL, Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp only [Fm, Matrix.of_apply, hF1, hF2, hM1, hM2, bvec]
  by_cases hi : i.val < r
  · have hei : eI k r ⟨i.val, hi⟩ = i := Fin.ext rfl
    rw [Finset.sum_eq_single ⟨i.val, hi⟩, hei, hz i (Or.inl hi), Pi.single_eq_same, one_mul, zero_mul,
      add_zero]
    · intro c _ hc
      rw [Pi.single_eq_of_ne, zero_mul]
      intro h
      apply hc
      have h' := congrArg Fin.val h
      have hv : (eI k r c).val = c.val := rfl
      exact Fin.ext (by rw [← hv, ← h'])
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have hsum : ∑ c : Fin r, (Pi.single (eI k r c) (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) i * (a *ᵥ fvec k r z b) (eI k r c) = 0 := by
      apply Finset.sum_eq_zero
      intro c _
      rw [Pi.single_eq_of_ne, zero_mul]
      intro h
      have h' := congrArg Fin.val h
      have hv : (eI k r c).val = c.val := rfl
      have hc := c.isLt
      omega
    rw [hsum, zero_add]
    by_cases hb : Fin.last r = b
    · subst hb
      rw [if_pos rfl, mul_one, hF2]
      have hterm : ∀ j, a i j * z j = if j = i then z i else 0 := by
        intro j
        by_cases hjW : r ≤ j.val ∧ j.val ≤ r + k
        · rw [ha.2.2 i j hjW.1 hjW.2 (by omega)]
          by_cases hij : i = j
          · subst hij
            simp
          · rw [if_neg hij, if_neg (Ne.symm hij), zero_mul]
        · rw [hz j (by omega), mul_zero]
          split_ifs with hij
          · subst hij
            exact (hz _ (by omega)).symm
          · rfl
      simp [Matrix.mulVec, dotProduct, hterm]
    · rw [if_neg hb, mul_zero]
      have hbr : b.val < r := by
        have := b.isLt
        have : b.val ≠ r := fun h => hb (Fin.ext h.symm)
        omega
      have hfb : fvec k r z b = bvec (eI k r ⟨b.val, hbr⟩) := by
        unfold fvec
        rw [dif_pos hbr]
      rw [hfb]
      unfold bvec
      have hcol : (a *ᵥ Pi.single (eI k r ⟨b.val, hbr⟩) (1 : ℂ)) i = a i (eI k r ⟨b.val, hbr⟩) := by
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [hcol, ha.2.1 ⟨b.val, hbr⟩ i (by show b.val ≤ i.val; omega), if_neg]
      intro h
      have h' := congrArg Fin.val h
      have hv : (eI k r ⟨b.val, hbr⟩).val = b.val := rfl
      omega

theorem flag_rel {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z')
    {g a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r))
    (ha : a ∈ RStab k r g) :
    (flagMat k r z a)ᴴ * Zhat k r z z' g * flagMat k r z' (g⁻¹ * a * g) = Zhat k r z z' g := by
  have hx : g⁻¹ * a * g ∈ Nset k r := ha.2
  have ha1 : a ∈ Nset k r := ha.1
  have hU : aᴴ * Hpk k r * a = Hpk k r := ha1.1
  have h1 := mul_Fm hz ha1
  have h2 := mul_Fm hz' hx
  have hgg : g * g⁻¹ = 1 := uh_mul_inv hg
  rw [zhat_eq]
  calc (flagMat k r z a)ᴴ * ((Fm k r z)ᴴ * (Hpk k r * g) * Fm k r z') * flagMat k r z' (g⁻¹ * a * g)
      = (Fm k r z * flagMat k r z a)ᴴ * (Hpk k r * g) *
          (Fm k r z' * flagMat k r z' (g⁻¹ * a * g)) := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = (a * Fm k r z)ᴴ * (Hpk k r * g) * (g⁻¹ * a * g * Fm k r z') := by rw [← h1, ← h2]
    _ = (Fm k r z)ᴴ * (aᴴ * Hpk k r * (g * g⁻¹) * a) * g * Fm k r z' := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = (Fm k r z)ᴴ * (Hpk k r * g) * Fm k r z' := by
        rw [hgg, Matrix.mul_one, hU]
        simp only [Matrix.mul_assoc]

end PI.AmpRootCommon
