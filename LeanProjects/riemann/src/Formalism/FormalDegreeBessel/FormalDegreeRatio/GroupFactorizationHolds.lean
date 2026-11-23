import Mathlib
import Formalism.FormalDegreeBessel.StatementG

open Matrix

noncomputable section

namespace Formalism.QuantumDeterminants

theorem sum_fin_castLE {m l : ℕ} (h : l ≤ m) (f : Fin m → ℂ)
    (hf : ∀ j : Fin m, l ≤ j.val → f j = 0) :
    ∑ j, f j = ∑ j : Fin l, f (Fin.castLE h j) := by
  rw [show (∑ j : Fin l, f (Fin.castLE h j)) = ∑ j ∈ Finset.univ.map (Fin.castLEEmb h), f j from
    (Finset.sum_map Finset.univ (Fin.castLEEmb h) f).symm]
  refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => hf j ?_).symm
  by_contra hlt
  push_neg at hlt
  exact hj (Finset.mem_map.mpr ⟨⟨j.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)

theorem minor_eq_of_mul {m : ℕ} (L U X Y : Matrix (Fin m) (Fin m) ℂ)
    (hL0 : ∀ i j : Fin m, i < j → L i j = 0) (hL1 : ∀ i, L i i = 1)
    (hU0 : ∀ i j : Fin m, j < i → U i j = 0) (hU1 : ∀ i, U i i = 1)
    (h : L * X = Y * U) (l : ℕ) (hl : l ≤ m) :
    (X.submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      (Y.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  have hord : ∀ i j : Fin l, i < j → Fin.castLE hl i < Fin.castLE hl j := fun i j h =>
    Fin.lt_def.2 (by simpa using Fin.lt_def.1 h)
  have h1 : (L * X).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      L.submatrix (Fin.castLE hl) (Fin.castLE hl) * X.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
    ext i j
    simp only [submatrix_apply, mul_apply]
    rw [sum_fin_castLE hl (fun q => L (Fin.castLE hl i) q * X q (Fin.castLE hl j)) (fun q hq => by
      rw [hL0 _ _ (Fin.lt_def.2 (by simp; omega)), zero_mul])]
  have h2 : (Y * U).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      Y.submatrix (Fin.castLE hl) (Fin.castLE hl) * U.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
    ext i j
    simp only [submatrix_apply, mul_apply]
    rw [sum_fin_castLE hl (fun q => Y (Fin.castLE hl i) q * U q (Fin.castLE hl j)) (fun q hq => by
      rw [hU0 _ _ (Fin.lt_def.2 (by simp; omega)), mul_zero])]
  have hdL : (L.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
    rw [Matrix.det_of_lowerTriangular (L.submatrix (Fin.castLE hl) (Fin.castLE hl)) (fun i j hij => hL0 _ _ (hord _ _ (OrderDual.toDual_lt_toDual.mp hij)))]
    simp [hL1]
  have hdU : (U.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
    rw [Matrix.det_of_upperTriangular (M := U.submatrix (Fin.castLE hl) (Fin.castLE hl)) (fun i j hij => hU0 _ _ (hord _ _ hij))]
    simp [hU1]
  have h3 := congrArg Matrix.det
    (show (L * X).submatrix (Fin.castLE hl) (Fin.castLE hl) = (Y * U).submatrix (Fin.castLE hl) (Fin.castLE hl)
      by rw [h])
  rw [h1, h2, Matrix.det_mul, Matrix.det_mul, hdL, hdU, one_mul, mul_one] at h3
  exact h3

def Fm (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) ℂ :=
  Matrix.of fun i a => fvec k r z a i

theorem Zhat_eq (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Zhat k r z z' g = (Fm k r z)ᴴ * Hpk k r * g * Fm k r z' := by
  simp only [Matrix.mul_assoc]
  ext a b
  rfl

theorem Sset_UH {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
    {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hs : s ∈ Sset k r z) :
    sᴴ * Hpk k r * s = Hpk k r := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  have h1 : hᴴ * Hpk k r * h = Hpk k r := hh.1
  have h2 : mᴴ * Hpk k r * m = Hpk k r := hm.1
  rw [conjTranspose_mul]
  calc mᴴ * hᴴ * Hpk k r * (h * m) = mᴴ * (hᴴ * Hpk k r * h) * m := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [h1, h2]

theorem UW_F {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z) :
    h * Fm k r z = Fm k r z := by
  ext i a
  change (h *ᵥ fvec k r z a) i = fvec k r z a i
  unfold fvec
  split_ifs with ha
  · rw [(hh.2.1 ⟨a.val, ha⟩).1]
  · rw [hh.2.2]

theorem mF_col {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ)
    (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i : Fin (2 * r + k + 1))
    (a : Fin (r + 1)) (hA : a.val < r) :
    (m * Fm k r z) i a = m i (eI k r ⟨a.val, hA⟩) := by
  change (m *ᵥ fvec k r z a) i = _
  simp [fvec, hA, bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

def Uof (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  fun c a => if hc : c.val < r then (m * Fm k r z) (eI k r ⟨c.val, hc⟩) a else if c = a then 1 else 0

theorem fvec_apply_lt {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    (c : Fin (r + 1)) (i : Fin (2 * r + k + 1)) (hi : i.val < r) :
    fvec k r z c i = if c.val = i.val then 1 else 0 := by
  unfold fvec
  split_ifs with hc h1 h1
  · simp [bvec, eI, Pi.single_apply, Fin.ext_iff, h1]
  · simp [bvec, eI, Pi.single_apply, Fin.ext_iff] <;> omega
  · omega
  · exact hz i (Or.inl hi)

theorem fvec_apply_ge {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ)
    (c : Fin (r + 1)) (i : Fin (2 * r + k + 1)) (hi : r ≤ i.val) :
    fvec k r z c i = if c.val = r then z i else 0 := by
  unfold fvec
  split_ifs with hc h1 h1
  · omega
  · simp [bvec, eI, Pi.single_apply, Fin.ext_iff] <;> omega
  · rfl
  · have := c.isLt
    omega

theorem N_F {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hm : m ∈ Nset k r) :
    m * Fm k r z = Fm k r z * Uof k r z m := by
  have hm2 := hm.2.1
  have hm3 := hm.2.2
  ext i a
  conv_rhs => rw [Matrix.mul_apply]
  by_cases hi : i.val < r
  · have hF : ∀ c, Fm k r z i c = if c = ⟨i.val, by omega⟩ then 1 else 0 := fun c => by
      change fvec k r z c i = _
      rw [fvec_apply_lt z hz c i hi]
      simp [Fin.ext_iff]
    simp only [hF, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    simp [Uof, hi, eI]
  · have hF : ∀ c, Fm k r z i c = if c = Fin.last r then z i else 0 := fun c => by
      change fvec k r z c i = _
      rw [fvec_apply_ge z c i (by omega)]
      simp [Fin.ext_iff]
    simp only [hF, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    have hU : Uof k r z m (Fin.last r) a = if Fin.last r = a then 1 else 0 := by simp [Uof]
    rw [hU]
    by_cases ha : a.val < r
    · rw [mF_col z m i a ha, hm2 ⟨a.val, ha⟩ i (by show a.val ≤ i.val; omega)]
      have h1 : i ≠ eI k r ⟨a.val, ha⟩ := by
        intro h
        have := congrArg Fin.val h
        change i.val = a.val at this
        omega
      have h2 : Fin.last r ≠ a := by
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      simp [h1, h2]
    · have ha' : a = Fin.last r := Fin.ext (by have := a.isLt; simp; omega)
      subst ha'
      simp only [if_true, mul_one]
      change (m *ᵥ fvec k r z (Fin.last r)) i = z i
      have hf : fvec k r z (Fin.last r) = z := by simp [fvec]
      rw [hf]
      have hterm : ∀ j, m i j * z j = if i = j then z j else 0 := by
        intro j
        by_cases hj : j.val < r ∨ r + k < j.val
        · rw [hz j hj]
          simp
        · push_neg at hj
          rw [hm3 i j hj.1 hj.2 (by omega)]
          split_ifs <;> simp
      simp only [Matrix.mulVec, dotProduct, hterm, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem Uof_lower_zero {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
    {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hm : m ∈ Nset k r)
    (c a : Fin (r + 1)) (hac : a < c) : Uof k r z m c a = 0 := by
  have hm2 := hm.2.1
  have hac' : a.val < c.val := hac
  by_cases hc : c.val < r
  · simp only [Uof, hc, dif_pos]
    rw [mF_col z m _ a (by omega), hm2 ⟨a.val, by omega⟩ _ (by show a.val ≤ c.val; omega)]
    rw [if_neg]
    intro h
    have := congrArg Fin.val h
    change c.val = a.val at this
    omega
  · have hne : c ≠ a := fun h => by rw [h] at hac'; omega
    simp [Uof, hc, hne]

theorem Uof_diag {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
    {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hm : m ∈ Nset k r)
    (c : Fin (r + 1)) : Uof k r z m c c = 1 := by
  have hm2 := hm.2.1
  by_cases hc : c.val < r
  · simp only [Uof, hc, dif_pos]
    rw [mF_col z m _ c hc, hm2 ⟨c.val, hc⟩ _ (le_refl _), if_pos rfl]
  · simp [Uof, hc]

theorem S_F {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hs : s ∈ Sset k r z) :
    ∃ U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, (∀ c a, a < c → U c a = 0) ∧ (∀ c, U c c = 1) ∧
      s * Fm k r z = Fm k r z * U := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  refine ⟨Uof k r z m, fun c a hac => Uof_lower_zero hm c a hac, fun c => Uof_diag hm c, ?_⟩
  rw [Matrix.mul_assoc, N_F hz hm, ← Matrix.mul_assoc, UW_F hh]

theorem diagonal_inverse_holds : DInv := by
  intro k r z z' hz hz' s hs s' hs' g l
  obtain ⟨U, hU0, hU1, hsF⟩ := S_F hz hs
  obtain ⟨U', hU0', hU1', hsF'⟩ := S_F hz' hs'
  have hH : sᴴ * Hpk k r * s = Hpk k r := Sset_UH hs
  have hFs : (Fm k r z)ᴴ * sᴴ = Uᴴ * (Fm k r z)ᴴ := by
    rw [← conjTranspose_mul, hsF, conjTranspose_mul]
  have hL0 : ∀ i j : Fin (r + 1), i < j → Uᴴ i j = 0 := fun i j hij => by
    simp [conjTranspose_apply, hU0 j i hij]
  have hL1 : ∀ i, Uᴴ i i = 1 := fun i => by simp [conjTranspose_apply, hU1 i]
  have hmul : Uᴴ * Zhat k r z z' (s * g * s') = Zhat k r z z' g * U' := by
    rw [Zhat_eq, Zhat_eq]
    calc Uᴴ * ((Fm k r z)ᴴ * Hpk k r * (s * g * s') * Fm k r z')
        = (Uᴴ * (Fm k r z)ᴴ) * Hpk k r * (s * g * s') * Fm k r z' := by
          simp only [Matrix.mul_assoc]
      _ = (Fm k r z)ᴴ * (sᴴ * Hpk k r * s) * g * (s' * Fm k r z') := by
          rw [← hFs]
          simp only [Matrix.mul_assoc]
      _ = (Fm k r z)ᴴ * Hpk k r * g * Fm k r z' * U' := by
          rw [hH, hsF']
          simp only [Matrix.mul_assoc]
  exact minor_eq_of_mul Uᴴ U' _ _ hL0 hL1 hU0' hU1' hmul l.val _

theorem group_inverse_holds : GInv := by
  intro k r z z' hz hz' s hs s' hs' g
  simp only [Gf, diagonal_inverse_holds k r z z' hz hz' s hs s' hs' g]

theorem group_factorization_holds : GFactor := by
  intro k r z z' g h
  have hne : Complex.normSq (Dmin k r z z' g ⟨r, by omega⟩) ≠ 0 :=
    (Complex.normSq_pos.mpr h).ne'
  simp only [Gf, GGf, zeta, Complex.normSq_div]
  field_simp

end Formalism.QuantumDeterminants
