import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.LowestKTypeMultiplicity
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

open Matrix

noncomputable section

namespace Formalism.MainNotions.S.Pv.Mom

open Formalism.QuantumDeterminants

variable {k r : ℕ}

def twD (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r then (-Complex.I) ^ (r - i.val)
  else if r + k < i.val then (-Complex.I) ^ (r - (2 * r + k - i.val))
  else 1

def twT (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := Matrix.diagonal (twD k r)

def twTi (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  Matrix.diagonal (fun i => star (twD k r i))

theorem negI_pow_mul_star (n : ℕ) : (-Complex.I) ^ n * star ((-Complex.I) ^ n) = 1 := by
  rw [star_pow, ← mul_pow]
  have : (-Complex.I) * star (-Complex.I) = 1 := by
    simp
  rw [this, one_pow]

theorem twD_mul_star (i : Fin (2 * r + k + 1)) : twD k r i * star (twD k r i) = 1 := by
  unfold twD
  split_ifs
  · exact negI_pow_mul_star _
  · exact negI_pow_mul_star _
  · simp

theorem star_twD_mul (i : Fin (2 * r + k + 1)) : star (twD k r i) * twD k r i = 1 := by
  rw [mul_comm]; exact twD_mul_star i

theorem twT_mul_twTi : twT k r * twTi k r = 1 := by
  unfold twT twTi
  rw [Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  exact twD_mul_star i

theorem twTi_mul_twT : twTi k r * twT k r = 1 := by
  unfold twT twTi
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact star_twD_mul i

theorem twT_inv : (twT k r)⁻¹ = twTi k r := Matrix.inv_eq_right_inv twT_mul_twTi

theorem twTi_inv : (twTi k r)⁻¹ = twT k r := Matrix.inv_eq_right_inv twTi_mul_twT

theorem twT_conjTranspose : (twT k r)ᴴ = twTi k r := by
  unfold twT twTi
  rw [Matrix.diagonal_conjTranspose]
  rfl

theorem twD_pair (i j : Fin (2 * r + k + 1)) (h : i.val + j.val = 2 * r + k) (hi : i.val < r ∨ j.val < r) :
    twD k r i = twD k r j := by
  unfold twD
  rcases hi with hi | hj
  · have hj1 : ¬ j.val < r := by omega
    have hj2 : r + k < j.val := by omega
    rw [if_pos hi, if_neg hj1, if_pos hj2]
    congr 1
    omega
  · have hi1 : ¬ i.val < r := by omega
    have hi2 : r + k < i.val := by omega
    rw [if_neg hi1, if_pos hi2, if_pos hj]
    congr 1
    omega

theorem twD_Wb (i : Fin (2 * r + k + 1)) (h1 : r ≤ i.val) (h2 : i.val ≤ r + k) : twD k r i = 1 := by
  unfold twD
  rw [if_neg (by omega), if_neg (by omega)]

theorem twT_mem_UH : twT k r ∈ UH (Hpk k r) := by
  show (twT k r)ᴴ * Hpk k r * twT k r = Hpk k r
  rw [twT_conjTranspose]
  unfold twTi twT
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  unfold Hpk
  split_ifs with h1 h2 h3 h4
  · rw [mul_one, twD_pair i j h1.2 (Or.inl h1.1), star_twD_mul]
  · rw [mul_one, twD_pair i j h2.2 (Or.inr h2.1), star_twD_mul]
  · obtain ⟨ha, hb, rfl⟩ := h3
    rw [twD_Wb i ha hb]; simp
  · obtain ⟨ha, hb, rfl⟩ := h3
    rw [twD_Wb i ha hb]; simp
  · simp

theorem twTi_mem_UH : twTi k r ∈ UH (Hpk k r) := by
  have h := WeylGroupFacts.uh_inv (k := k) (r := r) twT_mem_UH
  rwa [twT_inv] at h

theorem twT_comm_block {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : WeylGroupFacts.block k r h) :
    twT k r * h = h * twT k r := by
  unfold twT
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hj : j.val < r ∨ r + k < j.val
  · rw [hh.1 i j hj]
    split_ifs with e
    · subst e; ring
    · simp
  · by_cases hi : i.val < r ∨ r + k < i.val
    · rw [hh.2 i j hi]
      split_ifs with e
      · subst e; ring
      · simp
    · rw [twD_Wb i (by omega) (by omega), twD_Wb j (by omega) (by omega)]
      ring

theorem twT_conj_apply (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1)) :
    (twT k r * g * twTi k r) i j = twD k r i * g i j * star (twD k r j) := by
  unfold twT twTi
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem twT_conj_N {n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hn : n ∈ Nset k r) :
    twT k r * n * twTi k r ∈ Nset k r := by
  rw [WeylGroupFacts.nset_iff] at hn ⊢
  refine ⟨WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul twT_mem_UH hn.1) twTi_mem_UH, fun i j hj hi => ?_⟩
  rw [twT_conj_apply, hn.2 i j hj hi]
  split_ifs with e
  · subst e; rw [mul_one, twD_mul_star]
  · simp

theorem twTi_mulVec_Wb {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) : twTi k r *ᵥ z = z := by
  unfold twTi
  funext i
  rw [Matrix.mulVec_diagonal]
  by_cases hi : i.val < r ∨ r + k < i.val
  · rw [hz i hi, mul_zero]
  · rw [twD_Wb i (by omega) (by omega)]; simp

theorem twD_eI_succ (a : ℕ) (ha : a + 1 < r) (hi : a < 2 * r + k + 1) (hi' : a + 1 < 2 * r + k + 1) :
    twD k r ⟨a, hi⟩ * star (twD k r ⟨a + 1, hi'⟩) = -Complex.I := by
  unfold twD
  rw [if_pos (show a < r by omega), if_pos (show a + 1 < r by omega)]
  have e : r - a = (r - (a + 1)) + 1 := by omega
  rw [e, pow_succ, mul_comm ((-Complex.I) ^ (r - (a + 1))) (-Complex.I), mul_assoc, negI_pow_mul_star, mul_one]

theorem twD_last (hr : 0 < r) (hi : r - 1 < 2 * r + k + 1) : twD k r ⟨r - 1, hi⟩ = -Complex.I := by
  unfold twD
  rw [if_pos (show r - 1 < r by omega)]
  have e : r - (r - 1) = 1 := by omega
  rw [e, pow_one]

theorem twT_ell {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ell k r z (twT k r * g * twTi k r) = -Complex.I * ell k r z g := by
  unfold ell
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · rw [twT_conj_apply]
    have := twD_eI_succ (k := k) (r := r) a.val h (eI k r a).isLt (eI k r ⟨a.val + 1, h⟩).isLt
    simp only [eI] at this ⊢
    rw [mul_comm (twD k r _) (g _ _), mul_assoc, this]; ring
  · rw [← Matrix.mulVec_mulVec, twTi_mulVec_Wb hz, ← Matrix.mulVec_mulVec]
    unfold twT
    rw [Matrix.mulVec_diagonal]
    have hr : a.val = r - 1 := by omega
    have : eI k r a = ⟨r - 1, by omega⟩ := Fin.ext (by simp [eI, hr])
    rw [this, twD_last (by omega)]

theorem twT_psi {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    psi k r z c (twT k r * g * twTi k r) = psi k r z (c * -Complex.I) g := by
  unfold psi
  rw [twT_ell hz, mul_assoc]

theorem twTi_mulVec_bvec (i : Fin (2 * r + k + 1)) : twTi k r *ᵥ bvec i = star (twD k r i) • bvec i := by
  unfold twTi bvec
  funext j
  rw [Matrix.mulVec_diagonal]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

def spanA (k r : ℕ) (a : Fin (r + 1)) : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) :=
  Submodule.span ℂ (Set.range fun b : {b : Fin r // b.val < a.val} => bvec (eI k r b.1))

theorem diag_mulVec_mem_spanA (d : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1)) {y : Fin (2 * r + k + 1) → ℂ}
    (hy : y ∈ spanA k r a) : Matrix.diagonal d *ᵥ y ∈ spanA k r a := by
  unfold spanA at hy ⊢
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    have e : Matrix.diagonal d *ᵥ bvec (eI k r b.1) = d (eI k r b.1) • bvec (eI k r b.1) := by
      unfold bvec
      funext j
      rw [Matrix.mulVec_diagonal]
      by_cases h : j = eI k r b.1
      · subst h; simp
      · simp [h]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ hx

def sA (k r : ℕ) (a : Fin (r + 1)) : ℂ := if h : a.val < r then star (twD k r (eI k r ⟨a.val, h⟩)) else 1

def tA (k r : ℕ) (a : Fin (r + 1)) : ℂ := if h : a.val < r then twD k r (eI k r ⟨a.val, h⟩) else 1

theorem sA_mul_tA (a : Fin (r + 1)) : sA k r a * tA k r a = 1 := by
  unfold sA tA; split_ifs
  · exact star_twD_mul _
  · simp

theorem norm_twD (i : Fin (2 * r + k + 1)) : ‖twD k r i‖ = 1 := by
  unfold twD; split_ifs <;> simp [norm_pow]

theorem norm_sA (a : Fin (r + 1)) : ‖sA k r a‖ = 1 := by
  unfold sA; split_ifs
  · rw [norm_star, norm_twD]
  · simp

theorem twTi_mulVec_fvec {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (a : Fin (r + 1)) :
    twTi k r *ᵥ fvec k r z a = sA k r a • fvec k r z a := by
  unfold fvec sA
  split_ifs
  · exact twTi_mulVec_bvec _
  · rw [twTi_mulVec_Wb hz, one_smul]

theorem eucl_smul (s : ℂ) (v : Fin (2 * r + k + 1) → ℂ) : Formalism.MainNotions.S.eucl (s • v) = ‖s‖ * Formalism.MainNotions.S.eucl v := by
  unfold Formalism.MainNotions.S.eucl
  simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul]
  rw [← Finset.mul_sum, Real.sqrt_mul (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq,
    Real.sqrt_sq (norm_nonneg _)]

theorem lA_twT {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a : Fin (r + 1)) :
    Formalism.MainNotions.S.lA k r z (twT k r * g) a = Formalism.MainNotions.S.lA k r z g a := by
  unfold Formalism.MainNotions.S.lA
  congr 1
  have hinv : (twT k r * g)⁻¹ = g⁻¹ * twTi k r := by rw [Matrix.mul_inv_rev, twT_inv]
  ext t
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨tA k r a • (twTi k r *ᵥ y), Submodule.smul_mem _ _ (diag_mulVec_mem_spanA _ a hy), ?_⟩
    rw [hinv, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub, twTi_mulVec_fvec hz]
    have e : sA k r a • fvec k r z a - twTi k r *ᵥ y =
        sA k r a • (fvec k r z a - tA k r a • (twTi k r *ᵥ y)) := by
      rw [smul_sub, smul_smul, sA_mul_tA, one_smul]
    rw [e, Matrix.mulVec_smul, eucl_smul, norm_sA, one_mul]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨sA k r a • (twT k r *ᵥ y), Submodule.smul_mem _ _ (diag_mulVec_mem_spanA _ a hy), ?_⟩
    rw [hinv, ← Matrix.mulVec_mulVec]
    have e : twTi k r *ᵥ (fvec k r z a - sA k r a • (twT k r *ᵥ y)) = sA k r a • (fvec k r z a - y) := by
      rw [Matrix.mulVec_sub, twTi_mulVec_fvec hz, Matrix.mulVec_smul, Matrix.mulVec_mulVec, twTi_mul_twT,
        Matrix.one_mulVec, smul_sub]
    rw [e, Matrix.mulVec_smul, eucl_smul, norm_sA, one_mul]

end Formalism.MainNotions.S.Pv.Mom
