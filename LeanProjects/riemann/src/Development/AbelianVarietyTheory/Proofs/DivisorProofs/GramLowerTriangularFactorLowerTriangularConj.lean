import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

variable {s : ℕ}

def ldTop (j : Fin s) : {a : Fin s // (a : ℕ) < j + 1} := ⟨j, Nat.lt_succ_self _⟩

@[simp] theorem ldTop_val (j : Fin s) : (ldTop j).1 = j := rfl

theorem eq_ldTop_iff {j : Fin s} (a : {a : Fin s // (a : ℕ) < j + 1}) : a = ldTop j ↔ a.1 = j :=
  ⟨fun h => h ▸ rfl, fun h => Subtype.ext h⟩

theorem sum_eq_sum_lt_of_zero (m : ℕ) (f : Fin s → ℂ) (hf : ∀ l : Fin s, ¬ (l : ℕ) < m → f l = 0) :
    ∑ l, f l = ∑ b : {a : Fin s // (a : ℕ) < m}, f b := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun a : Fin s => (a : ℕ) < m) f]
  have : ∑ b : {a : Fin s // ¬ (a : ℕ) < m}, f b = 0 := Finset.sum_eq_zero (fun b _ => hf b b.2)
  rw [this, add_zero]

theorem prod_lt_eq (m : ℕ) (f : Fin s → ℂ) :
    ∏ a : {a : Fin s // (a : ℕ) < m}, f a = ∏ a : Fin s, if (a : ℕ) < m then f a else 1 := by
  rw [← Finset.prod_filter]
  exact (Finset.prod_subtype _ (by simp) f).symm

theorem prod_lt_succ (j : Fin s) (f : Fin s → ℂ) :
    ∏ a : {a : Fin s // (a : ℕ) < j + 1}, f a = (∏ a : {a : Fin s // (a : ℕ) < j}, f a) * f j := by
  have hj : f j = ∏ a : Fin s, if a = j then f a else 1 := by simp
  rw [prod_lt_eq, prod_lt_eq, hj, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  by_cases h1 : (a : ℕ) < j
  · have h2 : a ≠ j := fun h => by subst h; omega
    simp [h1, h2, show (a : ℕ) < j + 1 by omega]
  · by_cases h3 : a = j
    · subst h3; simp
    · have : ¬ (a : ℕ) < j + 1 := fun h => h3 (Fin.ext (by omega))
      simp [h1, h3, this]

theorem submatrix_mul_conjTranspose_lt (g M : Matrix (Fin s) (Fin s) ℂ) (hg : ∀ i j, i < j → g i j = 0)
    {κ : Type} (ρ : κ → Fin s) (m : ℕ) :
    (M * gᴴ).submatrix ρ (Subtype.val : {a : Fin s // (a : ℕ) < m} → Fin s) =
      M.submatrix ρ (Subtype.val : {a : Fin s // (a : ℕ) < m} → Fin s) *
        gᴴ.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < m} → Fin s) Subtype.val := by
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  refine sum_eq_sum_lt_of_zero m _ fun l hl => ?_
  rw [Matrix.conjTranspose_apply, hg c.1 l (by have := c.2; rw [Fin.lt_iff_val_lt_val]; omega), star_zero, mul_zero]

theorem submatrix_mul_lt (g M : Matrix (Fin s) (Fin s) ℂ) (hg : ∀ i j, i < j → g i j = 0)
    {κ : Type} (ν : κ → Fin s) (m : ℕ) :
    (g * M).submatrix (Subtype.val : {a : Fin s // (a : ℕ) < m} → Fin s) ν =
      g.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < m} → Fin s) Subtype.val *
        M.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < m} → Fin s) ν := by
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  refine sum_eq_sum_lt_of_zero m _ fun l hl => ?_
  rw [hg a.1 l (by have := a.2; rw [Fin.lt_iff_val_lt_val]; omega), zero_mul]

theorem det_submatrix_lt (g : Matrix (Fin s) (Fin s) ℂ) (hg : ∀ i j, i < j → g i j = 0) (m : ℕ) :
    (g.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < m} → Fin s) Subtype.val).det =
      ∏ a : {a : Fin s // (a : ℕ) < m}, g a a := by
  rw [Matrix.det_of_lowerTriangular]
  · rfl
  · intro a b h
    exact hg a.1 b.1 h

theorem leadMinor_conj_lower (g G : Matrix (Fin s) (Fin s) ℂ) (hg : ∀ i j, i < j → g i j = 0) (m : ℕ) :
    leadMinor (g * G * gᴴ) m =
      (∏ a : {a : Fin s // (a : ℕ) < m}, g a a) * leadMinor G m * star (∏ a : {a : Fin s // (a : ℕ) < m}, g a a) := by
  unfold leadMinor
  rw [submatrix_mul_conjTranspose_lt g _ hg, Matrix.det_mul, submatrix_mul_lt g G hg]
  erw [Matrix.det_mul]
  rw [← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose, det_submatrix_lt g hg]

theorem det_updateRow_finset_sum {ι κ : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (r : ι)
    (t : Finset κ) (c : κ → ℂ) (v : κ → ι → ℂ) :
    (A.updateRow r (∑ l ∈ t, c l • v l)).det = ∑ l ∈ t, c l * (A.updateRow r (v l)).det := by
  classical
  refine Finset.induction_on t ?_ ?_
  · simp only [Finset.sum_empty]
    exact Matrix.det_eq_zero_of_row_eq_zero r (fun c => by simp)
  · intro a t ha ih
    rw [Finset.sum_insert ha, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, ih, Finset.sum_insert ha]

theorem submatrix_ld_eq_updateRow (X : Matrix (Fin s) (Fin s) ℂ) (i j : Fin s) :
    X.submatrix (fun a : {a : Fin s // (a : ℕ) < j + 1} => if a.1 = j then i else a.1) Subtype.val =
      (X.submatrix Subtype.val Subtype.val).updateRow (ldTop j)
        (fun c : {a : Fin s // (a : ℕ) < j + 1} => X i c) := by
  ext a c
  rw [Matrix.updateRow_apply]
  by_cases h : a.1 = j
  · simp [h, (eq_ldTop_iff a).2 h]
  · have : a ≠ ldTop j := fun e => h ((eq_ldTop_iff a).1 e)
    simp [h, this]

theorem updateRow_mul_lower (g X : Matrix (Fin s) (Fin s) ℂ) (hg : ∀ i j, i < j → g i j = 0) (j : Fin s)
    (v : {a : Fin s // (a : ℕ) < j + 1} → ℂ) :
    ((g * X).submatrix Subtype.val Subtype.val).updateRow (ldTop j) v =
      (g.submatrix Subtype.val Subtype.val).updateRow (ldTop j) (Pi.single (ldTop j) 1) *
        (X.submatrix Subtype.val Subtype.val).updateRow (ldTop j) v := by
  ext a c
  by_cases h : a = ldTop j
  · subst h
    simp [Matrix.mul_apply, Pi.single_apply]
  · have ha : (a.1 : ℕ) < j := by
      have := a.2
      have : (a.1 : ℕ) ≠ j := fun e => h ((eq_ldTop_iff a).2 (Fin.ext e))
      omega
    rw [Matrix.updateRow_ne h, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.mul_apply]
    rw [sum_eq_sum_lt_of_zero ((j : ℕ) + 1) _ fun l hl => by
      rw [hg a.1 l (by rw [Fin.lt_iff_val_lt_val]; omega), zero_mul]]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.updateRow_ne h, Matrix.submatrix_apply, Matrix.updateRow_apply]
    by_cases hb : b = ldTop j
    · subst hb
      rw [ldTop_val, hg a.1 j (by rw [Fin.lt_iff_val_lt_val]; exact ha)]
      simp
    · simp [hb]

theorem det_frameRow (g : Matrix (Fin s) (Fin s) ℂ) (hg : ∀ i j, i < j → g i j = 0) (j : Fin s) :
    ((g.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < j + 1} → Fin s) Subtype.val).updateRow
      (ldTop j) (Pi.single (ldTop j) 1)).det =
      ∏ a : {a : Fin s // (a : ℕ) < j}, g a a := by
  rw [Matrix.det_of_lowerTriangular]
  · have e : ∀ a : {a : Fin s // (a : ℕ) < j + 1},
        ((g.submatrix Subtype.val Subtype.val).updateRow (ldTop j) (Pi.single (ldTop j) 1)) a a =
          (fun b : Fin s => if b = j then 1 else g b b) a := by
      intro a
      by_cases h : a = ldTop j
      · subst h; simp
      · have : a.1 ≠ j := fun e => h ((eq_ldTop_iff a).2 e)
        simp [Matrix.updateRow_ne h, this]
    rw [Fintype.prod_congr _ _ e, prod_lt_succ j (fun b : Fin s => if b = j then 1 else g b b)]
    simp only [if_true, mul_one]
    refine Fintype.prod_congr (fun a : {a : Fin s // (a : ℕ) < j} => if (a : Fin s) = j then (1 : ℂ) else g a a)
      (fun a => g a a) fun a => ?_
    have : a.1 ≠ j := fun e => by have := a.2; rw [e] at this; omega
    simp [this]
  · intro a b hab
    have hab' : (a.1 : ℕ) < b.1 := hab
    by_cases h : a = ldTop j
    · subst h
      have := b.2
      simp at hab'
      omega
    · rw [Matrix.updateRow_ne h, Matrix.submatrix_apply]
      exact hg a.1 b.1 (Fin.lt_iff_val_lt_val.mpr hab')

end GlobalTheory.ChernCalc

namespace GlobalTheory.ChernCalc

theorem ldNum_conj_lower {s : ℕ} (g G : Matrix (Fin s) (Fin s) ℂ) (hg : ∀ i j, i < j → g i j = 0) (i j : Fin s) :
    ((g * G * gᴴ).submatrix (fun a : {a : Fin s // (a : ℕ) < j + 1} => if a.1 = j then i else a.1) Subtype.val).det =
      (∏ a : {a : Fin s // (a : ℕ) < j}, g a a) *
        (∑ l, g i l * (G.submatrix (fun a : {a : Fin s // (a : ℕ) < j + 1} => if a.1 = j then l else a.1)
          Subtype.val).det) * star (∏ a : {a : Fin s // (a : ℕ) < j + 1}, g a a) := by
  rw [submatrix_mul_conjTranspose_lt g _ hg, Matrix.det_mul, ← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose,
    det_submatrix_lt g hg, submatrix_ld_eq_updateRow, updateRow_mul_lower g G hg]
  erw [Matrix.det_mul]
  rw [det_frameRow g hg]
  have hrow : (fun c : {a : Fin s // (a : ℕ) < j + 1} => (g * G) i c) =
      ∑ l, g i l • (fun c : {a : Fin s // (a : ℕ) < j + 1} => G l c) := by
    funext c; simp [Matrix.mul_apply, Finset.sum_apply]
  rw [hrow, det_updateRow_finset_sum]
  simp only [submatrix_ld_eq_updateRow]

theorem ldPart_conj_lower : ∀ (s : ℕ) (G g : Matrix (Fin s) (Fin s) ℂ), G.PosDef → (∀ i j, i < j → g i j = 0) →
    IsUnit g.det → ldPart (g * G * gᴴ) = g * ldPart G * (Matrix.diagonal fun i => g i i)ᴴ ∧
      ∀ i, grD (g * G * gᴴ) i = ‖g i i‖ ^ 2 * grD G i := by
  intro s G g hG hg hdet
  have hgd : g.det = ∏ a, g a a := Matrix.det_of_lowerTriangular g (fun a b h => hg a b h)
  have hdiag : ∀ a, g a a ≠ 0 := by
    intro a
    have h := hdet.ne_zero
    rw [hgd] at h
    exact (Finset.prod_ne_zero_iff.mp h) a (Finset.mem_univ _)
  have hP : ∀ m : ℕ, (∏ a : {a : Fin s // (a : ℕ) < m}, g a a) ≠ 0 :=
    fun m => Finset.prod_ne_zero_iff.mpr fun a _ => hdiag a
  have hlm : ∀ m : ℕ, leadMinor G m ≠ 0 := fun m => by
    unfold leadMinor
    exact ((hG.submatrix Subtype.val_injective).det_pos).ne'
  have hsq : ∀ z w : ℂ, (z * w * star z).re = ‖z‖ ^ 2 * w.re := by
    intro z w
    rw [mul_comm z w, mul_assoc, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [Complex.re_mul_ofReal]
    ring
  refine ⟨?_, fun i => ?_⟩
  · ext i j
    simp only [ldPart, Matrix.of_apply]
    rw [ldNum_conj_lower g G hg, leadMinor_conj_lower g G hg, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal,
      Matrix.mul_apply, prod_lt_succ j (fun b => g b b)]
    simp only [Matrix.of_apply, ← mul_div_assoc, Pi.star_apply]
    rw [← Finset.sum_div, star_mul]
    have h1 := hP (j : ℕ)
    have h2 := hlm (j : ℕ)
    have h3 : star (∏ a : {a : Fin s // (a : ℕ) < j}, g a a) ≠ 0 := star_ne_zero.mpr h1
    field_simp
  · unfold grD
    rw [leadMinor_conj_lower g G hg, leadMinor_conj_lower g G hg, hsq, hsq, prod_lt_succ i (fun b => g b b),
      norm_mul, mul_pow]
    have hn : ‖∏ a : {a : Fin s // (a : ℕ) < i}, g a a‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr (hP _))
    rw [mul_assoc, mul_div_mul_left _ _ hn, mul_div_assoc]

end GlobalTheory.ChernCalc
