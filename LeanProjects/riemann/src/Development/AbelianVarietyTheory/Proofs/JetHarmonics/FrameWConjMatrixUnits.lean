import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementKT
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CapFrame

open Formalism.QuantumDeterminants

variable {k r : ℕ}

def dualIx (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if i.val < r ∨ r + k < i.val then ⟨2 * r + k - i.val, by omega⟩ else i

def sgnIx (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

lemma dualIx_val (i : Fin (2 * r + k + 1)) :
    (dualIx k r i).val = if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val := by
  unfold dualIx; split_ifs <;> rfl

lemma dualIx_dualIx (i : Fin (2 * r + k + 1)) : dualIx k r (dualIx k r i) = i := by
  have := i.isLt
  apply Fin.ext
  rw [dualIx_val, dualIx_val]
  split_ifs <;> omega

lemma sgnIx_dualIx (i : Fin (2 * r + k + 1)) : sgnIx k r (dualIx k r i) = sgnIx k r i := by
  have := i.isLt
  unfold sgnIx
  rw [dualIx_val]
  split_ifs <;> first | rfl | omega

lemma sgnIx_sq (i : Fin (2 * r + k + 1)) : sgnIx k r i * sgnIx k r i = 1 := by
  unfold sgnIx; split_ifs <;> simp

lemma star_sgnIx (i : Fin (2 * r + k + 1)) : star (sgnIx k r i) = sgnIx k r i := by
  unfold sgnIx; split_ifs <;> simp

lemma Hpk_apply (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = dualIx k r i then sgnIx k r i else 0 := by
  have := i.isLt
  have := j.isLt
  unfold Hpk sgnIx
  simp only [Fin.ext_iff, dualIx_val]
  split_ifs <;> first | rfl | omega

lemma Hpk_apply' (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if i = dualIx k r j then sgnIx k r j else 0 := by
  rw [Hpk_apply]
  by_cases h : j = dualIx k r i
  · subst h; simp [dualIx_dualIx, sgnIx_dualIx]
  · rw [if_neg h, if_neg]
    rintro rfl
    exact h (dualIx_dualIx j).symm

lemma Hpk_mul_apply (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j) :
    (Hpk k r * X) i j = sgnIx k r i * X (dualIx k r i) j := by
  simp [Matrix.mul_apply, Hpk_apply]

lemma mul_Hpk_apply (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j) :
    (X * Hpk k r) i j = X i (dualIx k r j) * sgnIx k r j := by
  simp [Matrix.mul_apply, Hpk_apply']

lemma Hpk_mulVec (v : Fin (2 * r + k + 1) → ℂ) (i) :
    (Hpk k r *ᵥ v) i = sgnIx k r i * v (dualIx k r i) := by
  simp [Matrix.mulVec, dotProduct, Hpk_apply]

lemma Hpk_mul_self : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Hpk_mul_apply, Hpk_apply, dualIx_dualIx, sgnIx_dualIx, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp [sgnIx_sq]
  · simp [h, Ne.symm h]

lemma herm_single (v : Fin (2 * r + k + 1) → ℂ) (j) :
    herm (Hpk k r) v (Pi.single j 1) = sgnIx k r j * v (dualIx k r j) := by
  unfold herm
  rw [← Pi.single_star, star_one, single_one_dotProduct, Hpk_mulVec]

lemma herm_smul_right (v w : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    herm (Hpk k r) v (c • w) = star c * herm (Hpk k r) v w := by
  unfold herm
  rw [star_smul, smul_dotProduct, smul_eq_mul]

section U
variable {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}

lemma left_inv_U (hU : gᴴ * Hpk k r * g = Hpk k r) : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hU, Hpk_mul_self]

lemma inv_eq_U (hU : gᴴ * Hpk k r * g = Hpk k r) : g⁻¹ = Hpk k r * gᴴ * Hpk k r :=
  Matrix.inv_eq_left_inv (left_inv_U hU)

lemma inv_mul_U (hU : gᴴ * Hpk k r * g = Hpk k r) : g⁻¹ * g = 1 := by
  rw [inv_eq_U hU, left_inv_U hU]

lemma mul_inv_U (hU : gᴴ * Hpk k r * g = Hpk k r) : g * g⁻¹ = 1 :=
  mul_eq_one_comm.mp (inv_mul_U hU)

lemma isUnit_U (hU : gᴴ * Hpk k r * g = Hpk k r) : IsUnit g :=
  ⟨⟨g, g⁻¹, mul_inv_U hU, inv_mul_U hU⟩, rfl⟩

lemma adj_mul_H (hU : gᴴ * Hpk k r * g = Hpk k r) : gᴴ * Hpk k r = Hpk k r * g⁻¹ := by
  conv_rhs => rw [← hU]
  rw [Matrix.mul_assoc _ g, mul_inv_U hU, Matrix.mul_one]

lemma H_mul_inv_adj (hU : gᴴ * Hpk k r * g = Hpk k r) : Hpk k r * (g⁻¹)ᴴ = g * Hpk k r := by
  have h1 : (g⁻¹)ᴴ * gᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, mul_inv_U hU, Matrix.conjTranspose_one]
  have h2 : (g⁻¹)ᴴ * Hpk k r = Hpk k r * g := by
    conv_lhs => rw [← hU]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  calc Hpk k r * (g⁻¹)ᴴ = Hpk k r * ((g⁻¹)ᴴ * Hpk k r) * Hpk k r := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Hpk_mul_self, Matrix.mul_one]
    _ = g * Hpk k r := by rw [h2, ← Matrix.mul_assoc, Hpk_mul_self, Matrix.one_mul]

lemma inv_apply_U (hU : gᴴ * Hpk k r * g = Hpk k r) (i j) :
    g⁻¹ i j = sgnIx k r i * star (g (dualIx k r j) (dualIx k r i)) * sgnIx k r j := by
  rw [inv_eq_U hU, mul_Hpk_apply, Hpk_mul_apply, Matrix.conjTranspose_apply]

lemma apply_eq_inv_U (hU : gᴴ * Hpk k r * g = Hpk k r) (i j) :
    g i j = sgnIx k r i * star (g⁻¹ (dualIx k r j) (dualIx k r i)) * sgnIx k r j := by
  have : g = Hpk k r * (g⁻¹)ᴴ * Hpk k r := by
    rw [H_mul_inv_adj hU, Matrix.mul_assoc, Hpk_mul_self, Matrix.mul_one]
  conv_lhs => rw [this]
  rw [mul_Hpk_apply, Hpk_mul_apply, Matrix.conjTranspose_apply]

lemma herm_U (hU : gᴴ * Hpk k r * g = Hpk k r) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (g *ᵥ x) (g *ᵥ y) = herm (Hpk k r) x y := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hU]

lemma herm_U' (hU : gᴴ * Hpk k r * g = Hpk k r) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x (g *ᵥ y) = herm (Hpk k r) (g⁻¹ *ᵥ x) y := by
  rw [← herm_U hU (g⁻¹ *ᵥ x) y, Matrix.mulVec_mulVec, mul_inv_U hU, Matrix.one_mulVec]

lemma herm_U'' (hU : gᴴ * Hpk k r * g = Hpk k r) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (g *ᵥ x) y = herm (Hpk k r) x (g⁻¹ *ᵥ y) := by
  rw [← herm_U hU x (g⁻¹ *ᵥ y), Matrix.mulVec_mulVec, mul_inv_U hU, Matrix.one_mulVec]

lemma conj_single_apply (g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a b i j) :
    (g * Matrix.single a b (1 : ℂ) * h) i j = g i a * h b j := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_mul]

lemma H_single_H (a b : Fin (2 * r + k + 1)) :
    Hpk k r * Matrix.single b a (1 : ℂ) * Hpk k r =
      (sgnIx k r b * sgnIx k r a) • Matrix.single (dualIx k r b) (dualIx k r a) (1 : ℂ) := by
  ext i j
  rw [conj_single_apply, Hpk_apply', Hpk_apply, Matrix.smul_apply, Matrix.single_apply]
  by_cases h1 : i = dualIx k r b <;> by_cases h2 : j = dualIx k r a <;> simp [h1, h2, eq_comm]

lemma theta_conj (hU : gᴴ * Hpk k r * g = Hpk k r) (a b : Fin (2 * r + k + 1)) :
    Hpk k r * (g * Matrix.single a b (1 : ℂ) * g⁻¹)ᴴ * Hpk k r =
      (sgnIx k r b * sgnIx k r a) • (g * Matrix.single (dualIx k r b) (dualIx k r a) (1 : ℂ) * g⁻¹) := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_single, star_one]
  calc Hpk k r * (g⁻¹ᴴ * (Matrix.single b a (1 : ℂ) * gᴴ)) * Hpk k r
      = (Hpk k r * g⁻¹ᴴ) * Matrix.single b a (1 : ℂ) * (gᴴ * Hpk k r) := by
        simp only [Matrix.mul_assoc]
    _ = g * (Hpk k r * Matrix.single b a (1 : ℂ) * Hpk k r) * g⁻¹ := by
        rw [H_mul_inv_adj hU, adj_mul_H hU]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [H_single_H, Matrix.mul_smul, Matrix.smul_mul]

end U

lemma ell_neg_smul (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ell k r z (-(c • X)) = -(c * ell k r z X) := by
  unfold ell
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs
  · simp
  · simp [Matrix.neg_mulVec, Matrix.smul_mulVec]

section Frame
variable {z : Fin (2 * r + k + 1) → ℂ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}

lemma frame_U (hg : PI.UpqRep.IsFrameW k r z g) : gᴴ * Hpk k r * g = Hpk k r := hg.1

lemma frame_fix (hg : PI.UpqRep.IsFrameW k r z g) {j : Fin (2 * r + k + 1)}
    (hj : j.val < r ∨ r + k < j.val) : g *ᵥ Pi.single j 1 = Pi.single j 1 := by
  have := j.isLt
  rcases hj with hj | hj
  · exact (hg.2.1 ⟨j.val, hj⟩).1
  · have e : j = PI.UpqRep.esI k r ⟨2 * r + k - j.val, by omega⟩ :=
      Fin.ext (by simp only [PI.UpqRep.esI]; omega)
    rw [e]
    exact (hg.2.1 _).2

lemma frame_inv_fix (hg : PI.UpqRep.IsFrameW k r z g) {j : Fin (2 * r + k + 1)}
    (hj : j.val < r ∨ r + k < j.val) : g⁻¹ *ᵥ Pi.single j 1 = Pi.single j 1 := by
  conv_lhs => rw [← frame_fix hg hj]
  rw [Matrix.mulVec_mulVec, inv_mul_U (frame_U hg), Matrix.one_mulVec]

lemma frame_z_eq_lin_zu (hg : PI.UpqRep.IsFrameW k r z g) :
    g *ᵥ (((Real.sqrt (Tz k r z) : ℝ) : ℂ) • Pi.single (⟨r + k, by omega⟩ : Fin (2 * r + k + 1)) 1) = z :=
  hg.2.2

lemma frame_inv_mulVec_negativeVector (hg : PI.UpqRep.IsFrameW k r z g) :
    g⁻¹ *ᵥ z = ((Real.sqrt (Tz k r z) : ℝ) : ℂ) • Pi.single (⟨r + k, by omega⟩ : Fin (2 * r + k + 1)) 1 := by
  conv_lhs => rw [← frame_z_eq_lin_zu hg]
  rw [Matrix.mulVec_mulVec, inv_mul_U (frame_U hg), Matrix.one_mulVec]

lemma frame_col (hg : PI.UpqRep.IsFrameW k r z g) (i) {j : Fin (2 * r + k + 1)}
    (hj : j.val < r ∨ r + k < j.val) : g i j = if i = j then 1 else 0 := by
  have := congrFun (frame_fix hg hj) i
  simpa [Pi.single_apply] using this

lemma frame_inv_col (hg : PI.UpqRep.IsFrameW k r z g) (i) {j : Fin (2 * r + k + 1)}
    (hj : j.val < r ∨ r + k < j.val) : g⁻¹ i j = if i = j then 1 else 0 := by
  have := congrFun (frame_inv_fix hg hj) i
  simpa [Pi.single_apply] using this

lemma dualIx_out {i : Fin (2 * r + k + 1)} (hi : i.val < r ∨ r + k < i.val) :
    (dualIx k r i).val < r ∨ r + k < (dualIx k r i).val := by
  have := i.isLt
  rw [dualIx_val, if_pos hi]; omega

lemma dualIx_inj {i j : Fin (2 * r + k + 1)} : dualIx k r i = dualIx k r j ↔ i = j :=
  ⟨fun h => by rw [← dualIx_dualIx i, h, dualIx_dualIx], fun h => by rw [h]⟩

lemma frame_row (hg : PI.UpqRep.IsFrameW k r z g) {i : Fin (2 * r + k + 1)}
    (hi : i.val < r ∨ r + k < i.val) (j) : g i j = if i = j then 1 else 0 := by
  rw [apply_eq_inv_U (frame_U hg), frame_inv_col hg _ (dualIx_out hi)]
  by_cases h : i = j
  · subst h; simp [sgnIx_sq]
  · simp [h, dualIx_inj, Ne.symm h]

lemma frame_inv_row (hg : PI.UpqRep.IsFrameW k r z g) {i : Fin (2 * r + k + 1)}
    (hi : i.val < r ∨ r + k < i.val) (j) : g⁻¹ i j = if i = j then 1 else 0 := by
  rw [inv_apply_U (frame_U hg), frame_col hg _ (dualIx_out hi)]
  by_cases h : i = j
  · subst h; simp [sgnIx_sq]
  · simp [h, dualIx_inj, Ne.symm h]

lemma frame_ne_zero (hg : PI.UpqRep.IsFrameW k r z g) {i j : Fin (2 * r + k + 1)} (h : g i j ≠ 0) :
    i.val = j.val ∨ ((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)) := by
  by_contra hc
  apply h
  have hne : i ≠ j := fun e => hc (Or.inl (by rw [e]))
  by_cases hi : i.val < r ∨ r + k < i.val
  · rw [frame_row hg hi, if_neg hne]
  · rw [frame_col hg i (by omega), if_neg hne]

lemma frame_inv_ne_zero (hg : PI.UpqRep.IsFrameW k r z g) {i j : Fin (2 * r + k + 1)} (h : g⁻¹ i j ≠ 0) :
    i.val = j.val ∨ ((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)) := by
  by_contra hc
  apply h
  have hne : i ≠ j := fun e => hc (Or.inl (by rw [e]))
  by_cases hi : i.val < r ∨ r + k < i.val
  · rw [frame_inv_row hg hi, if_neg hne]
  · rw [frame_inv_col hg i (by omega), if_neg hne]

lemma frame_support (hg : PI.UpqRep.IsFrameW k r z g) (a b : Fin (2 * r + k + 1)) (hab : a < b)
    (h : ¬ (r ≤ a.val ∧ b.val ≤ r + k)) (i j : Fin (2 * r + k + 1))
    (hij : ¬ (i < j ∧ ¬ (r ≤ i.val ∧ j.val ≤ r + k))) :
    (g * Matrix.single a b (1 : ℂ) * g⁻¹) i j = 0 := by
  rw [conj_single_apply]
  by_contra hc
  have h1 := frame_ne_zero hg (left_ne_zero_of_mul hc)
  have h2 := frame_inv_ne_zero hg (right_ne_zero_of_mul hc)
  rw [Fin.lt_def] at hab hij
  omega

lemma ell_conj_single (hg : PI.UpqRep.IsFrameW k r z g) (a b : Fin (2 * r + k + 1)) :
    ell k r z (g * Matrix.single a b (1 : ℂ) * g⁻¹) =
      if b.val = a.val + 1 ∧ b.val < r then 1
      else if a.val + 1 = r ∧ b.val = r + k then ((Real.sqrt (Tz k r z) : ℝ) : ℂ) else 0 := by
  have key : ∀ c : Fin r,
      (if h : c.val + 1 < r then (g * Matrix.single a b (1 : ℂ) * g⁻¹) (eI k r c) (eI k r ⟨c.val + 1, h⟩)
        else ((g * Matrix.single a b (1 : ℂ) * g⁻¹) *ᵥ z) (eI k r c)) =
      if c.val = a.val then (if b.val = a.val + 1 ∧ b.val < r then 1
        else if a.val + 1 = r ∧ b.val = r + k then ((Real.sqrt (Tz k r z) : ℝ) : ℂ) else 0) else 0 := by
    intro c
    have hc := c.isLt
    have hrow : g (eI k r c) a = if c.val = a.val then 1 else 0 := by
      rw [frame_row hg (Or.inl hc)]
      simp only [Fin.ext_iff, eI]
    by_cases h : c.val + 1 < r
    · rw [dif_pos h, conj_single_apply, hrow, frame_inv_col hg _ (Or.inl h)]
      simp only [Fin.ext_iff, eI]
      split_ifs <;> first | omega | simp
    · rw [dif_neg h, ← Matrix.mulVec_mulVec, frame_inv_mulVec_negativeVector hg, Matrix.mulVec_smul, Pi.smul_apply]
      have : ((g * Matrix.single a b (1 : ℂ)) *ᵥ
          Pi.single (⟨r + k, by omega⟩ : Fin (2 * r + k + 1)) (1 : ℂ)) (eI k r c) =
          g (eI k r c) a * if b.val = r + k then 1 else 0 := by
        have := conj_single_apply g 1 a b (eI k r c) ⟨r + k, by omega⟩
        rw [Matrix.mul_one, Matrix.one_apply] at this
        simp only [Fin.ext_iff] at this
        rw [← this]
        simp
      rw [this, hrow]
      split_ifs <;> first | omega | simp
  unfold ell
  rw [Finset.sum_congr rfl fun c _ => key c]
  by_cases ha : a.val < r
  · rw [Finset.sum_eq_single (⟨a.val, ha⟩ : Fin r)]
    · simp
    · intro c _ hc
      rw [if_neg fun e => hc (Fin.ext e)]
    · simp
  · rw [Finset.sum_eq_zero, if_neg (by omega), if_neg (by omega)]
    intro c _
    have := c.isLt
    rw [if_neg (by omega)]

lemma norm_ell_sub (hg : PI.UpqRep.IsFrameW k r z g) (a b : Fin (2 * r + k + 1)) :
    ‖ell k r z (g * Matrix.single a b 1 * g⁻¹) -
      star (ell k r z (-(Hpk k r * (g * Matrix.single a b (1 : ℂ) * g⁻¹)ᴴ * Hpk k r)))‖ =
    if b.val = a.val + 1 ∧ (b.val < r ∨ r + k < a.val) then (1 : ℝ)
    else if (a.val + 1 = r ∧ b.val = r + k) ∨ (a.val = r + k ∧ b.val = r + k + 1) then
      Real.sqrt (Tz k r z) else 0 := by
  have := a.isLt
  have := b.isLt
  have c1 : ((dualIx k r a).val = (dualIx k r b).val + 1 ∧ (dualIx k r a).val < r) ↔
      (b.val = a.val + 1 ∧ r + k < a.val) := by
    rw [dualIx_val, dualIx_val]; split_ifs <;> omega
  have c2 : ((dualIx k r b).val + 1 = r ∧ (dualIx k r a).val = r + k) ↔
      (a.val = r + k ∧ b.val = r + k + 1) := by
    rw [dualIx_val, dualIx_val]; split_ifs <;> omega
  rw [theta_conj (frame_U hg), ell_neg_smul, ell_conj_single hg, ell_conj_single hg]
  simp only [c1, c2]
  have hs : ‖sgnIx k r b * sgnIx k r a‖ = 1 := by
    unfold sgnIx; split_ifs <;> simp
  generalize sgnIx k r b * sgnIx k r a = s at hs
  generalize hT : Real.sqrt (Tz k r z) = T
  have hT0 : 0 ≤ T := hT ▸ Real.sqrt_nonneg _
  split_ifs <;> first | omega | simp [abs_of_nonneg hT0, hs]

end Frame

theorem frame_matrix_units : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (g : Mx k r), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → PI.UpqRep.IsFrameW k r z g → IsUnit g ∧ (∀ a b : Fin (2 * r + k + 1), a < b → ¬ (r ≤ a.val ∧ b.val ≤ r + k) → (∀ i j : Fin (2 * r + k + 1), ¬ (i < j ∧ ¬ (r ≤ i.val ∧ j.val ≤ r + k)) → (g * Matrix.single a b (1 : ℂ) * g⁻¹) i j = 0) ∧ ‖Formalism.QuantumDeterminants.ell k r z (g * Matrix.single a b 1 * g⁻¹) - star (Formalism.QuantumDeterminants.ell k r z (-((Formalism.QuantumDeterminants.Hpk k r) * (g * Matrix.single a b (1 : ℂ) * g⁻¹)ᴴ * (Formalism.QuantumDeterminants.Hpk k r))))‖ = (if b.val = a.val + 1 ∧ (b.val < r ∨ r + k < a.val) then (1 : ℝ) else if (a.val + 1 = r ∧ b.val = r + k) ∨ (a.val = r + k ∧ b.val = r + k + 1) then Real.sqrt (Formalism.QuantumDeterminants.Tz k r z) else 0)) ∧ (Formalism.FourierDecayAlt.Q.IsFrameOf k r [z] (fun i : Fin k => g *ᵥ Pi.single ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) i) 1) ∧ ∀ i j : Fin k, Formalism.FourierDecayAlt.Q.unitB (Formalism.QuantumDeterminants.Hpk k r) (fun i : Fin k => g *ᵥ Pi.single ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) i) 1) i j = g * Matrix.single ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) i) ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) j) 1 * g⁻¹) ∧ g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z 0 = (if r = 0 then ((Real.sqrt (Formalism.QuantumDeterminants.Tz k r z) : ℝ) : ℂ) • Pi.single (Fin.last (2 * r + k)) 1 else Pi.single 0 1) ∧ gᵀ *ᵥ (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) = (if r = 0 then -((Real.sqrt (Formalism.QuantumDeterminants.Tz k r z) : ℝ) : ℂ) else 1) • Pi.single (Fin.last (2 * r + k)) 1 := by
  intro k r z g _ _ hg
  have hU := frame_U hg
  refine ⟨isUnit_U hU, fun a b hab h => ⟨frame_support hg a b hab h, norm_ell_sub hg a b⟩,
    ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · intro a i hi
    have := a.isLt
    have : g i ⟨r + a.val, by omega⟩ = 0 := by
      rw [frame_row hg hi, if_neg]
      simp only [Fin.ext_iff]; omega
    simpa using this
  · intro a b
    have := a.isLt
    have := b.isLt
    rw [herm_U hU, herm_single, Pi.single_apply]
    unfold sgnIx
    simp only [Fin.ext_iff, dualIx_val]
    split_ifs <;> first | omega | simp
  · intro a v hv
    have := a.isLt
    rw [List.mem_singleton.mp hv, herm_U'' hU, frame_inv_mulVec_negativeVector hg, herm_smul_right, herm_single,
      Pi.single_apply, if_neg, mul_zero, mul_zero]
    simp only [Fin.ext_iff, dualIx_val]
    split_ifs <;> omega
  · intro i j
    have := i.isLt
    have := j.isLt
    ext p q
    rw [conj_single_apply]
    unfold Formalism.FourierDecayAlt.Q.unitB
    rw [Matrix.of_apply, herm_U' hU, herm_single]
    have e1 : dualIx k r ⟨r + j.val, by omega⟩ = ⟨r + j.val, by omega⟩ := by
      unfold dualIx; rw [if_neg]; simp only; omega
    have e2 : sgnIx k r ⟨r + j.val, by omega⟩ = 1 := by
      unfold sgnIx; rw [if_neg]; simp only; omega
    rw [e1, e2]
    simp [bvec]
  · unfold fvec
    by_cases h : r = 0
    · rw [if_pos h, dif_neg (by simp [h]), frame_inv_mulVec_negativeVector hg]
      subst h
      congr 2
    · have h0 : (0 : Fin (r + 1)).val < r := by simp; omega
      rw [if_neg h, dif_pos h0]
      exact frame_inv_fix hg (j := 0) (Or.inl (by simp; omega))
  · funext d
    have hd := d.isLt
    have e : (gᵀ *ᵥ flat k r (fvec k r z 0)) d =
        herm (Hpk k r) (g *ᵥ Pi.single d 1) (fvec k r z 0) := by
      unfold flat herm
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    rw [e, herm_U'' hU]
    unfold fvec
    by_cases h : r = 0
    · rw [if_pos h, dif_neg (by simp [h]), frame_inv_mulVec_negativeVector hg, herm_smul_right, herm_single]
      unfold sgnIx
      simp only [Pi.smul_apply, Pi.single_apply, Fin.ext_iff, dualIx_val, Fin.val_last]
      split_ifs <;> first | omega | simp
    · have h0 : (0 : Fin (r + 1)).val < r := by simp; omega
      rw [if_neg h, dif_pos h0]
      have := frame_inv_fix hg (j := 0) (Or.inl (by simp; omega))
      have e0 : bvec (eI k r ⟨(0 : Fin (r + 1)).val, h0⟩) = Pi.single (0 : Fin (2 * r + k + 1)) (1 : ℂ) := rfl
      rw [e0, this, herm_single]
      unfold sgnIx
      simp only [Pi.smul_apply, Pi.single_apply, Fin.ext_iff, dualIx_val, Fin.val_last, Fin.val_zero]
      have hr : 0 < r := Nat.pos_of_ne_zero h
      have hr' : ¬ 0 = r + k := by omega
      simp [hr, hr', eq_comm]

end GlobalTheory.CapFrame
