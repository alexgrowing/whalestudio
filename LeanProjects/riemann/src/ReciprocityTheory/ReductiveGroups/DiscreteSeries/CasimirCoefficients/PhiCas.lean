import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiCasA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiCasB

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

private theorem isUpperTri_one : IsUpperTri (1 : Matrix (Fin n) (Fin n) ℂ) :=
  fun _ _ h => Matrix.one_apply_ne h.ne'

private theorem isLowerTri_one : IsLowerTri (1 : Matrix (Fin n) (Fin n) ℂ) :=
  fun _ _ h => Matrix.one_apply_ne h.ne

private theorem diag_line (a l : Fin n) (t : ℂ) :
    (1 + t • Matrix.single a a (1 : ℂ)) l l = if l = a then 1 + t else 1 := by
  by_cases h : l = a
  · subst h
    simp
  · have : ¬(a = l ∧ a = l) := fun h' => h h'.1.symm
    simp [h, Matrix.single_apply_of_ne (h := this)]

private theorem diag_prod (μ : Fin n → ℤ) (a : Fin n) (t : ℂ) :
    ∏ l, ((if l = a then 1 + t else 1) : ℂ) ^ (-μ l) = (1 + t) ^ (-μ a) := by
  rw [Finset.prod_eq_single a (fun l _ hl => by simp [hl]) (by simp)]
  simp

private theorem hasDerivAt_scale (μ : Fin n → ℤ) (a : Fin n) (c : ℂ) :
    HasDerivAt (fun t : ℂ => (1 + t) ^ (-μ a) * c) (-(μ a : ℂ) * c) 0 := by
  have h1 : HasDerivAt (fun t : ℂ => 1 + t) 1 0 := by
    simpa using (hasDerivAt_id' (0 : ℂ)).const_add 1
  have h2 := (hasDerivAt_zpow (-μ a) (1 + 0 : ℂ) (Or.inl (by simp))).comp (0 : ℂ) h1
  simpa [Function.comp_def] using h2.mul_const c

private theorem eventually_ne_line : ∀ᶠ t : ℂ in nhds 0, 1 + t ≠ 0 :=
  (continuous_const.add continuous_id).continuousAt.eventually_ne (by simp)

theorem lhol_phiM_lower (μ : Fin n → ℤ) {a b : Fin n} (hab : b < a) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : z ∈ OmegaSet n) : Lhol (Matrix.single a b 1) (PhiM μ) z = 0 := by
  have hconst : ∀ t : ℂ, PhiM μ (z + t • (Matrix.single a b 1 * z)) = PhiM μ z := by
    intro t
    have hc : IsLowerTri (1 + t • Matrix.single a b (1 : ℂ)) := by
      intro i j hij
      have : ¬(a = i ∧ b = j) := fun ⟨h1, h2⟩ => by
        subst h1; subst h2; exact absurd (hab.trans hij) (lt_irrefl _)
      simp [Matrix.one_apply_ne hij.ne, Matrix.single_apply_of_ne (h := this)]
    have hcd : ∀ l, (1 + t • Matrix.single a b (1 : ℂ)) l l = 1 := by
      intro l
      have : ¬(a = l ∧ b = l) := fun ⟨h1, h2⟩ => hab.ne' (h1.trans h2.symm)
      simp [Matrix.single_apply_of_ne (h := this)]
    obtain ⟨-, h⟩ := phiM_tri_mul μ hc isUpperTri_one (fun l => by rw [hcd l]; exact one_ne_zero)
      (fun l => by simp) hz
    have e : (1 + t • Matrix.single a b (1 : ℂ)) * z * 1 = z + t • (Matrix.single a b 1 * z) := by
      rw [Matrix.mul_one, add_mul, Matrix.one_mul, Matrix.smul_mul]
    rw [← e, h, Finset.prod_eq_one (fun l _ => by rw [hcd l, Matrix.one_apply_eq, mul_one, _root_.one_zpow]),
      one_mul]
  have hd := hasDerivAt_line (differentiableAt_phiM μ hz) (Matrix.single a b 1 * z)
  have h0 : HasDerivAt (fun t : ℂ => PhiM μ (z + t • (Matrix.single a b 1 * z))) 0 0 := by
    simp only [hconst]
    exact hasDerivAt_const _ _
  exact hd.unique h0

theorem rhol_phiM_upper (μ : Fin n → ℤ) {a b : Fin n} (hab : a < b) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : z ∈ OmegaSet n) : Rhol (Matrix.single a b 1) (PhiM μ) z = 0 := by
  have hconst : ∀ t : ℂ, PhiM μ (z + t • (z * Matrix.single a b 1)) = PhiM μ z := by
    intro t
    have hc : IsUpperTri (1 + t • Matrix.single a b (1 : ℂ)) := by
      intro i j hij
      have : ¬(a = i ∧ b = j) := fun ⟨h1, h2⟩ => by
        subst h1; subst h2; exact absurd (hab.trans hij) (lt_irrefl _)
      simp [Matrix.one_apply_ne hij.ne', Matrix.single_apply_of_ne (h := this)]
    have hcd : ∀ l, (1 + t • Matrix.single a b (1 : ℂ)) l l = 1 := by
      intro l
      have : ¬(a = l ∧ b = l) := fun ⟨h1, h2⟩ => hab.ne (h1.trans h2.symm)
      simp [Matrix.single_apply_of_ne (h := this)]
    obtain ⟨-, h⟩ := phiM_tri_mul μ isLowerTri_one hc (fun l => by simp)
      (fun l => by rw [hcd l]; exact one_ne_zero) hz
    have e : 1 * z * (1 + t • Matrix.single a b (1 : ℂ)) = z + t • (z * Matrix.single a b 1) := by
      rw [Matrix.one_mul, mul_add, Matrix.mul_one, Matrix.mul_smul]
    rw [← e, h, Finset.prod_eq_one (fun l _ => by rw [hcd l, Matrix.one_apply_eq, one_mul, _root_.one_zpow]),
      one_mul]
  have hd := hasDerivAt_line (differentiableAt_phiM μ hz) (z * Matrix.single a b 1)
  have h0 : HasDerivAt (fun t : ℂ => PhiM μ (z + t • (z * Matrix.single a b 1))) 0 0 := by
    simp only [hconst]
    exact hasDerivAt_const _ _
  exact hd.unique h0

theorem lhol_phiM_diag (μ : Fin n → ℤ) (a : Fin n) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    Lhol (Matrix.single a a 1) (PhiM μ) z = -(μ a : ℂ) * PhiM μ z := by
  have key : ∀ t : ℂ, 1 + t ≠ 0 →
      PhiM μ (z + t • (Matrix.single a a 1 * z)) = (1 + t) ^ (-μ a) * PhiM μ z := by
    intro t ht
    have hc : IsLowerTri (1 + t • Matrix.single a a (1 : ℂ)) := by
      intro i j hij
      have : ¬(a = i ∧ a = j) := fun ⟨h1, h2⟩ => hij.ne (h1.symm.trans h2)
      simp [Matrix.one_apply_ne hij.ne, Matrix.single_apply_of_ne (h := this)]
    obtain ⟨-, h⟩ := phiM_tri_mul μ hc isUpperTri_one
      (fun l => by rw [diag_line]; split_ifs <;> simp [ht]) (fun l => by simp) hz
    have e : (1 + t • Matrix.single a a (1 : ℂ)) * z * 1 = z + t • (Matrix.single a a 1 * z) := by
      rw [Matrix.mul_one, add_mul, Matrix.one_mul, Matrix.smul_mul]
    rw [← e, h]
    congr 1
    simp only [Matrix.one_apply_eq, mul_one, diag_line]
    exact diag_prod μ a t
  have hev : (fun t : ℂ => PhiM μ (z + t • (Matrix.single a a 1 * z))) =ᶠ[nhds 0]
      fun t => (1 + t) ^ (-μ a) * PhiM μ z := by
    filter_upwards [eventually_ne_line] with t ht using key t ht
  have hd := hasDerivAt_line (differentiableAt_phiM μ hz) (Matrix.single a a 1 * z)
  exact hd.unique ((hasDerivAt_scale μ a _).congr_of_eventuallyEq hev)

theorem rhol_phiM_diag (μ : Fin n → ℤ) (a : Fin n) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    Rhol (Matrix.single a a 1) (PhiM μ) z = -(μ a : ℂ) * PhiM μ z := by
  have key : ∀ t : ℂ, 1 + t ≠ 0 →
      PhiM μ (z + t • (z * Matrix.single a a 1)) = (1 + t) ^ (-μ a) * PhiM μ z := by
    intro t ht
    have hc : IsUpperTri (1 + t • Matrix.single a a (1 : ℂ)) := by
      intro i j hij
      have : ¬(a = i ∧ a = j) := fun ⟨h1, h2⟩ => hij.ne' (h1.symm.trans h2)
      simp [Matrix.one_apply_ne hij.ne', Matrix.single_apply_of_ne (h := this)]
    obtain ⟨-, h⟩ := phiM_tri_mul μ isLowerTri_one hc (fun l => by simp)
      (fun l => by rw [diag_line]; split_ifs <;> simp [ht]) hz
    have e : 1 * z * (1 + t • Matrix.single a a (1 : ℂ)) = z + t • (z * Matrix.single a a 1) := by
      rw [Matrix.one_mul, mul_add, Matrix.mul_one, Matrix.mul_smul]
    rw [← e, h]
    congr 1
    simp only [Matrix.one_apply_eq, one_mul, diag_line]
    exact diag_prod μ a t
  have hev : (fun t : ℂ => PhiM μ (z + t • (z * Matrix.single a a 1))) =ᶠ[nhds 0]
      fun t => (1 + t) ^ (-μ a) * PhiM μ z := by
    filter_upwards [eventually_ne_line] with t ht using key t ht
  have hd := hasDerivAt_line (differentiableAt_phiM μ hz) (z * Matrix.single a a 1)
  exact hd.unique ((hasDerivAt_scale μ a _).congr_of_eventuallyEq hev)

theorem lhol_lhol_phiM (μ : Fin n → ℤ) (a b : Fin n) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : z ∈ OmegaSet n) :
    Lhol (Matrix.single a b 1) (Lhol (Matrix.single b a 1) (PhiM μ)) z =
      ((casCoef μ a b : ℝ) : ℂ) * PhiM μ z := by
  have hO : IsOpen (OmegaSet n) := isOpen_omega
  have hlow : ∀ a b : Fin n, b < a →
      Lhol (Matrix.single b a 1) (Lhol (Matrix.single a b 1) (PhiM μ)) z = 0 := by
    intro a b hab
    have hev : Lhol (Matrix.single a b (1 : ℂ)) (PhiM μ) =ᶠ[nhds z] fun _ => (0 : ℂ) := by
      filter_upwards [hO.mem_nhds hz] with w hw using lhol_phiM_lower μ hab hw
    show fderiv ℂ (Lhol (Matrix.single a b (1 : ℂ)) (PhiM μ)) z _ = 0
    rw [hev.fderiv_eq]
    simp
  have e1 := lhol_phiM_diag μ a hz
  have e2 := lhol_phiM_diag μ b hz
  unfold Lhol at e1 e2
  rcases lt_trichotomy a b with h | rfl | h
  · rw [hlow b a h, casCoef, if_neg h.ne, if_neg (not_lt.mpr h.le)]
    simp
  · have hev : Lhol (Matrix.single a a (1 : ℂ)) (PhiM μ) =ᶠ[nhds z] fun w => -(μ a : ℂ) * PhiM μ w := by
      filter_upwards [hO.mem_nhds hz] with w hw using lhol_phiM_diag μ a hw
    have hf : fderiv ℂ (fun w => -(μ a : ℂ) * PhiM μ w) z = -(μ a : ℂ) • fderiv ℂ (PhiM μ) z :=
      ((differentiableAt_phiM μ hz).hasFDerivAt.const_mul (-(μ a : ℂ))).fderiv
    show fderiv ℂ (Lhol (Matrix.single a a (1 : ℂ)) (PhiM μ)) z _ = _
    rw [hev.fderiv_eq]
    erw [hf]
    rw [_root_.smul_apply, smul_eq_mul, e1, casCoef, if_pos rfl, if_neg (lt_irrefl a)]
    push_cast
    ring
  · rw [lhol_comm (contDiffAt_phiM μ hz) _ _, hlow a b h]
    simp only [Matrix.single_mul_single_same, mul_one, sub_mul, map_sub]
    rw [e1, e2, casCoef, if_neg h.ne', if_pos h]
    push_cast
    ring

theorem casL_phiM (μ : Fin n → ℤ) (lam : Fin n → ℝ) (hμ : IsMu lam μ) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : z ∈ OmegaSet n) : casL (PhiM μ) z = ((casVal lam : ℝ) : ℂ) * PhiM μ z := by
  show ∑ a, ∑ b, Lhol (Matrix.single a b 1) (Lhol (Matrix.single b a 1) (PhiM μ)) z = _
  simp only [lhol_lhol_phiM μ _ _ hz, ← Finset.sum_mul]
  rw [← sum_casCoef μ lam hμ]
  push_cast
  rfl

end ReciprocityTheory.ChartRestriction.DS.S7
