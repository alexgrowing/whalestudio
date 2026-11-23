import Mathlib
import Formalism.HermitianCurvature.StatementQ

open Matrix Finset

noncomputable section

namespace PI.IsotropicReflections

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

variable {k r : ℕ}

def sw (l : Fin r) (p : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if p = eI k r l then esI k r l else if p = esI k r l then eI k r l else p

def al (l : Fin r) (c : ℂ) (p : Fin (2 * r + k + 1)) : ℂ :=
  if p = eI k r l then c else if p = esI k r l then (star c)⁻¹ else 1

private lemma eI_val_weyl_conjugation_fixed_column (l : Fin r) : (eI k r l).val = l.val := rfl

private lemma esI_val' (l : Fin r) : (esI k r l).val = 2 * r + k - l.val := rfl

lemma eI_ne_esI (l : Fin r) : eI k r l ≠ esI k r l := by
  intro h
  have h' := congrArg Fin.val h
  rw [eI_val_weyl_conjugation_fixed_column, esI_val'] at h'
  have := l.isLt
  omega

lemma sw_e (l : Fin r) : sw (k := k) l (eI k r l) = esI k r l := by
  simp [sw]

lemma swap_dual_isotropic (l : Fin r) : sw (k := k) l (esI k r l) = eI k r l := by
  simp [sw, (eI_ne_esI l).symm]

lemma sw_o (l : Fin r) {p : Fin (2 * r + k + 1)} (h1 : p ≠ eI k r l) (h2 : p ≠ esI k r l) :
    sw l p = p := by
  simp [sw, h1, h2]

lemma al_e (l : Fin r) (c : ℂ) : al (k := k) l c (eI k r l) = c := by
  simp [al]

lemma reflection_scalar_dual_isotropic (l : Fin r) (c : ℂ) : al (k := k) l c (esI k r l) = (star c)⁻¹ := by
  simp [al, (eI_ne_esI l).symm]

lemma al_o (l : Fin r) (c : ℂ) {p : Fin (2 * r + k + 1)} (h1 : p ≠ eI k r l) (h2 : p ≠ esI k r l) :
    al l c p = 1 := by
  simp [al, h1, h2]

lemma trich (l : Fin r) (p : Fin (2 * r + k + 1)) :
    p = eI k r l ∨ p = esI k r l ∨ (p ≠ eI k r l ∧ p ≠ esI k r l) := by
  by_cases h1 : p = eI k r l
  · exact Or.inl h1
  · by_cases h2 : p = esI k r l
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ⟨h1, h2⟩)

lemma sw_sw (l : Fin r) (p : Fin (2 * r + k + 1)) : sw l (sw l p) = p := by
  rcases trich l p with h | h | ⟨h1, h2⟩
  · subst h
    rw [sw_e, swap_dual_isotropic]
  · subst h
    rw [swap_dual_isotropic, sw_e]
  · rw [sw_o l h1 h2, sw_o l h1 h2]

lemma weyl_lift_eq_pair (l : Fin r) (c : ℂ) (i q : Fin (2 * r + k + 1)) :
    w1 k r l c i q = if i = sw l q then al l c q else 0 := by
  rcases trich l q with hq | hq | ⟨hq1, hq2⟩ <;> rcases trich l i with hi | hi | ⟨hi1, hi2⟩ <;>
    (try subst hq) <;> (try subst hi) <;> (try have hq1' := Ne.symm hq1) <;> (try have hq2' := Ne.symm hq2) <;>
    (try have hi1' := Ne.symm hi1) <;> (try have hi2' := Ne.symm hi2) <;>
    simp [w1, sw_e, swap_dual_isotropic, al_e, reflection_scalar_dual_isotropic, sw_o, al_o, eI_ne_esI, (eI_ne_esI l).symm, *]

lemma reflection_row_formula (l : Fin r) (c : ℂ) (p i : Fin (2 * r + k + 1)) :
    w1 k r l c p i = if i = sw l p then al l c (sw l p) else 0 := by
  rw [weyl_lift_eq_pair]
  by_cases h : i = sw l p
  · subst h
    rw [sw_sw]
    simp
  · have h' : p ≠ sw l i := fun h' => h (by rw [h', sw_sw])
    simp [h, h']

lemma hpk_e_row (l : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r l) j = if j = esI k r l then 1 else 0 := by
  have hl := l.isLt
  have hj := j.isLt
  simp only [Hpk]
  split_ifs <;> (try simp only [Fin.ext_iff, eI_val_weyl_conjugation_fixed_column, esI_val'] at *) <;> first | rfl | omega

lemma hpk_s_row (l : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r l) j = if j = eI k r l then 1 else 0 := by
  have hl := l.isLt
  have hj := j.isLt
  simp only [Hpk]
  split_ifs <;> (try simp only [Fin.ext_iff, eI_val_weyl_conjugation_fixed_column, esI_val'] at *) <;> first | rfl | omega

lemma hpk_e_col (l : Fin r) (i : Fin (2 * r + k + 1)) :
    Hpk k r i (eI k r l) = if i = esI k r l then 1 else 0 := by
  have hl := l.isLt
  have hi := i.isLt
  simp only [Hpk]
  split_ifs <;> (try simp only [Fin.ext_iff, eI_val_weyl_conjugation_fixed_column, esI_val'] at *) <;> first | rfl | omega

lemma hpk_s_col (l : Fin r) (i : Fin (2 * r + k + 1)) :
    Hpk k r i (esI k r l) = if i = eI k r l then 1 else 0 := by
  have hl := l.isLt
  have hi := i.isLt
  simp only [Hpk]
  split_ifs <;> (try simp only [Fin.ext_iff, eI_val_weyl_conjugation_fixed_column, esI_val'] at *) <;> first | rfl | omega

lemma mulVec_bvec {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (j : Fin m) :
    M *ᵥ bvec j = fun i => M i j := by
  funext i
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

lemma herm_bvec {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ) (j : Fin m) :
    herm H v (bvec j) = (H *ᵥ v) j := by
  simp only [herm, bvec]
  rw [← Pi.single_star, star_one, single_dotProduct, one_mul]

lemma monomial_conj {m : ℕ} (w H : Matrix (Fin m) (Fin m) ℂ) (σ : Fin m → Fin m) (α : Fin m → ℂ)
    (hw : ∀ i q, w i q = if i = σ q then α q else 0) (p q : Fin m) :
    (wᴴ * H * w) p q = star (α p) * H (σ p) (σ q) * α q := by
  rw [Matrix.mul_apply]
  simp_rw [hw]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, hw, apply_ite (star : ℂ → ℂ), star_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

lemma conj_fixed_col {m : ℕ} (g H : Matrix (Fin m) (Fin m) ℂ) (p : Fin m)
    (hg : ∀ i, g i p = if i = p then 1 else 0) (q : Fin m) :
    (gᴴ * H * g) p q = ∑ j, H p j * g j q := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, hg, apply_ite (star : ℂ → ℂ), star_one, star_zero, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

lemma reflection_mem_unitary (l : Fin r) (c : ℂ) (hc : c ≠ 0) : w1 k r l c ∈ UH (Hpk k r) := by
  simp only [UH, Set.mem_setOf_eq]
  ext p q
  rw [monomial_conj _ _ (sw l) (al l c) (weyl_lift_eq_pair l c)]
  rcases trich l p with hp | hp | ⟨hp1, hp2⟩ <;> rcases trich l q with hq | hq | ⟨hq1, hq2⟩ <;>
    (try subst hp) <;> (try subst hq) <;>
    simp [sw_e, swap_dual_isotropic, al_e, reflection_scalar_dual_isotropic, sw_o, al_o, hpk_e_row, hpk_s_row, hpk_e_col, hpk_s_col, eI_ne_esI,
      (eI_ne_esI l).symm, hc, *]

lemma reflection_fixes_basis_vector (l : Fin r) (c : ℂ) (j : Fin (2 * r + k + 1)) (h1 : j ≠ eI k r l) (h2 : j ≠ esI k r l) :
    w1 k r l c *ᵥ bvec j = bvec j := by
  rw [mulVec_bvec]
  funext i
  rw [weyl_lift_eq_pair, sw_o l h1 h2, al_o l c h1 h2]
  simp [bvec, Pi.single_apply]

lemma reflection_mem_Glev_castSucc (l : Fin r) (c : ℂ) (hc : c ≠ 0) : w1 k r l c ∈ Glev k r l.castSucc := by
  simp only [Glev, Set.mem_setOf_eq]
  refine ⟨reflection_mem_unitary l c hc, fun a ha => ?_⟩
  have hal : a.val < l.val := by simpa using ha
  have h1 := a.isLt
  have h2 := l.isLt
  refine ⟨reflection_fixes_basis_vector l c _ ?_ ?_, reflection_fixes_basis_vector l c _ ?_ ?_⟩ <;> intro h <;> have h' := congrArg Fin.val h <;>
    simp only [eI_val_weyl_conjugation_fixed_column, esI_val'] at h' <;> omega

section G

variable (l : Fin r) (g : Mx k r) (hg : g ∈ Glev k r l.succ)
include hg

lemma g_col_e (i : Fin (2 * r + k + 1)) : g i (eI k r l) = if i = eI k r l then 1 else 0 := by
  have h := hg
  simp only [Glev, Set.mem_setOf_eq] at h
  have e := (h.2 l (by simp)).1
  rw [mulVec_bvec] at e
  have e' := congrFun e i
  simpa [bvec, Pi.single_apply] using e'

lemma diagonal_column_dual_isotropic (i : Fin (2 * r + k + 1)) : g i (esI k r l) = if i = esI k r l then 1 else 0 := by
  have h := hg
  simp only [Glev, Set.mem_setOf_eq] at h
  have e := (h.2 l (by simp)).2
  rw [mulVec_bvec] at e
  have e' := congrFun e i
  simpa [bvec, Pi.single_apply] using e'

lemma diagonal_row_dual_isotropic (j : Fin (2 * r + k + 1)) : g (esI k r l) j = if j = esI k r l then 1 else 0 := by
  have h := hg
  simp only [Glev, UH, Set.mem_setOf_eq] at h
  have e := conj_fixed_col g (Hpk k r) (eI k r l) (g_col_e l g hg) j
  rw [h.1] at e
  simp only [hpk_e_row, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at e
  exact e.symm

lemma g_row_e (j : Fin (2 * r + k + 1)) : g (eI k r l) j = if j = eI k r l then 1 else 0 := by
  have h := hg
  simp only [Glev, UH, Set.mem_setOf_eq] at h
  have e := conj_fixed_col g (Hpk k r) (esI k r l) (diagonal_column_dual_isotropic l g hg) j
  rw [h.1] at e
  simp only [hpk_s_row, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at e
  exact e.symm

lemma g_mem_cast : g ∈ Glev k r l.castSucc := by
  have h := hg
  simp only [Glev, Set.mem_setOf_eq] at h ⊢
  refine ⟨h.1, fun a ha => h.2 a ?_⟩
  simp only [Fin.coe_castSucc, Fin.val_succ] at ha ⊢
  omega

lemma w1_commute_of_mem_Glev (c : ℂ) : w1 k r l c * g = g * w1 k r l c := by
  ext p q
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp_rw [reflection_row_formula l c p, (weyl_lift_eq_pair l c · q)]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hr1 := g_row_e l g hg
  have hr2 := diagonal_row_dual_isotropic l g hg
  have hc1 := g_col_e l g hg
  have hc2 := diagonal_column_dual_isotropic l g hg
  rcases trich l p with hp | hp | ⟨hp1, hp2⟩ <;> rcases trich l q with hq | hq | ⟨hq1, hq2⟩ <;>
    (try subst hp) <;> (try subst hq) <;>
    simp [sw_e, swap_dual_isotropic, al_e, reflection_scalar_dual_isotropic, sw_o, al_o, eI_ne_esI, (eI_ne_esI l).symm, *]

lemma reflection_hermitian_value (c : ℂ) :
    herm (Hpk k r) ((w1 k r l c * g) *ᵥ bvec (eI k r l)) (bvec (eI k r l)) = c := by
  have h := hg
  simp only [Glev, Set.mem_setOf_eq] at h
  have hge : g *ᵥ bvec (eI k r l) = bvec (eI k r l) := (h.2 l (by simp)).1
  rw [herm_bvec, ← Matrix.mulVec_mulVec, hge, mulVec_bvec]
  simp only [Matrix.mulVec, dotProduct, hpk_e_row, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  rw [weyl_lift_eq_pair, sw_e, al_e]
  simp

end G

theorem isotropic_reflection_properties : Formalism.FourierDecayAlt.Q.WeylLevelElementFacts := by
  intro k r l c hc
  exact ⟨reflection_mem_Glev_castSucc l c hc, fun g hg => ⟨g_mem_cast l g hg, w1_commute_of_mem_Glev l g hg c, reflection_hermitian_value l g hg c⟩⟩

end PI.IsotropicReflections
