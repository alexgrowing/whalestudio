import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.LevelDeterminantOfTriangularChange

noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace BL

theorem ell_col (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) :
    ell k r z g = ∑ a : Fin r, (g *ᵥ fvec k r z ⟨a.val + 1, by omega⟩) (eI k r a) := by
  unfold ell
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : a.val + 1 < r
  · rw [dif_pos h]
    first
      | simp [fvec, h, bvec, Matrix.mulVec_single_one]
      | simp [fvec, h, bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  · rw [dif_neg h]
    simp [fvec, h]

section Lv2
variable {k r' : ℕ}

theorem hpk_sh (p q : Fin (2 * r' + k + 1)) : Hpk k (1 + r') (sh p) (sh q) = Hpk k r' p q := by
  simp only [Hpk, sh, Fin.ext_iff, Fin.val_mk]
  have e1 : (p.val + 1 < 1 + r' ∧ p.val + 1 + (q.val + 1) = 2 * (1 + r') + k) ↔
      (p.val < r' ∧ p.val + q.val = 2 * r' + k) := by
    constructor <;> intro h <;> omega
  have e2 : (q.val + 1 < 1 + r' ∧ p.val + 1 + (q.val + 1) = 2 * (1 + r') + k) ↔
      (q.val < r' ∧ p.val + q.val = 2 * r' + k) := by
    constructor <;> intro h <;> omega
  have e3 : (1 + r' ≤ p.val + 1 ∧ p.val + 1 ≤ 1 + r' + k ∧ p.val + 1 = q.val + 1) ↔
      (r' ≤ p.val ∧ p.val ≤ r' + k ∧ p.val = q.val) := by
    constructor <;> intro h <;> omega
  have e4 : (p.val + 1 = 1 + r' + k) ↔ (p.val = r' + k) := by
    constructor <;> intro h <;> omega
  simp only [e1, e2, e3, e4]

theorem hpk_out (p : Fin (2 * (1 + r') + k + 1)) (hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k)
    (q : Fin (2 * r' + k + 1)) : Hpk k (1 + r') p (sh q) = 0 := by
  have := p.isLt
  have := q.isLt
  simp only [Hpk, sh, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | omega

private lemma sum_eq_sum_sh_of_zero_at_edges (F : Fin (2 * (1 + r') + k + 1) → ℂ)
    (hF : ∀ p : Fin (2 * (1 + r') + k + 1), (p.val = 0 ∨ p.val = 2 * (1 + r') + k) → F p = 0) :
    ∑ p, F p = ∑ q : Fin (2 * r' + k + 1), F (sh q) := by
  have hinj : Function.Injective (fun q : Fin (2 * r' + k + 1) => (sh q : Fin (2 * (1 + r') + k + 1))) := by
    intro a b h
    simp only [sh, Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  rw [show ∑ q : Fin (2 * r' + k + 1), F (sh q) =
      ∑ p ∈ Finset.univ.map ⟨fun q : Fin (2 * r' + k + 1) => (sh q : Fin (2 * (1 + r') + k + 1)), hinj⟩, F p
      from (Finset.sum_map Finset.univ
        ⟨fun q : Fin (2 * r' + k + 1) => (sh q : Fin (2 * (1 + r') + k + 1)), hinj⟩ F).symm]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro p _ hp
  apply hF
  by_contra hc
  apply hp
  have := p.isLt
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
  refine ⟨⟨p.val - 1, by omega⟩, ?_⟩
  ext
  simp only [sh, Fin.val_mk]
  omega

private lemma liftVec_apply_sh (v : Fin (2 * r' + k + 1) → ℂ) (q : Fin (2 * r' + k + 1)) :
    liftVec k 1 r' v (sh q) = v q := by
  have h1 : 1 ≤ (sh q : Fin (2 * (1 + r') + k + 1)).val ∧
      (sh q : Fin (2 * (1 + r') + k + 1)).val < 2 * r' + k + 1 + 1 := by
    have := q.isLt
    simp only [sh, Fin.val_mk]
    omega
  simp only [liftVec]
  rw [dif_pos h1]
  exact congrArg v (Fin.ext (by simp [sh]))

theorem hpk_lv (v : Fin (2 * r' + k + 1) → ℂ) :
    Hpk k (1 + r') *ᵥ liftVec k 1 r' v = liftVec k 1 r' (Hpk k r' *ᵥ v) := by
  funext p
  simp only [Matrix.mulVec, dotProduct]
  refine (sum_eq_sum_sh_of_zero_at_edges _ ?_).trans ?_
  · intro j hj
    have h0 : ¬(1 ≤ j.val ∧ j.val < 2 * r' + k + 1 + 1) := by omega
    simp only [liftVec, dif_neg h0, mul_zero]
  · simp only [liftVec_apply_sh]
    by_cases hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k
    · have h0 : ¬(1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1) := by omega
      simp only [hpk_out p hp, zero_mul, Finset.sum_const_zero, liftVec, dif_neg h0]
    · have hp' : p = sh ⟨p.val - 1, by have := p.isLt; omega⟩ := by
        ext
        simp only [sh, Fin.val_mk]
        omega
      rw [hp']
      simp only [hpk_sh, liftVec_apply_sh, Matrix.mulVec, dotProduct]

theorem herm_lv (v w : Fin (2 * r' + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) (liftVec k 1 r' v) (liftVec k 1 r' w) = herm (Hpk k r') v w := by
  unfold herm
  rw [hpk_lv]
  simp only [dotProduct, Pi.star_apply]
  refine (sum_eq_sum_sh_of_zero_at_edges _ ?_).trans ?_
  · intro p hp
    have h0 : ¬(1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1) := by omega
    simp only [liftVec, dif_neg h0, mul_zero]
  · simp only [liftVec_apply_sh]

theorem hermitianForm_liftVec_firstVector (v : Fin (2 * r' + k + 1) → ℂ) : herm (Hpk k (1 + r')) (liftVec k 1 r' v) (e0 k r') = 0 := by
  unfold herm
  rw [hpk_lv]
  simp [e0, bvec, dotProduct, Pi.single_apply, liftVec, eI, a0]
  apply Finset.sum_eq_zero
  intro x _
  split_ifs with h1 h2 <;> first | rfl | (rw [h2] at h1; simp at h1)

theorem firstVector_apply_first (h : 0 < 1 + r') : e0 k r' (eI k (1 + r') ⟨0, h⟩) = 1 := by
  simp [e0, bvec, a0, eI]

theorem firstVector_apply_succ (b : ℕ) (h : b + 1 < 1 + r') : e0 k r' (eI k (1 + r') ⟨b + 1, h⟩) = 0 := by
  simp [e0, bvec, a0, eI, Pi.single_apply]

theorem eI_succ (b : ℕ) (h : b + 1 < 1 + r') : eI k (1 + r') ⟨b + 1, h⟩ = sh (eI k r' ⟨b, by omega⟩) := by
  ext
  simp [eI, sh]

private lemma lev_apply_sh_sh (m : Mat k r') (p q : Fin (2 * r' + k + 1)) :
    ιLev k 1 r' m (sh p) (sh q) = m p q := by
  have hp : 1 ≤ (sh p : Fin (2 * (1 + r') + k + 1)).val ∧
      (sh p : Fin (2 * (1 + r') + k + 1)).val < 2 * r' + k + 1 + 1 := by
    have := p.isLt
    simp only [sh, Fin.val_mk]
    omega
  have hq : 1 ≤ (sh q : Fin (2 * (1 + r') + k + 1)).val ∧
      (sh q : Fin (2 * (1 + r') + k + 1)).val < 2 * r' + k + 1 + 1 := by
    have := q.isLt
    simp only [sh, Fin.val_mk]
    omega
  simp only [ιLev]
  rw [dif_pos hp, dif_pos hq]
  exact congrArg₂ m (Fin.ext (by simp [sh])) (Fin.ext (by simp [sh]))

private lemma lev_mulVec_liftVec_eq_liftVec_mulVec (m : Mat k r') (w : Fin (2 * r' + k + 1) → ℂ) :
    ιLev k 1 r' m *ᵥ liftVec k 1 r' w = liftVec k 1 r' (m *ᵥ w) := by
  funext p
  simp only [Matrix.mulVec, dotProduct]
  refine (sum_eq_sum_sh_of_zero_at_edges _ ?_).trans ?_
  · intro j hj
    have h0 : ¬(1 ≤ j.val ∧ j.val < 2 * r' + k + 1 + 1) := by omega
    simp only [liftVec, dif_neg h0, mul_zero]
  · simp only [liftVec_apply_sh]
    by_cases hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k
    · have h0 : ¬(1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1) := by omega
      have hz : ∀ q : Fin (2 * r' + k + 1), ιLev k 1 r' m p (sh q) = 0 := by
        intro q
        have hne : p ≠ sh q := by
          intro he
          rw [he] at hp
          have := q.isLt
          simp only [sh, Fin.val_mk] at hp
          omega
        simp only [ιLev, dif_neg h0, if_neg hne]
      simp only [hz, zero_mul, Finset.sum_const_zero, liftVec, dif_neg h0]
    · have hp' : p = sh ⟨p.val - 1, by have := p.isLt; omega⟩ := by
        ext
        simp only [sh, Fin.val_mk]
        omega
      rw [hp']
      simp only [lev_apply_sh_sh, liftVec_apply_sh, Matrix.mulVec, dotProduct]

theorem hcol (hHA : HeisAct) (m : Mat k r') (X : HPar k r') (w : Fin (2 * r' + k + 1) → ℂ) :
    (heis0 k r' X * ιLev k 1 r' m) *ᵥ liftVec k 1 r' w =
      liftVec k 1 r' (m *ᵥ w) - herm (Hpk k r') (m *ᵥ w) X.1 • e0 k r' := by
  unfold HeisAct at hHA
  rw [← Matrix.mulVec_mulVec, lev_mulVec_liftVec_eq_liftVec_mulVec]
  unfold heis0
  rw [hHA, herm_lv, hermitianForm_liftVec_firstVector, zero_smul, add_zero]

theorem sum_fin_one_add_eq_add_sum {M : Type} [AddCommMonoid M] (F : Fin (1 + r') → M) :
    ∑ a, F a = F ⟨0, by omega⟩ + ∑ a' : Fin r', F ⟨a'.val + 1, by omega⟩ := by
  rw [← Fintype.sum_equiv (finCongr (Nat.add_comm r' 1))
    (fun a : Fin (r' + 1) => F (finCongr (Nat.add_comm r' 1) a)) F (fun _ => rfl), Fin.sum_univ_succ]
  refine congrArg₂ (· + ·) ?_ ?_
  · exact congrArg F (Fin.ext (by simp))
  · exact Finset.sum_congr rfl fun a _ => congrArg F (Fin.ext (by simp))

private lemma liftVec_bvec_eq_bvec_sh (i : Fin (2 * r' + k + 1)) :
    liftVec k 1 r' (bvec i) = bvec (sh i) := by
  funext p
  by_cases hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k
  · have h0 : ¬(1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1) := by omega
    have hne : p ≠ sh i := by
      intro he
      rw [he] at hp
      have := i.isLt
      simp only [sh, Fin.val_mk] at hp
      omega
    simp only [liftVec, dif_neg h0, bvec, Pi.single_apply, if_neg hne]
  · have hp' : p = sh ⟨p.val - 1, by have := p.isLt; omega⟩ := by
      ext
      simp only [sh, Fin.val_mk]
      omega
    rw [hp', liftVec_apply_sh]
    simp [bvec, Pi.single_apply, sh, Fin.ext_iff]

theorem fvec_lift (z1 : Fin (2 * r' + k + 1) → ℂ) (a : Fin (1 + r')) :
    fvec k (1 + r') (liftVec k 1 r' z1) ⟨a.val + 1, by omega⟩ = liftVec k 1 r' (fvec k r' z1 ⟨a.val, by omega⟩) := by
  by_cases ha : a.val < r'
  · have h1 : a.val + 1 < 1 + r' := by omega
    simp only [fvec, Fin.val_mk, dif_pos h1, dif_pos ha]
    rw [eI_succ a.val h1]
    exact (liftVec_bvec_eq_bvec_sh _).symm
  · have h1 : ¬ a.val + 1 < 1 + r' := by omega
    simp only [fvec, Fin.val_mk, dif_neg h1, dif_neg ha]

private lemma liftVec_apply_eI_zero_eq_zero (v : Fin (2 * r' + k + 1) → ℂ) (h : 0 < 1 + r') :
    liftVec k 1 r' v (eI k (1 + r') ⟨0, h⟩) = 0 := by
  simp [liftVec, eI]

theorem ell_lev (hHA : HeisAct) (z1 : Fin (2 * r' + k + 1) → ℂ) (m : Mat k r') (X : HPar k r') :
    ell k (1 + r') (liftVec k 1 r' z1) (heis0 k r' X * ιLev k 1 r' m) =
      -herm (Hpk k r') (m *ᵥ fvec k r' z1 ⟨0, by omega⟩) X.1 + ell k r' z1 m := by
  have key : ∀ a : Fin (1 + r'),
      ((heis0 k r' X * ιLev k 1 r' m) *ᵥ fvec k (1 + r') (liftVec k 1 r' z1) ⟨a.val + 1, by omega⟩)
        (eI k (1 + r') a) =
      liftVec k 1 r' (m *ᵥ fvec k r' z1 ⟨a.val, by omega⟩) (eI k (1 + r') a) -
        herm (Hpk k r') (m *ᵥ fvec k r' z1 ⟨a.val, by omega⟩) X.1 * e0 k r' (eI k (1 + r') a) := by
    intro a
    rw [fvec_lift, hcol hHA]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [ell_col, ell_col, sum_fin_one_add_eq_add_sum]
  refine congrArg₂ (· + ·) ?_ (Finset.sum_congr rfl fun a' _ => ?_)
  · beta_reduce
    rw [key, firstVector_apply_first, liftVec_apply_eI_zero_eq_zero, mul_one, zero_sub]
  · beta_reduce
    rw [key, firstVector_apply_succ, mul_zero, sub_zero, eI_succ, liftVec_apply_sh]

theorem lam_lev (hHA : HeisAct) (z1 : Fin (2 * r' + k + 1) → ℂ) (m : Mat k r') (X : HPar k r') :
    lam k (1 + r') (liftVec k 1 r' z1) (heis0 k r' X * ιLev k 1 r' m) =
      -2 * (herm (Hpk k r') (m *ᵥ fvec k r' z1 ⟨0, by omega⟩) X.1).im + lam k r' z1 m := by
  simp only [lam, cStd]
  rw [ell_lev hHA]
  simp only [mul_add, mul_neg, Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.neg_im]
  norm_num

theorem z_lift (z : Fin (2 * (1 + r') + k + 1) → ℂ) (hz : inWb k (1 + r') z) :
    z = liftVec k 1 r' (fun q => z (sh q)) := by
  unfold inWb at hz
  funext p
  by_cases hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k
  · have h0 : ¬(1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1) := by omega
    rw [hz p (by omega)]
    simp only [liftVec, dif_neg h0]
  · have hp' : p = sh ⟨p.val - 1, by have := p.isLt; omega⟩ := by
      ext
      simp only [sh, Fin.val_mk]
      omega
    rw [hp', liftVec_apply_sh]

theorem shifted_mem_weightSpace (z : Fin (2 * (1 + r') + k + 1) → ℂ) (hz : inWb k (1 + r') z) : inWb k r' (fun q => z (sh q)) := by
  unfold inWb at hz ⊢
  intro i hi
  have := i.isLt
  exact hz (sh i) (by simp only [sh, Fin.val_mk]; omega)

theorem tz_lift (z1 : Fin (2 * r' + k + 1) → ℂ) : Tz k (1 + r') (liftVec k 1 r' z1) = Tz k r' z1 := by
  unfold Tz
  rw [herm_lv]

end Lv2

end BL

end ReciprocityTheory.ChartRestriction.DS.Xi
