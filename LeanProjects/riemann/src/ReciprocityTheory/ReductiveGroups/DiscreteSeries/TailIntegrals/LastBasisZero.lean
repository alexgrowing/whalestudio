import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Phi2

noncomputable section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder

namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem ea_k_iff {k r : ℕ} {κ : Mat k r} : κ ∈ Kset k r ↔ κ ∈ GV k r ∧ κᴴ * κ = 1 := by
  first
    | exact Iff.rfl
    | simp only [Kset, Set.mem_setOf_eq]

theorem ea_gv_mul {k r : ℕ} {a b : Mat k r} (ha : a ∈ GV k r) (hb : b ∈ GV k r) : a * b ∈ GV k r := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

theorem ea_k_mul {k r : ℕ} {a b : Mat k r} (ha : a ∈ Kset k r) (hb : b ∈ Kset k r) : a * b ∈ Kset k r := by
  obtain ⟨ha1, ha2⟩ := ea_k_iff.1 ha
  obtain ⟨hb1, hb2⟩ := ea_k_iff.1 hb
  refine ea_k_iff.2 ⟨ea_gv_mul ha1 hb1, ?_⟩
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * (a * b) = bᴴ * (aᴴ * a) * b := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [ha2, Matrix.mul_one, hb2]

theorem ea_k_inv_mem {k r : ℕ} {κ : Mat k r} (h : κ ∈ Kset k r) : κ⁻¹ ∈ GV k r := by
  obtain ⟨h1, h2⟩ := ea_k_iff.1 h
  have hinv : κ⁻¹ = κᴴ := Matrix.inv_eq_left_inv h2
  have h3 : κ * κᴴ = 1 := by
    first
      | exact mul_eq_one_comm.1 h2
      | (rw [← hinv]; exact Matrix.mul_nonsing_inv κ (Matrix.isUnit_det_of_left_inverse h2))
  have hH : κᴴ * Hpk k r * κ = Hpk k r := h1
  show (κ⁻¹)ᴴ * Hpk k r * κ⁻¹ = Hpk k r
  rw [hinv, Matrix.conjTranspose_conjTranspose]
  calc κ * Hpk k r * κᴴ = κ * (κᴴ * Hpk k r * κ) * κᴴ := by rw [hH]
    _ = (κ * κᴴ) * Hpk k r * (κ * κᴴ) := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [h3, Matrix.one_mul, Matrix.mul_one]

theorem ea_dot_unit {k r : ℕ} {κ : Mat k r} (h : κᴴ * κ = 1) (v w : Fin (2 * r + k + 1) → ℂ) :
    star (κ *ᵥ v) ⬝ᵥ (κ *ᵥ w) = star v ⬝ᵥ w := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

theorem ea_one_gv (k r : ℕ) : (1 : Mat k r) ∈ GV k r := by
  show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
  simp

theorem ea_lift_zero (k r' : ℕ) : liftVec k 1 r' (0 : Fin (2 * r' + k + 1) → ℂ) = 0 := by
  funext p
  simp only [liftVec]
  split_ifs <;> rfl

theorem ea_heis0_zero (k r' : ℕ) : heis0 k r' ((0 : Fin (2 * r' + k + 1) → ℂ), (0 : ℝ)) = 1 := by
  have hh : hb k r' 0 0 = 0 := by simp [hb, herm]
  have hl := ea_lift_zero k r'
  simp only [heis0, hl, hh, heisG]
  ext i j
  simp [Matrix.vecMulVec, herm]

theorem ea_lev_one (k r' : ℕ) : ιLev k 1 r' (1 : Mat k r') = 1 := by
  ext p q
  have hp := p.isLt
  have hq := q.isLt
  simp only [ιLev, Matrix.one_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem ea_inv_one (k r : ℕ) : (1 : Mat k r)⁻¹ = 1 := by
  first
    | exact Matrix.inv_one
    | simp

theorem rankOne_mem_unitary {k r' : ℕ} (hOSM : OneStepMem) {c : ℂ} (hc : c ≠ 0) : w0 k r' c ∈ GV k (1 + r') := by
  have h := (hOSM k r' (0, 0) (0, 0) c hc 1 (ea_one_gv k r')).1
  rw [oneStep, ea_heis0_zero, ea_lev_one, ea_inv_one, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_one] at h
  exact h

theorem rankOne_conjTranspose (k r' : ℕ) (c : ℂ) : (w0 k r' c)ᴴ = w0 k r' c⁻¹ := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [Matrix.conjTranspose_apply, w0, Fin.ext_iff]
  split_ifs <;> first | (exfalso; omega) | (simp; done)

private theorem mulVec_bvec_eq_fun_apply {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (j : Fin m) :
    M *ᵥ bvec j = fun i => M i j := by
  funext i
  show ∑ l, M i l * bvec j l = M i j
  simp [bvec, Pi.single_apply]

private theorem dotProduct_bvec_eq_apply {m : ℕ} (w : Fin m → ℂ) (j : Fin m) : w ⬝ᵥ bvec j = w j := by
  show ∑ i, w i * bvec j i = w j
  simp [bvec, Pi.single_apply]

private theorem e0_apply_eq_ite (k r' : ℕ) (p : Fin (2 * (1 + r') + k + 1)) :
    e0 k r' p = if p.val = 0 then 1 else 0 := by
  simp only [e0, bvec, Pi.single_apply, eI, a0, Fin.ext_iff]

private theorem es0_apply_eq_ite (k r' : ℕ) (p : Fin (2 * (1 + r') + k + 1)) :
    es0 k r' p = if p.val = 2 * (1 + r') + k then 1 else 0 := by
  simp only [es0, bvec, Pi.single_apply, esI, a0, Fin.ext_iff, Nat.sub_zero]

private theorem w0_mul_apply_zero (k r' : ℕ) (c : ℂ) (M : Mat k (1 + r')) (p q : Fin (2 * (1 + r') + k + 1))
    (hp : p.val = 0) : (w0 k r' c * M) p q = (star c)⁻¹ * M ⟨2 * (1 + r') + k, by omega⟩ q := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨2 * (1 + r') + k, by omega⟩ : Fin (2 * (1 + r') + k + 1))]
  · congr 1
    simp only [w0, Fin.ext_iff, and_true, true_and, eq_self_iff_true]
    split_ifs <;> first | rfl | (exfalso; omega)
  · intro l _ hl
    have hl' : l.val ≠ 2 * (1 + r') + k := fun h => hl (Fin.ext h)
    have : w0 k r' c p l = 0 := by
      simp only [w0, Fin.ext_iff, and_true, true_and, eq_self_iff_true]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [this, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

private theorem w0_mul_apply_last (k r' : ℕ) (c : ℂ) (M : Mat k (1 + r')) (p q : Fin (2 * (1 + r') + k + 1))
    (hp : p.val = 2 * (1 + r') + k) : (w0 k r' c * M) p q = c * M ⟨0, by omega⟩ q := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨0, by omega⟩ : Fin (2 * (1 + r') + k + 1))]
  · congr 1
    simp only [w0, Fin.ext_iff, and_true, true_and, eq_self_iff_true]
    split_ifs <;> first | rfl | (exfalso; omega)
  · intro l _ hl
    have hl' : l.val ≠ 0 := fun h => hl (Fin.ext h)
    have : w0 k r' c p l = 0 := by
      simp only [w0, Fin.ext_iff, and_true, true_and, eq_self_iff_true]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [this, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

private theorem w0_mul_apply_of_middle (k r' : ℕ) (c : ℂ) (M : Mat k (1 + r')) (p q : Fin (2 * (1 + r') + k + 1))
    (hp0 : 0 < p.val) (hpN : p.val < 2 * (1 + r') + k) : (w0 k r' c * M) p q = M p q := by
  rw [Matrix.mul_apply, Finset.sum_eq_single p]
  · have : w0 k r' c p p = 1 := by
      simp only [w0, Fin.ext_iff, and_true, true_and, eq_self_iff_true]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [this, one_mul]
  · intro l _ hl
    have hl' : l.val ≠ p.val := fun h => hl (Fin.ext h)
    have : w0 k r' c p l = 0 := by
      simp only [w0, Fin.ext_iff, and_true, true_and, eq_self_iff_true]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [this, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

private theorem weylMatrix_mul_weylMatrix_eq_one (k r' : ℕ) (d c : ℂ) (h1 : (star d)⁻¹ * c = 1) (h2 : d * (star c)⁻¹ = 1) :
    w0 k r' d * w0 k r' c = 1 := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  rw [Matrix.one_apply]
  by_cases hi0 : i.val = 0
  · rw [w0_mul_apply_zero k r' d _ i j hi0]
    simp only [w0, Fin.ext_iff, and_true, true_and, eq_self_iff_true]
    split_ifs <;> first | (exfalso; omega) | exact h1 | (simp; done)
  · by_cases hiN : i.val = 2 * (1 + r') + k
    · rw [w0_mul_apply_last k r' d _ i j hiN]
      simp only [w0, Fin.ext_iff, and_true, true_and, eq_self_iff_true]
      split_ifs <;> first | (exfalso; omega) | exact h2 | (simp; done)
    · rw [w0_mul_apply_of_middle k r' d _ i j (by omega) (by omega)]
      simp only [w0, Fin.ext_iff, and_true, true_and, eq_self_iff_true]
      split_ifs <;> first | (exfalso; omega) | rfl

theorem rankOne_mem_maximalCompact {k r' : ℕ} (hOSM : OneStepMem) {u : ℂ} (hu : ‖u‖ = 1) : w0 k r' u ∈ Kset k (1 + r') := by
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu
    exact zero_ne_one hu
  have hsu : star u * u = 1 := by
    first
      | (rw [Complex.star_def, Complex.conj_mul', hu]; norm_num)
      | (rw [Complex.star_def, RCLike.conj_mul, hu]; norm_num)
      | (rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hu]; norm_num)
  have hsi : star u⁻¹ = (star u)⁻¹ := by
    first
      | exact star_inv' u
      | exact star_inv₀ u
      | simp
  refine ea_k_iff.2 ⟨rankOne_mem_unitary hOSM hu0, ?_⟩
  rw [rankOne_conjTranspose]
  apply weylMatrix_mul_weylMatrix_eq_one
  · rw [hsi, inv_inv, hsu]
  · rw [← mul_inv, mul_comm, hsu, inv_one]

private theorem sum_eq_sum_mp_of_zero_at_edges (k r' : ℕ) (g : Fin (2 * (1 + r') + k + 1) → ℂ)
    (hz : ∀ q : Fin (2 * (1 + r') + k + 1), (q.val = 0 ∨ q.val = 2 * (1 + r') + k) → g q = 0) :
    ∑ q, g q = ∑ j, g (mp k r' j) := by
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (mp k r'))) ?_]
  · rw [Finset.sum_image]
    intro a _ b _ hab
    apply Fin.ext
    have := congrArg Fin.val hab
    simp only [mp] at this
    omega
  · intro q _ hq
    apply hz
    have hql := q.isLt
    by_contra hne
    apply hq
    rw [Finset.mem_image]
    refine ⟨⟨q.val - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    simp only [mp]
    omega

private theorem liftVec_apply_eq_zero_of_edge (k r' : ℕ) (v : Fin (2 * r' + k + 1) → ℂ) (q : Fin (2 * (1 + r') + k + 1))
    (hq : q.val = 0 ∨ q.val = 2 * (1 + r') + k) : liftVec k 1 r' v q = 0 := by
  simp only [liftVec]
  split_ifs with h
  · exfalso; omega
  · rfl

private theorem liftVec_apply_mp (k r' : ℕ) (v : Fin (2 * r' + k + 1) → ℂ) (j : Fin (2 * r' + k + 1)) :
    liftVec k 1 r' v (mp k r' j) = v j := by
  have hj := j.isLt
  simp only [liftVec, mp]
  split_ifs with h
  · first
      | rfl
      | exact congrArg v (Fin.ext (Nat.add_sub_cancel j.val 1))
      | (simp; intro; omega)
  · exfalso; omega

private theorem Hpk_one_add_apply_mp_mp (k r' : ℕ) (i j : Fin (2 * r' + k + 1)) :
    Hpk k (1 + r') (mp k r' i) (mp k r' j) = Hpk k r' i j := by
  have hi := i.isLt
  have hj := j.isLt
  have e1 : (mp k r' i).val = i.val + 1 := rfl
  have e2 : (mp k r' j).val = j.val + 1 := rfl
  simp only [and_true, true_and, Hpk, Fin.ext_iff, e1, e2]
  split_ifs <;> first | rfl | (exfalso; omega) | simp_all

private theorem Hpk_mulVec_liftVec_eq_liftVec_mulVec (k r' : ℕ) (v : Fin (2 * r' + k + 1) → ℂ) :
    Hpk k (1 + r') *ᵥ liftVec k 1 r' v = liftVec k 1 r' (Hpk k r' *ᵥ v) := by
  funext p
  have hpl := p.isLt
  show ∑ q, Hpk k (1 + r') p q * liftVec k 1 r' v q = liftVec k 1 r' (Hpk k r' *ᵥ v) p
  rw [sum_eq_sum_mp_of_zero_at_edges k r' (fun q => Hpk k (1 + r') p q * liftVec k 1 r' v q)
    (fun q hq => by
      show Hpk k (1 + r') p q * liftVec k 1 r' v q = 0
      rw [liftVec_apply_eq_zero_of_edge k r' v q hq, mul_zero])]
  simp only [liftVec_apply_mp]
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · have hpe : p = mp k r' ⟨p.val - 1, by omega⟩ := Fin.ext (by simp only [mp]; omega)
    rw [hpe, liftVec_apply_mp]
    show _ = ∑ j, Hpk k r' _ j * v j
    simp only [Hpk_one_add_apply_mp_mp]
  · have h0 : liftVec k 1 r' (Hpk k r' *ᵥ v) p = 0 := by
      simp only [liftVec]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [h0]
    apply Finset.sum_eq_zero
    intro j _
    have hj := j.isLt
    have : Hpk k (1 + r') p (mp k r' j) = 0 := by
      simp only [Hpk, mp, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [this, zero_mul]

private theorem dotProduct_star_liftVec_liftVec (k r' : ℕ) (y w : Fin (2 * r' + k + 1) → ℂ) :
    star (liftVec k 1 r' y) ⬝ᵥ liftVec k 1 r' w = star y ⬝ᵥ w := by
  show ∑ q, star (liftVec k 1 r' y q) * liftVec k 1 r' w q = ∑ j, star (y j) * w j
  rw [sum_eq_sum_mp_of_zero_at_edges k r' (fun q => star (liftVec k 1 r' y q) * liftVec k 1 r' w q)
    (fun q hq => by
      show star (liftVec k 1 r' y q) * liftVec k 1 r' w q = 0
      rw [liftVec_apply_eq_zero_of_edge k r' w q hq, mul_zero])]
  simp only [liftVec_apply_mp]

private theorem herm_liftVec_liftVec (k r' : ℕ) (v y : Fin (2 * r' + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) (liftVec k 1 r' v) (liftVec k 1 r' y) = herm (Hpk k r') v y := by
  rw [herm, herm, Hpk_mulVec_liftVec_eq_liftVec_mulVec, dotProduct_star_liftVec_liftVec]

private theorem Hpk_mulVec_e0_eq_es0_vec (k r' : ℕ) : Hpk k (1 + r') *ᵥ e0 k r' = es0 k r' := by
  funext p
  have hp := p.isLt
  show ∑ q, Hpk k (1 + r') p q * e0 k r' q = es0 k r' p
  rw [es0_apply_eq_ite, Finset.sum_eq_single (⟨0, by omega⟩ : Fin (2 * (1 + r') + k + 1))]
  · rw [e0_apply_eq_ite]
    simp only [and_true, true_and, Hpk, Fin.ext_iff]
    split_ifs <;> first | rfl | (simp; done) | (exfalso; omega)
  · intro q _ hq
    have hq' : q.val ≠ 0 := fun h => hq (Fin.ext h)
    rw [e0_apply_eq_ite, if_neg hq', mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

private theorem Hpk_mulVec_es0_eq_e0_vec (k r' : ℕ) : Hpk k (1 + r') *ᵥ es0 k r' = e0 k r' := by
  funext p
  have hp := p.isLt
  show ∑ q, Hpk k (1 + r') p q * es0 k r' q = e0 k r' p
  rw [e0_apply_eq_ite, Finset.sum_eq_single (⟨2 * (1 + r') + k, by omega⟩ : Fin (2 * (1 + r') + k + 1))]
  · rw [es0_apply_eq_ite]
    simp only [and_true, true_and, Hpk, Fin.ext_iff]
    split_ifs <;> first | rfl | (simp; done) | (exfalso; omega)
  · intro q _ hq
    have hq' : q.val ≠ 2 * (1 + r') + k := fun h => hq (Fin.ext h)
    rw [es0_apply_eq_ite, if_neg hq', mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

private theorem herm_e0_left_eq_star_apply_last (k r' : ℕ) (w : Fin (2 * (1 + r') + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) (e0 k r') w = star (w ⟨2 * (1 + r') + k, by omega⟩) := by
  rw [herm, Hpk_mulVec_e0_eq_es0_vec, es0, dotProduct_bvec_eq_apply]
  rfl

private theorem herm_es0_left_eq_star_apply_zero (k r' : ℕ) (w : Fin (2 * (1 + r') + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) (es0 k r') w = star (w ⟨0, by omega⟩) := by
  rw [herm, Hpk_mulVec_es0_eq_e0_vec, e0, dotProduct_bvec_eq_apply]
  rfl

private theorem e0_apply_last_eq_zero (k r' : ℕ) : e0 k r' ⟨2 * (1 + r') + k, by omega⟩ = 0 := by
  rw [e0_apply_eq_ite]
  exact if_neg (show ¬(2 * (1 + r') + k = 0) by omega)

private theorem e0_apply_zero_eq_one (k r' : ℕ) : e0 k r' ⟨0, by omega⟩ = 1 := by
  rw [e0_apply_eq_ite]
  exact if_pos rfl

theorem heisenberg_first_basis {k r' : ℕ} (hHA : HeisAct) (x : HPar k r') : heis0 k r' x *ᵥ e0 k r' = e0 k r' := by
  rw [heis0, hHA k r', herm_e0_left_eq_star_apply_last, herm_e0_left_eq_star_apply_last,
    liftVec_apply_eq_zero_of_edge k r' x.1 ⟨2 * (1 + r') + k, by omega⟩ (Or.inr rfl), e0_apply_last_eq_zero]
  simp

theorem heisenberg_last_basis {k r' : ℕ} (hHA : HeisAct) (x : HPar k r') :
    heis0 k r' x *ᵥ es0 k r' = es0 k r' + (liftVec k 1 r' x.1 + hb k r' x.1 x.2 • e0 k r') := by
  rw [heis0, hHA k r', herm_es0_left_eq_star_apply_zero, herm_es0_left_eq_star_apply_zero,
    liftVec_apply_eq_zero_of_edge k r' x.1 ⟨0, by omega⟩ (Or.inl rfl), e0_apply_zero_eq_one]
  simp

theorem ea_heis_lift {k r' : ℕ} (hHA : HeisAct) (x : HPar k r') (v : Fin (2 * r' + k + 1) → ℂ) :
    heis0 k r' x *ᵥ liftVec k 1 r' v = liftVec k 1 r' v - herm (Hpk k r') v x.1 • e0 k r' := by
  have h3 : herm (Hpk k (1 + r')) (liftVec k 1 r' v) (e0 k r') = 0 := by
    rw [herm, Hpk_mulVec_liftVec_eq_liftVec_mulVec]
    show ∑ p, star (e0 k r' p) * liftVec k 1 r' (Hpk k r' *ᵥ v) p = 0
    apply Finset.sum_eq_zero
    intro p _
    rw [e0_apply_eq_ite]
    split_ifs with hp
    · rw [liftVec_apply_eq_zero_of_edge k r' _ p (Or.inl hp), mul_zero]
    · rw [star_zero, zero_mul]
  rw [heis0, hHA k r', herm_liftVec_liftVec, h3]
  simp

theorem last_basis_zero (k r' : ℕ) : es0 k r' 0 = 0 := by
  rw [es0_apply_eq_ite]
  exact if_neg (by first | (rw [Fin.val_zero]; omega) | simp | omega)

theorem first_basis_zero (k r' : ℕ) : e0 k r' 0 = 1 := by
  rw [e0_apply_eq_ite]
  exact if_pos (by first | rfl | simp)

theorem last_basis_middle_zero (k r' : ℕ) (j : Fin (2 * r' + k + 1)) : es0 k r' (mp k r' j) = 0 := by
  have hj := j.isLt
  rw [es0_apply_eq_ite]
  exact if_neg (by simp only [mp]; omega)

theorem first_basis_middle_zero (k r' : ℕ) (j : Fin (2 * r' + k + 1)) : e0 k r' (mp k r' j) = 0 := by
  rw [e0_apply_eq_ite]
  exact if_neg (by simp only [mp]; omega)

theorem ea_phiV_app {k r : ℕ} (b : Fin (r + 1)) (i : Fin (2 * r + k + 1)) :
    phiV k r b i = if b.val < r then (if i.val = 2 * r + k - b.val then 1 else 0) else
      ((Real.sqrt 2)⁻¹ : ℂ) * ((if i.val = r then 1 else 0) + (if i.val = r + k then 1 else 0)) := by
  simp only [phiV]
  by_cases h1 : b.val < r
  · rw [dif_pos h1, if_pos h1]
    simp only [bvec, Pi.single_apply, esI, Fin.ext_iff]
  · rw [dif_neg h1, if_neg h1]
    simp only [epsV, bvec, Pi.smul_apply, Pi.add_apply, smul_eq_mul, Pi.single_apply, wI, Fin.ext_iff,
      Fin.val_zero, Fin.val_last, Nat.add_zero]

theorem ea_phiV'_app {k r : ℕ} (hk : 1 ≤ k) (b : Fin (r + 1)) (i : Fin (2 * r + k + 1)) :
    phiV' k r b i = if b.val < r then (if i.val = b.val then 1 else 0) else
      ((Real.sqrt 2)⁻¹ : ℂ) * ((if i.val = r then 1 else 0) - (if i.val = r + k then 1 else 0)) := by
  simp only [phiV']
  by_cases h1 : b.val < r
  · rw [if_pos h1]
    simp only [phiV]
    rw [dif_pos h1, mulVec_bvec_eq_fun_apply]
    simp only [Hpk, esI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  · rw [if_neg h1]
    simp only [phiV]
    rw [dif_neg h1, epsV, Matrix.mulVec_smul, Matrix.mulVec_add, mulVec_bvec_eq_fun_apply, mulVec_bvec_eq_fun_apply]
    have c1 : Hpk k r i (wI k r 0) = if i.val = r then 1 else 0 := by
      simp only [Hpk, wI, Fin.ext_iff, Fin.val_zero, Nat.add_zero]
      split_ifs <;> first | rfl | (exfalso; omega)
    have c2 : Hpk k r i (wI k r (Fin.last k)) = -(if i.val = r + k then 1 else 0) := by
      simp only [Hpk, wI, Fin.ext_iff, Fin.val_last]
      split_ifs <;> first | rfl | (simp; done) | (exfalso; omega)
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, c1, c2]
    ring

theorem ea_sum_ind {n : ℕ} (j : ℕ) (hj : j < n) : ∑ i : Fin n, (if i.val = j then (1 : ℂ) else 0) = 1 := by
  rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin n)]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Fin.ext h)
  · intro h; exact absurd (Finset.mem_univ _) h

private theorem hpk_sq_lemma (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hi := i.isLt
  have hj := j.isLt
  by_cases hm : r ≤ i.val ∧ i.val ≤ r + k
  · rw [Finset.sum_eq_single i]
    · simp only [and_true, true_and, Hpk, Fin.ext_iff]
      split_ifs <;> first | (exfalso; omega) | (simp; done) | norm_num
    · intro l _ hl
      have hl' : l.val ≠ i.val := fun h => hl (Fin.ext h)
      have : Hpk k r i l = 0 := by
        simp only [and_true, true_and, Hpk, Fin.ext_iff]
        split_ifs <;> first | rfl | (exfalso; omega)
      rw [this, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_single (⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1))]
    · simp only [and_true, true_and, Hpk, Fin.ext_iff]
      split_ifs <;> first | (exfalso; omega) | (simp; done) | norm_num
    · intro l _ hl
      have hl' : l.val ≠ 2 * r + k - i.val := fun h => hl (Fin.ext h)
      have : Hpk k r i l = 0 := by
        simp only [and_true, true_and, Hpk, Fin.ext_iff]
        split_ifs <;> first | rfl | (exfalso; omega)
      rw [this, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

private theorem star_inv_sqrt_two_mul_sum_ite_eq_sub (k r : ℕ) (hk : 1 ≤ k) (i : Fin (2 * r + k + 1)) :
    star (((Real.sqrt 2)⁻¹ : ℂ) * ((if i.val = r then 1 else 0) - (if i.val = r + k then 1 else 0))) *
      (((Real.sqrt 2)⁻¹ : ℂ) * ((if i.val = r then 1 else 0) + (if i.val = r + k then 1 else 0))) =
    star ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) * (if i.val = r then 1 else 0) -
      star ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) * (if i.val = r + k then 1 else 0) := by
  split_ifs <;> first | (exfalso; omega) | (simp; done) | (simp; ring) | ring

theorem ea_phiV'_herm {k r : ℕ} (hk : 1 ≤ k) (a b : Fin (r + 1)) :
    herm (Hpk k r) (phiV' k r a) (phiV' k r b) = 0 := by
  have e : Hpk k r *ᵥ phiV' k r a = phiV k r a := by
    rw [phiV', Matrix.mulVec_mulVec, hpk_sq_lemma, Matrix.one_mulVec]
  rw [herm, e]
  show ∑ i, star (phiV' k r b i) * phiV k r a i = 0
  simp only [ea_phiV'_app hk, ea_phiV_app]
  have ha := a.isLt
  have hb := b.isLt
  by_cases h1 : a.val < r <;> by_cases h2 : b.val < r
  · simp only [if_pos h1, if_pos h2]
    apply Finset.sum_eq_zero
    intro i _
    split_ifs <;> first | (exfalso; omega) | simp
  · simp only [if_pos h1, if_neg h2]
    apply Finset.sum_eq_zero
    intro i _
    split_ifs <;> first | (exfalso; omega) | simp
  · simp only [if_neg h1, if_pos h2]
    apply Finset.sum_eq_zero
    intro i _
    split_ifs <;> first | (exfalso; omega) | simp
  · simp only [if_neg h1, if_neg h2, star_inv_sqrt_two_mul_sum_ite_eq_sub k r hk]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ea_sum_ind (n := 2 * r + k + 1) r (by omega), ea_sum_ind (n := 2 * r + k + 1) (r + k) (by omega), sub_self]

theorem ea_phiV'_li {k r : ℕ} (hk : 1 ≤ k) : LinearIndependent ℂ (phiV' k r) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg b
  have hs : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
  have hc : ((Real.sqrt 2)⁻¹ : ℂ) ≠ 0 := by simp [hs]
  have hbl := b.isLt
  by_cases hb : b.val < r
  · have := congrFun hg ⟨b.val, by omega⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ea_phiV'_app hk, Pi.zero_apply] at this
    rw [Finset.sum_eq_single b] at this
    · split_ifs at this <;> first | (exfalso; omega) | simp_all
    · intro c _ hcb
      have : c.val ≠ b.val := fun h => hcb (Fin.ext h)
      split_ifs <;> first | (exfalso; omega) | simp
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hbr : b.val = r := by omega
    have := congrFun hg ⟨r, by omega⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ea_phiV'_app hk, Pi.zero_apply] at this
    rw [Finset.sum_eq_single b] at this
    · split_ifs at this <;> first | (exfalso; omega) | simp_all
    · intro c _ hcb
      have : c.val ≠ b.val := fun h => hcb (Fin.ext h)
      split_ifs <;> first | (exfalso; omega) | simp
    · intro h; exact absurd (Finset.mem_univ _) h

private theorem lev_apply_eq_ite_of_outer (k r' : ℕ) (g : Mat k r') (p q : Fin (2 * (1 + r') + k + 1))
    (hp : ¬(1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1)) : ιLev k 1 r' g p q = if p = q then 1 else 0 := by
  simp only [ιLev]
  rw [dif_neg hp]

private theorem lev_apply_mp_mp (k r' : ℕ) (g : Mat k r') (i j : Fin (2 * r' + k + 1)) :
    ιLev k 1 r' g (mp k r' i) (mp k r' j) = g i j := by
  have hi := i.isLt
  have hj := j.isLt
  have h1 : 1 ≤ (mp k r' i).val ∧ (mp k r' i).val < 2 * r' + k + 1 + 1 := by simp only [mp]; omega
  have h2 : 1 ≤ (mp k r' j).val ∧ (mp k r' j).val < 2 * r' + k + 1 + 1 := by simp only [mp]; omega
  simp only [ιLev]
  rw [dif_pos h1, dif_pos h2]
  all_goals (congr 1 <;> first | exact Fin.ext (Nat.add_sub_cancel _ 1) | (apply Fin.ext; simp [mp]))

private theorem w0_one_mul_Hpk_eq_lev_Hpk (k r' : ℕ) : w0 k r' 1 * Hpk k (1 + r') = ιLev k 1 r' (Hpk k r') := by
  ext p q
  have hp := p.isLt
  have hq := q.isLt
  by_cases hp0 : p.val = 0
  · rw [w0_mul_apply_zero k r' 1 _ p q hp0, lev_apply_eq_ite_of_outer k r' _ p q (by omega)]
    simp only [and_true, true_and, Hpk, Fin.ext_iff, star_one, inv_one, one_mul]
    split_ifs <;> first | rfl | (exfalso; omega)
  · by_cases hpN : p.val = 2 * (1 + r') + k
    · rw [w0_mul_apply_last k r' 1 _ p q hpN, lev_apply_eq_ite_of_outer k r' _ p q (by omega)]
      simp only [and_true, true_and, Hpk, Fin.ext_iff, one_mul]
      split_ifs <;> first | rfl | (exfalso; omega)
    · rw [w0_mul_apply_of_middle k r' 1 _ p q (by omega) (by omega)]
      by_cases hqm : 1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1
      · obtain ⟨p', rfl⟩ : ∃ p' : Fin (2 * r' + k + 1), p = mp k r' p' :=
          ⟨⟨p.val - 1, by omega⟩, Fin.ext (by simp only [mp]; omega)⟩
        obtain ⟨q', rfl⟩ : ∃ q' : Fin (2 * r' + k + 1), q = mp k r' q' :=
          ⟨⟨q.val - 1, by omega⟩, Fin.ext (by simp only [mp]; omega)⟩
        rw [lev_apply_mp_mp, Hpk_one_add_apply_mp_mp]
      · simp only [ιLev, Hpk, Fin.ext_iff]
        split_ifs <;> first | rfl | (exfalso; omega)

theorem phi_embedded_eq_rankOne (k r' : ℕ) (a : Fin (1 + r' + 1)) : phi2 k r' a = w0 k r' 1 *ᵥ phiV' k (1 + r') a := by
  rw [phi2, phiV', Matrix.mulVec_mulVec, w0_one_mul_Hpk_eq_lev_Hpk]

theorem ea_yx (k r' : ℕ) (x : HPar k r') (a : Fin (1 + r' + 1)) :
    Yx k r' x a = ((heis0 k r' x)⁻¹ * w0 k r' 1) *ᵥ phiV' k (1 + r') a := by
  rw [Yx, phi_embedded_eq_rankOne, Matrix.mulVec_mulVec]

theorem ea_hinv_gv {k r' : ℕ} (hHI : HeisInv) (hHM : HeisMem) (x : HPar k r') :
    (heis0 k r' x)⁻¹ ∈ GV k (1 + r') := by
  rw [hHI k r' x]
  exact (hHM k r' (-x.1, -x.2)).1

private theorem herm_mulVec_mulVec_of_mem_GV {k r : ℕ} {M : Mat k r} (hM : M ∈ GV k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (M *ᵥ v) (M *ᵥ w) = herm (Hpk k r) v w := by
  have h : Mᴴ * Hpk k r * M = Hpk k r := hM
  rw [herm, herm, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, h]

theorem ea_yx_iso {k r' : ℕ} (hk : 1 ≤ k) (hHI : HeisInv) (hHM : HeisMem) (hOSM : OneStepMem) (x : HPar k r')
    (a b : Fin (1 + r' + 1)) : herm (Hpk k (1 + r')) (Yx k r' x a) (Yx k r' x b) = 0 := by
  rw [ea_yx, ea_yx,
    herm_mulVec_mulVec_of_mem_GV (ea_gv_mul (ea_hinv_gv hHI hHM x) (rankOne_mem_unitary hOSM (one_ne_zero : (1 : ℂ) ≠ 0)))]
  exact ea_phiV'_herm (r := 1 + r') hk a b

private theorem eq_zero_of_mulVec_eq_zero_of_mem_GV {k r : ℕ} {M : Mat k r} (hM : M ∈ GV k r) (u : Fin (2 * r + k + 1) → ℂ)
    (hu : M *ᵥ u = 0) : u = 0 := by
  have h : Mᴴ * Hpk k r * M = Hpk k r := hM
  have e : Hpk k r *ᵥ u = 0 := by
    rw [← h, ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_zero]
  have e2 : u = (Hpk k r * Hpk k r) *ᵥ u := by rw [hpk_sq_lemma, Matrix.one_mulVec]
  rw [e2, ← Matrix.mulVec_mulVec, e, Matrix.mulVec_zero]

theorem ea_yx_li {k r' : ℕ} (hk : 1 ≤ k) (hHI : HeisInv) (hHM : HeisMem) (hOSM : OneStepMem) (x : HPar k r') :
    LinearIndependent ℂ (Yx k r' x) := by
  have hM : ((heis0 k r' x)⁻¹ * w0 k r' 1) ∈ GV k (1 + r') :=
    ea_gv_mul (ea_hinv_gv hHI hHM x) (rankOne_mem_unitary hOSM (one_ne_zero : (1 : ℂ) ≠ 0))
  have hli := ea_phiV'_li (k := k) (r := 1 + r') hk
  have e : Yx k r' x = fun a => ((heis0 k r' x)⁻¹ * w0 k r' 1) *ᵥ phiV' k (1 + r') a :=
    funext (ea_yx k r' x)
  rw [e]
  exact hli.map' (Matrix.mulVecLin _) (LinearMap.ker_eq_bot'.2 (eq_zero_of_mulVec_eq_zero_of_mem_GV hM))

end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
