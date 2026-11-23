import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.DelFormula

noncomputable section

open Matrix MeasureTheory
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace FormulaFAux

theorem shear_mp {n : ℕ} (i j : Fin (n + 1)) (hij : i ≠ j) (c : ℂ) :
    MeasurePreserving (fun y : Fin (n + 1) → ℂ => Function.update y i (y i + c * y j)) volume volume := by
  obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hij.symm
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) i
  have he : MeasurePreserving e volume ((volume : Measure ℂ).prod (volume : Measure (Fin n → ℂ))) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure ℂ)) i
  have h1 : MeasurePreserving (fun p : (Fin n → ℂ) × ℂ => (p.1, p.2 + c * p.1 j'))
      ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ))
      ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ)) := by
    refine (MeasurePreserving.id (volume : Measure (Fin n → ℂ))).skew_product
      (g := fun x a => a + c * x j') ?_ ?_
    · exact measurable_snd.add (measurable_const.mul ((measurable_pi_apply j').comp measurable_fst))
    · exact Filter.Eventually.of_forall fun x => map_add_right_eq_self (volume : Measure ℂ) (c * x j')
  have hS : MeasurePreserving (fun p : ℂ × (Fin n → ℂ) => (p.1 + c * p.2 j', p.2))
      ((volume : Measure ℂ).prod (volume : Measure (Fin n → ℂ)))
      ((volume : Measure ℂ).prod (volume : Measure (Fin n → ℂ))) :=
    (Measure.measurePreserving_swap).comp (h1.comp Measure.measurePreserving_swap)
  have key : (fun y : Fin (n + 1) → ℂ => Function.update y i (y i + c * y j)) =
      e.symm ∘ (fun p : ℂ × (Fin n → ℂ) => (p.1 + c * p.2 j', p.2)) ∘ e := by
    funext y
    apply e.injective
    rw [Function.comp_apply, MeasurableEquiv.apply_symm_apply]
    refine Prod.ext ?_ ?_
    · show Function.update y i (y i + c * y j) i = y i + c * y (i.succAbove j')
      rw [hj']
      simp
    · funext m
      show Function.update y i (y i + c * y j) (i.succAbove m) = y (i.succAbove m)
      simp [Function.update_apply, Fin.succAbove_ne]
  rw [key]
  exact (MeasurePreserving.symm e he).comp (hS.comp he)

theorem fne {n : ℕ} (a b : Fin n) (h : a.val ≠ b.val) : a ≠ b := fun e => h (congrArg Fin.val e)

theorem w_ne (k r' : ℕ) (hk : 1 ≤ k) : wI k r' 0 ≠ wI k r' (Fin.last k) := by
  intro h
  have h' := congrArg Fin.val h
  simp [wI, Fin.last] at h'
  omega

def rotF (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) : Fin (2 * r' + k + 1) → ℂ :=
  Function.update (Function.update y (wI k r' 0) (cc * (y (wI k r' 0) - y (wI k r' (Fin.last k)))))
    (wI k r' (Fin.last k)) (cc * (y (wI k r' 0) + y (wI k r' (Fin.last k))))

private lemma measurePreserving_update_update_cc_rotation_of_ne {N : ℕ} (a b : Fin (N + 1)) (hne : a ≠ b) :
    MeasurePreserving (fun y : Fin (N + 1) → ℂ =>
      Function.update (Function.update y a (cc * (y a - y b))) b (cc * (y a + y b))) volume volume := by
  obtain ⟨q, hqdef⟩ : ∃ q : ℂ, q = ((Real.sqrt 2 : ℝ) : ℂ) := ⟨_, rfl⟩
  have hq : q ^ 2 = 2 := by
    rw [hqdef, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hq0 : q ≠ 0 := by
    intro h
    rw [h] at hq
    norm_num at hq
  have hcc : cc = q / 2 := by
    have hinv : cc = q⁻¹ := by
      rw [hqdef]
    rw [hinv, eq_div_iff two_ne_zero, ← hq, pow_two, ← mul_assoc, inv_mul_cancel₀ hq0, one_mul]
  have key : (fun y : Fin (N + 1) → ℂ =>
      Function.update (Function.update y a (cc * (y a - y b))) b (cc * (y a + y b))) =
      (fun y : Fin (N + 1) → ℂ => Function.update y a (y a + -(q - 1) * y b)) ∘
      ((fun y : Fin (N + 1) → ℂ => Function.update y b (y b + q / 2 * y a)) ∘
      (fun y : Fin (N + 1) → ℂ => Function.update y a (y a + -(q - 1) * y b))) := by
    funext y m
    by_cases hma : m = a
    · simp [Function.update_apply, hma, hne, hne.symm, hcc]
      linear_combination (y a - (q - 2) * y b) / 2 * hq
    · by_cases hmb : m = b
      · simp [Function.update_apply, hmb, hne, hne.symm, hcc]
        linear_combination y b / 2 * hq
      · simp [Function.update_apply, hma, hmb]
  rw [key]
  exact (shear_mp a b hne _).comp ((shear_mp b a hne.symm _).comp (shear_mp a b hne _))

theorem rot_mp (k r' : ℕ) (hk : 1 ≤ k) : MeasurePreserving (rotF k r') volume volume := by
  exact measurePreserving_update_update_cc_rotation_of_ne (wI k r' 0) (wI k r' (Fin.last k)) (w_ne k r' hk)

def ix2 (k r' : ℕ) : Fin (1 + r') ⊕ (Fin (1 + r') ⊕ Fin (k - 1)) → Fin (2 * r' + k + 1)
  | Sum.inl t => ⟨t.val, by omega⟩
  | Sum.inr (Sum.inl t) => ⟨2 * r' + k - t.val, by omega⟩
  | Sum.inr (Sum.inr i) => ⟨r' + i.val + 1, by omega⟩

theorem index_embedding_bijective (k r' : ℕ) (hk : 1 ≤ k) : Function.Bijective (ix2 k r') := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · rintro (a | a | a) (b | b | b) h <;>
      (have := a.isLt; have := b.isLt; simp [ix2, Fin.ext_iff] at h ⊢ <;> omega)
  · simp only [Fintype.card_sum, Fintype.card_fin]
    omega

def permF (k r' : ℕ) (z : Fin (2 * r' + k + 1) → ℂ) : (Fin (1 + r') → ℂ) × (Fin (1 + r') → ℂ) × (Fin (k - 1) → ℂ) :=
  (fun j => z (ix2 k r' (Sum.inl j)), fun j => z (ix2 k r' (Sum.inr (Sum.inl j))),
    fun i => z (ix2 k r' (Sum.inr (Sum.inr i))))

theorem perm_mp (k r' : ℕ) (hk : 1 ≤ k) : MeasurePreserving (permF k r') volume volume := by
  let E := Equiv.ofBijective (ix2 k r') (index_embedding_bijective k r' hk)
  have h1 := MeasurePreserving.symm _
    (measurePreserving_piCongrLeft (fun _ : Fin (2 * r' + k + 1) => (volume : Measure ℂ)) E)
  have h2 := measurePreserving_sumPiEquivProdPi
    (fun _ : Fin (1 + r') ⊕ (Fin (1 + r') ⊕ Fin (k - 1)) => (volume : Measure ℂ))
  have h3 := measurePreserving_sumPiEquivProdPi (fun _ : Fin (1 + r') ⊕ Fin (k - 1) => (volume : Measure ℂ))
  have h4 := (MeasurePreserving.id (volume : Measure (Fin (1 + r') → ℂ))).prod h3
  have h5 := h4.comp (h2.comp h1)
  first
    | exact h5
    | (convert h5 using 1; funext z; rfl)

theorem lin_eq (k r' : ℕ) (hk : 1 ≤ k) (y : Fin (2 * r' + k + 1) → ℂ) :
    permF k r' (rotF k r' y) = ((hcoord k r' (y, 0)).1, (hcoord k r' (y, 0)).2.1, (hcoord k r' (y, 0)).2.2.1) := by
  have hne := w_ne k r' hk
  refine Prod.ext (funext fun j => ?_) (Prod.ext (funext fun j => ?_) (funext fun i => ?_))
  · have := j.isLt
    show rotF k r' y ⟨j.val, by omega⟩ = (hcoord k r' (y, 0)).1 j
    rw [hc1 k r' hk, AN, dif_pos (by omega), aF]
    split_ifs with hj
    · have hj' : j.val < r' := hj
      have n1 : (⟨j.val, by omega⟩ : Fin (2 * r' + k + 1)) ≠ wI k r' (Fin.last k) :=
        fne _ _ (by simp only [wI, Fin.val_last]; omega)
      have n0 : (⟨j.val, by omega⟩ : Fin (2 * r' + k + 1)) ≠ wI k r' 0 :=
        fne _ _ (by simp only [wI, Fin.val_zero]; omega)
      rw [rotF, Function.update_of_ne n1, Function.update_of_ne n0]
      try rfl
    · have hj' : ¬ j.val < r' := hj
      have e : (⟨j.val, by omega⟩ : Fin (2 * r' + k + 1)) = wI k r' 0 :=
        Fin.ext (by simp only [wI, Fin.val_zero]; omega)
      rw [e, rotF, Function.update_of_ne hne, Function.update_self]
  · have := j.isLt
    show rotF k r' y ⟨2 * r' + k - j.val, by omega⟩ = (hcoord k r' (y, 0)).2.1 j
    rw [hc2, AN', dif_pos (by omega), aF']
    split_ifs with hj
    · have hj' : j.val < r' := hj
      have n1 : (⟨2 * r' + k - j.val, by omega⟩ : Fin (2 * r' + k + 1)) ≠ wI k r' (Fin.last k) :=
        fne _ _ (by simp only [wI, Fin.val_last]; omega)
      have n0 : (⟨2 * r' + k - j.val, by omega⟩ : Fin (2 * r' + k + 1)) ≠ wI k r' 0 :=
        fne _ _ (by simp only [wI, Fin.val_zero]; omega)
      rw [rotF, Function.update_of_ne n1, Function.update_of_ne n0]
      try rfl
    · have hj' : ¬ j.val < r' := hj
      have e : (⟨2 * r' + k - j.val, by omega⟩ : Fin (2 * r' + k + 1)) = wI k r' (Fin.last k) :=
        Fin.ext (by simp only [wI, Fin.val_last]; omega)
      rw [e, rotF, Function.update_self]
  · have := i.isLt
    show rotF k r' y ⟨r' + i.val + 1, by omega⟩ = (hcoord k r' (y, 0)).2.2.1 i
    have n1 : (⟨r' + i.val + 1, by omega⟩ : Fin (2 * r' + k + 1)) ≠ wI k r' (Fin.last k) :=
      fne _ _ (by simp only [wI, Fin.val_last]; omega)
    have n0 : (⟨r' + i.val + 1, by omega⟩ : Fin (2 * r' + k + 1)) ≠ wI k r' 0 :=
      fne _ _ (by simp only [wI, Fin.val_zero]; omega)
    rw [rotF, Function.update_of_ne n1, Function.update_of_ne n0]
    try rfl

def imF (k r' : ℕ) (q : (Fin (1 + r') → ℂ) × (Fin (1 + r') → ℂ) × (Fin (k - 1) → ℂ)) : ℝ :=
  (∑ j, q.2.1 j * star (q.1 j)).im

theorem imF_meas (k r' : ℕ) : Measurable (imF k r') := by
  apply Continuous.measurable
  unfold imF
  fun_prop

theorem hcoord_mp (k r' : ℕ) (hk : 1 ≤ k) : MeasurePreserving (hcoord k r') volume volume := by
  have hL : MeasurePreserving (fun y => permF k r' (rotF k r' y)) volume volume :=
    (perm_mp k r' hk).comp (rot_mp k r' hk)
  have hP := hL.prod (MeasurePreserving.id (volume : Measure ℝ))
  have hSk : MeasurePreserving
      (fun z : ((Fin (1 + r') → ℂ) × (Fin (1 + r') → ℂ) × (Fin (k - 1) → ℂ)) × ℝ =>
        (z.1, z.2 + imF k r' z.1)) volume volume := by
    refine (MeasurePreserving.id
      (volume : Measure ((Fin (1 + r') → ℂ) × (Fin (1 + r') → ℂ) × (Fin (k - 1) → ℂ)))).skew_product
      (g := fun q t => t + imF k r' q) ?_ ?_
    · exact measurable_snd.add ((imF_meas k r').comp measurable_fst)
    · exact Filter.Eventually.of_forall fun q => map_add_right_eq_self (volume : Measure ℝ) (imF k r' q)
  have hA1 := measurePreserving_prodAssoc (volume : Measure (Fin (1 + r') → ℂ))
    (volume : Measure ((Fin (1 + r') → ℂ) × (Fin (k - 1) → ℂ))) (volume : Measure ℝ)
  have hA2 := measurePreserving_prodAssoc (volume : Measure (Fin (1 + r') → ℂ))
    (volume : Measure (Fin (k - 1) → ℂ)) (volume : Measure ℝ)
  have hA3 := (MeasurePreserving.id (volume : Measure (Fin (1 + r') → ℂ))).prod hA2
  have hAll := hA3.comp (hA1.comp (hSk.comp hP))
  have key : hcoord k r' = fun x : HPar k r' =>
      ((permF k r' (rotF k r' x.1)).1, (permF k r' (rotF k r' x.1)).2.1,
        (permF k r' (rotF k r' x.1)).2.2, x.2 + imF k r' (permF k r' (rotF k r' x.1))) := by
    funext x
    obtain ⟨y, t⟩ := x
    dsimp only
    rw [lin_eq k r' hk y]
    rfl
  rw [key]
  exact hAll

theorem formulaF_all : FormulaF := fun k r' hk => ⟨fun x l => del_formula k r' hk x l, hcoord_mp k r' hk⟩

end FormulaFAux

end ReciprocityTheory.ChartRestriction.DS.Xi
