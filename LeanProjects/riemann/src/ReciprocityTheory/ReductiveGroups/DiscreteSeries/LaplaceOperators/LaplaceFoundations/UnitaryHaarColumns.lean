import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.StandardBasisEmbedding

open Formalism.QuantumDeterminants

variable {k r : ℕ}

def bl (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val < r + k

instance (i : Fin (2 * r + k + 1)) : Decidable (bl k r i) := by unfold bl; infer_instance

def eB (k r : ℕ) (q : Fin k) : Fin (2 * r + k + 1) := ⟨r + q.val, by omega⟩

private theorem eB_val_eq_add (q : Fin k) : (eB k r q).val = r + q.val := rfl

theorem eB_inj : Function.Injective (eB k r) := by
  intro a b hab
  have h1 := congrArg Fin.val hab
  rw [eB_val_eq_add, eB_val_eq_add] at h1
  exact Fin.ext (by omega)

theorem bl_eB (q : Fin k) : bl k r (eB k r q) := by
  have := q.isLt
  show r ≤ (eB k r q).val ∧ (eB k r q).val < r + k
  rw [eB_val_eq_add]
  omega

theorem ex_eB {i : Fin (2 * r + k + 1)} (hi : bl k r i) : ∃ q, i = eB k r q := by
  have hi' : r ≤ i.val ∧ i.val < r + k := hi
  refine ⟨⟨i.val - r, by omega⟩, Fin.ext ?_⟩
  rw [eB_val_eq_add]
  show i.val = r + (i.val - r)
  omega

theorem sumB (f : Fin (2 * r + k + 1) → ℂ) (hf : ∀ p, ¬ bl k r p → f p = 0) :
    ∑ p, f p = ∑ q : Fin k, f (eB k r q) := by
  rw [← Finset.sum_image (s := Finset.univ) (g := eB k r) (by intro a _ b _ hab; exact eB_inj hab)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro p _ hp
  apply hf
  intro hb
  obtain ⟨q, rfl⟩ := ex_eB hb
  exact hp (Finset.mem_image_of_mem _ (Finset.mem_univ _))

private theorem blockW_apply_of_bl (h : Matrix (Fin k) (Fin k) ℂ) {i j : Fin (2 * r + k + 1)}
    (hi : bl k r i) (hj : bl k r j) :
    Formalism.MainNotions.S.blockW k r h i j =
      h ⟨i.val - r, by unfold bl at hi; omega⟩ ⟨j.val - r, by unfold bl at hj; omega⟩ := by
  have hi' : r ≤ i.val ∧ i.val < r + k := hi
  have hj' : r ≤ j.val ∧ j.val < r + k := hj
  simp only [Formalism.MainNotions.S.blockW, dif_pos hi', dif_pos hj']

theorem bw_ee (h : Matrix (Fin k) (Fin k) ℂ) (q q' : Fin k) :
    Formalism.MainNotions.S.blockW k r h (eB k r q) (eB k r q') = h q q' := by
  rw [blockW_apply_of_bl h (bl_eB q) (bl_eB q')]
  have e : ∀ (a : Fin k) (ha : (eB k r a).val - r < k), (⟨(eB k r a).val - r, ha⟩ : Fin k) = a :=
    fun a _ => Fin.ext (by show r + a.val - r = a.val; omega)
  rw [e, e]

theorem bw_col (h : Matrix (Fin k) (Fin k) ℂ) (i : Fin (2 * r + k + 1)) {j : Fin (2 * r + k + 1)}
    (hj : ¬ bl k r j) : Formalism.MainNotions.S.blockW k r h i j = if i = j then 1 else 0 := by
  have hj' : ¬ (r ≤ j.val ∧ j.val < r + k) := hj
  by_cases hi : r ≤ i.val ∧ i.val < r + k
  · have hne : i ≠ j := by
      intro e
      subst e
      exact hj' hi
    simp only [Formalism.MainNotions.S.blockW, dif_pos hi, dif_neg hj', if_neg hne]
  · simp only [Formalism.MainNotions.S.blockW, dif_neg hi]

theorem bw_row (h : Matrix (Fin k) (Fin k) ℂ) {i : Fin (2 * r + k + 1)} (j : Fin (2 * r + k + 1))
    (hi : ¬ bl k r i) : Formalism.MainNotions.S.blockW k r h i j = if i = j then 1 else 0 := by
  have hi' : ¬ (r ≤ i.val ∧ i.val < r + k) := hi
  simp only [Formalism.MainNotions.S.blockW, dif_neg hi']

theorem bw_off (h : Matrix (Fin k) (Fin k) ℂ) {i j : Fin (2 * r + k + 1)}
    (hi : ¬ bl k r i) (hj : bl k r j) : Formalism.MainNotions.S.blockW k r h i j = 0 := by
  have hi' : ¬ (r ≤ i.val ∧ i.val < r + k) := hi
  have hne : i ≠ j := by
    intro e
    subst e
    exact hi hj
  simp only [Formalism.MainNotions.S.blockW, dif_neg hi', if_neg hne]

theorem bw_off' (h : Matrix (Fin k) (Fin k) ℂ) {i j : Fin (2 * r + k + 1)}
    (hi : bl k r i) (hj : ¬ bl k r j) : Formalism.MainNotions.S.blockW k r h i j = 0 := by
  have hi' : r ≤ i.val ∧ i.val < r + k := hi
  have hj' : ¬ (r ≤ j.val ∧ j.val < r + k) := hj
  simp only [Formalism.MainNotions.S.blockW, dif_pos hi', dif_neg hj']

theorem blockW_mul (a b : Matrix (Fin k) (Fin k) ℂ) :
    Formalism.MainNotions.S.blockW k r (a * b) = Formalism.MainNotions.S.blockW k r a * Formalism.MainNotions.S.blockW k r b := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : bl k r i
  · by_cases hj : bl k r j
    · obtain ⟨qi, rfl⟩ := ex_eB hi
      obtain ⟨qj, rfl⟩ := ex_eB hj
      rw [bw_ee, Matrix.mul_apply,
        sumB (fun p => Formalism.MainNotions.S.blockW k r a (eB k r qi) p * Formalism.MainNotions.S.blockW k r b p (eB k r qj))
          (fun p hp => by rw [bw_off' a (bl_eB qi) hp, zero_mul])]
      simp only [bw_ee]
    · simp only [fun l => bw_col b l hj, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte, bw_off' a hi hj, bw_off' (a * b) hi hj]
  · rw [bw_row _ j hi]
    simp only [fun l => bw_row a l hi, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte, bw_row b j hi]

theorem blockW_one : Formalism.MainNotions.S.blockW k r (1 : Matrix (Fin k) (Fin k) ℂ) = 1 := by
  ext i j
  rw [Matrix.one_apply]
  by_cases hi : bl k r i
  · by_cases hj : bl k r j
    · obtain ⟨qi, rfl⟩ := ex_eB hi
      obtain ⟨qj, rfl⟩ := ex_eB hj
      rw [bw_ee, Matrix.one_apply]
      simp only [eB_inj.eq_iff]
    · have hne : i ≠ j := by
        intro e
        subst e
        exact hj hi
      rw [bw_off' _ hi hj, if_neg hne]
  · exact bw_row _ j hi

theorem blockW_conjTranspose (h : Matrix (Fin k) (Fin k) ℂ) :
    (Formalism.MainNotions.S.blockW k r h)ᴴ = Formalism.MainNotions.S.blockW k r hᴴ := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  by_cases hi : bl k r i <;> by_cases hj : bl k r j
  · obtain ⟨qi, rfl⟩ := ex_eB hi
    obtain ⟨qj, rfl⟩ := ex_eB hj
    rw [bw_ee, bw_ee, Matrix.conjTranspose_apply]
  · rw [bw_off h hj hi, bw_off' _ hi hj, star_zero]
  · rw [bw_off' h hj hi, bw_off _ hi hj, star_zero]
  · rw [bw_row h i hj, bw_row _ j hi]
    by_cases e : i = j
    · subst e
      simp
    · rw [if_neg (Ne.symm e), if_neg e, star_zero]

theorem H_blrow {i : Fin (2 * r + k + 1)} (hi : bl k r i) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if i = j then 1 else 0 := by
  have hi' : r ≤ i.val ∧ i.val < r + k := hi
  simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem H_blcol {j : Fin (2 * r + k + 1)} (hj : bl k r j) (i : Fin (2 * r + k + 1)) :
    Hpk k r i j = if i = j then 1 else 0 := by
  have hj' : r ≤ j.val ∧ j.val < r + k := hj
  simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem H_lo {c : Fin (2 * r + k + 1)} (hc : c.val < r) (b : Fin (2 * r + k + 1)) :
    Hpk k r c b = if c.val + b.val = 2 * r + k then 1 else 0 := by
  have := b.isLt
  simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem H_hi {c : Fin (2 * r + k + 1)} (hc : r + k < c.val) (b : Fin (2 * r + k + 1)) :
    Hpk k r c b = if c.val + b.val = 2 * r + k then 1 else 0 := by
  have := b.isLt
  simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem H_mid {c : Fin (2 * r + k + 1)} (hc : c.val = r + k) (b : Fin (2 * r + k + 1)) :
    Hpk k r c b = if c = b then -1 else 0 := by
  have := b.isLt
  simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem H_comm (h : Matrix (Fin k) (Fin k) ℂ) :
    Hpk k r * Formalism.MainNotions.S.blockW k r h = Formalism.MainNotions.S.blockW k r h * Hpk k r := by
  ext c d
  rw [Matrix.mul_apply, Matrix.mul_apply]
  by_cases hc : bl k r c
  · simp only [H_blrow hc, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    by_cases hd : bl k r d
    · simp only [H_blcol hd, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    · rw [bw_off' h hc hd]
      symm
      apply Finset.sum_eq_zero
      intro l _
      by_cases hl : bl k r l
      · have hne : l ≠ d := by
          intro e
          subst e
          exact hd hl
        rw [H_blrow hl d, if_neg hne, mul_zero]
      · rw [bw_off' h hc hl, zero_mul]
  · simp only [fun l => bw_row h l hc, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ↓reduceIte]
    by_cases hd : bl k r d
    · have hne : c ≠ d := by
        intro e
        subst e
        exact hc hd
      rw [H_blcol hd c, if_neg hne]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hl : bl k r l
      · have hne' : c ≠ l := by
          intro e
          subst e
          exact hc hl
        rw [H_blcol hl c, if_neg hne', zero_mul]
      · rw [bw_off h hl hd, mul_zero]
    · simp only [fun l => bw_col h l hd, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte]

theorem bw_mulVec {c : Fin (2 * r + k + 1)} (hc : ¬ bl k r c) (h : Matrix (Fin k) (Fin k) ℂ) :
    Formalism.MainNotions.S.blockW k r h *ᵥ bvec c = bvec c := by
  funext i
  simp only [Formalism.QuantumDeterminants.bvec, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  exact bw_col h i hc

theorem mem_UW {h : Matrix (Fin k) (Fin k) ℂ} (hu : h ∈ Matrix.unitaryGroup (Fin k) ℂ) :
    Formalism.MainNotions.S.blockW k r h ∈ UWset k r (z0 k r) := by
  have hs : hᴴ * h = 1 := by
    have hs' : star h * h = 1 := by
      first
        | exact Matrix.mem_unitaryGroup_iff'.mp hu
        | exact Unitary.star_mul_self_of_mem hu
        | exact hu.1
    rwa [Matrix.star_eq_conjTranspose] at hs'
  simp only [Formalism.QuantumDeterminants.UWset, Set.mem_setOf_eq]
  refine ⟨?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · show (Formalism.MainNotions.S.blockW k r h)ᴴ * Hpk k r * Formalism.MainNotions.S.blockW k r h = Hpk k r
    rw [blockW_conjTranspose, Matrix.mul_assoc, H_comm, ← Matrix.mul_assoc, ← blockW_mul, hs,
      blockW_one, Matrix.one_mul]
  · apply bw_mulVec
    have := a.isLt
    show ¬ (r ≤ a.val ∧ a.val < r + k)
    omega
  · apply bw_mulVec
    have := a.isLt
    show ¬ (r ≤ 2 * r + k - a.val ∧ 2 * r + k - a.val < r + k)
    omega
  · show Formalism.MainNotions.S.blockW k r h *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI k r (Fin.last k)) =
      Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI k r (Fin.last k))
    apply bw_mulVec
    show ¬ (r ≤ r + k ∧ r + k < r + k)
    omega

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.StandardBasisEmbedding
