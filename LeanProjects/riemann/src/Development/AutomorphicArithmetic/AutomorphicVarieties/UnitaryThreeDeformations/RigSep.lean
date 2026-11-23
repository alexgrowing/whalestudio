import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostNumber
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems

open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia

private theorem norm_det_lt_one_of_norm_le_one_of_norm_apply_lt_one {K : Type*} [NormedField K] [IsUltrametricDist K] {n : Type*} [Fintype n]
    [DecidableEq n] (A : Matrix n n K) (a : n) (h1 : ∀ i j, ‖A i j‖ ≤ 1) (h2 : ∀ j, ‖A a j‖ < 1) :
    ‖A.det‖ < 1 := by
  rw [Matrix.det_apply']
  obtain ⟨σ, -, hσ⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
    (Finset.univ_nonempty (α := Equiv.Perm n))
    (fun τ : Equiv.Perm n => (((Equiv.Perm.sign τ : ℤ) : K)) * ∏ i, A (τ i) i)
  refine lt_of_le_of_lt hσ ?_
  show ‖(((Equiv.Perm.sign σ : ℤ) : K)) * ∏ i, A (σ i) i‖ < 1
  have hs : ‖(((Equiv.Perm.sign σ : ℤ) : K))‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [norm_mul, hs, one_mul, norm_prod,
    ← Finset.mul_prod_erase Finset.univ (fun i => ‖A (σ i) i‖) (Finset.mem_univ (σ.symm a))]
  have hle : ∏ i ∈ Finset.univ.erase (σ.symm a), ‖A (σ i) i‖ ≤ 1 :=
    Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => h1 _ _)
  have hlt : ‖A (σ (σ.symm a)) (σ.symm a)‖ < 1 := by
    rw [Equiv.apply_symm_apply]
    exact h2 _
  calc ‖A (σ (σ.symm a)) (σ.symm a)‖ * ∏ i ∈ Finset.univ.erase (σ.symm a), ‖A (σ i) i‖
      ≤ ‖A (σ (σ.symm a)) (σ.symm a)‖ * 1 := mul_le_mul_of_nonneg_left hle (norm_nonneg _)
    _ < 1 := by simpa using hlt

private theorem norm_le_one_of_det_smul_one_sub_eq_zero {K : Type*} [NormedField K] [IsUltrametricDist K] {n : Type*} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) (h1 : ∀ i j, ‖M i j‖ ≤ 1) (t : K)
    (ht : (t • (1 : Matrix n n K) - M).det = 0) : ‖t‖ ≤ 1 := by
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr ht
  rcases isEmpty_or_nonempty n with hn | hn
  · exact absurd (funext fun c => (IsEmpty.false c).elim) hv0
  obtain ⟨b, hb⟩ := Finite.exists_max (fun c => ‖v c‖)
  have hvb : v b ≠ 0 := by
    intro h0
    apply hv0
    funext c
    have := hb c
    rw [h0, norm_zero] at this
    exact norm_le_zero_iff.mp this
  have hrow : t * v b = ∑ c, M b c * v c := by
    have := congrFun hv b
    simp [Matrix.sub_mulVec, Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.one_apply,
      sub_mul, Finset.sum_sub_distrib, ite_mul, Finset.sum_ite_eq] at this
    linear_combination this
  have hbound : ‖t * v b‖ ≤ 1 * ‖v b‖ := by
    rw [hrow]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) (fun c _ => ?_)
    rw [norm_mul]
    exact mul_le_mul (h1 b c) (hb c) (norm_nonneg _) zero_le_one
  rw [norm_mul] at hbound
  exact le_of_mul_le_mul_right hbound (norm_pos_iff.mpr hvb)

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.UnitaryThreeInertia.rig_sep :
    ∀ {l : ℕ} [Fact l.Prime] (M : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) (d : Fin 3 → PadicAlgCl l) (P : GL (Fin 3) (PadicAlgCl l)), (∀ a b, ‖M a b - Matrix.diagonal d a b‖ < 1) → (∀ a, ‖d a‖ = 1) → (∀ a b, a ≠ b → ‖d a - d b‖ = 1) → (∀ i j, j < i → (((P⁻¹ : GL (Fin 3) (PadicAlgCl l)) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) * M * (P : Matrix (Fin 3) (Fin 3) (PadicAlgCl l))) i j = 0) → ∀ i j, i ≠ j → ∀ u : PadicAlgCl l, ‖u - 1‖ < 1 → (((P⁻¹ : GL (Fin 3) (PadicAlgCl l)) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) * M * (P : Matrix (Fin 3) (Fin 3) (PadicAlgCl l))) i i ≠ (((P⁻¹ : GL (Fin 3) (PadicAlgCl l)) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) * M * (P : Matrix (Fin 3) (Fin 3) (PadicAlgCl l))) j j * u := by
  intro l _ M d P hM hd hdd hT i j hij u hu
  set T := ((P⁻¹ : GL (Fin 3) (PadicAlgCl l)) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) * M *
    (P : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) with hTdef
  have hsub : ∀ x y : PadicAlgCl l, ‖x - y‖ ≤ max ‖x‖ ‖y‖ := fun x y => by
    simpa [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max x (-y)
  have hdet : ∀ x : PadicAlgCl l, (x • (1 : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) - M).det =
      ∏ k, (x - T k k) := by
    intro x
    have h1 : ((P⁻¹ : GL (Fin 3) (PadicAlgCl l)) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) *
        (x • 1 - M) * (P : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) = x • 1 - T := by
      rw [hTdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        Units.inv_mul]
    have h2 : (((P⁻¹ : GL (Fin 3) (PadicAlgCl l)) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l))).det *
        ((P : Matrix (Fin 3) (Fin 3) (PadicAlgCl l))).det = 1 := by
      rw [← Matrix.det_mul, Units.inv_mul, Matrix.det_one]
    have h3 : (x • (1 : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) - T).det =
        ∏ k, (x • (1 : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) - T) k k := by
      apply Matrix.det_of_upperTriangular
      intro a b hab
      have hne : a ≠ b := (ne_of_lt hab).symm
      simp [Matrix.sub_apply, Matrix.one_apply, hne, hT a b hab]
    calc (x • (1 : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) - M).det
        = ((((P⁻¹ : GL (Fin 3) (PadicAlgCl l)) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l))).det *
          ((P : Matrix (Fin 3) (Fin 3) (PadicAlgCl l))).det) *
          (x • (1 : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) - M).det := by rw [h2, one_mul]
      _ = (((P⁻¹ : GL (Fin 3) (PadicAlgCl l)) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) *
          (x • 1 - M) * (P : Matrix (Fin 3) (Fin 3) (PadicAlgCl l))).det := by
        rw [Matrix.det_mul, Matrix.det_mul]
        ring
      _ = ∏ k, (x - T k k) := by
        rw [h1, h3]
        simp [Matrix.sub_apply, Matrix.one_apply]
  have hM1 : ∀ a b, ‖M a b‖ ≤ 1 := by
    intro a b
    have hdg : ‖Matrix.diagonal d a b‖ ≤ 1 := by
      by_cases hab : a = b
      · subst hab
        simp [hd a]
      · simp [Matrix.diagonal_apply_ne _ hab]
    have := IsUltrametricDist.norm_add_le_max (M a b - Matrix.diagonal d a b) (Matrix.diagonal d a b)
    rw [sub_add_cancel] at this
    exact this.trans (max_le (hM a b).le hdg)
  have ht1 : ∀ k, ‖T k k‖ ≤ 1 := fun k =>
    norm_le_one_of_det_smul_one_sub_eq_zero M hM1 (T k k) (by rw [hdet]; exact Finset.prod_eq_zero (Finset.mem_univ k) (sub_self _))
  have ht2 : ∀ a, ∃ k, ‖d a - T k k‖ < 1 := by
    intro a
    have hsmall : ‖(d a • (1 : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) - M).det‖ < 1 := by
      apply norm_det_lt_one_of_norm_le_one_of_norm_apply_lt_one _ a
      · intro c b
        rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
        refine (hsub _ _).trans (max_le ?_ (hM1 c b))
        by_cases hcb : c = b
        · subst hcb
          simp [Matrix.one_apply_eq, hd a]
        · simp [Matrix.one_apply_ne hcb]
      · intro b
        rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
        by_cases hab : a = b
        · subst hab
          have := hM a a
          rw [Matrix.diagonal_apply_eq] at this
          rw [norm_sub_rev] at this
          simpa using this
        · have := hM a b
          rw [Matrix.diagonal_apply_ne _ hab, sub_zero] at this
          simpa [Matrix.one_apply_ne hab] using this
    rw [hdet, norm_prod, Fin.prod_univ_three] at hsmall
    by_contra hne
    push_neg at hne
    have := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (hne 0) (hne 1)) (hne 2)
    linarith
  choose φ hφ using ht2
  have hinj : Function.Injective φ := by
    intro a b hab
    by_contra hne
    have h := hdd a b hne
    have : ‖d a - d b‖ ≤ max ‖d a - T (φ a) (φ a)‖ ‖d b - T (φ a) (φ a)‖ := by
      have := hsub (d a - T (φ a) (φ a)) (d b - T (φ a) (φ a))
      simpa using this
    rw [hab] at this
    have := this.trans_lt (max_lt (hab ▸ hφ a) (hφ b))
    linarith
  have hsurj := Finite.surjective_of_injective hinj
  obtain ⟨a, rfl⟩ := hsurj i
  obtain ⟨b, rfl⟩ := hsurj j
  have hab : a ≠ b := fun h => hij (h ▸ rfl)
  intro heq
  have hclose : ‖T (φ a) (φ a) - T (φ b) (φ b)‖ < 1 := by
    rw [heq, show T (φ b) (φ b) * u - T (φ b) (φ b) = T (φ b) (φ b) * (u - 1) by ring, norm_mul]
    calc ‖T (φ b) (φ b)‖ * ‖u - 1‖ ≤ 1 * ‖u - 1‖ :=
          mul_le_mul_of_nonneg_right (ht1 _) (norm_nonneg _)
      _ < 1 := by linarith
  have hsplit : d a - d b = (d a - T (φ a) (φ a)) +
      ((T (φ a) (φ a) - T (φ b) (φ b)) + (T (φ b) (φ b) - d b)) := by ring
  have h3 : ‖d a - d b‖ < 1 := by
    rw [hsplit]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hφ a) ?_)
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hclose ?_)
    rw [norm_sub_rev]
    exact hφ b
  have := hdd a b hab
  linarith
