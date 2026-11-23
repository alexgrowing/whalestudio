import Formalism.SatakeDualWeyl.Statement

noncomputable section

open Matrix

namespace Formalism.UG.P

variable {n : Type} [Fintype n] [DecidableEq n]

theorem cT_conj_eq_star (M : Matrix n n ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = star M := by
  unfold Formalism.UG.cT
  ext i j
  simp [Matrix.star_apply, Matrix.transpose_apply, Matrix.map_apply]

theorem isCompact_of_unitary {T : Set (Matrix n n ℂ)} (hT : IsClosed T)
    (hU : ∀ M ∈ T, star M * M = 1) : IsCompact T := by
  have hsub : T ⊆ (Set.pi Set.univ (fun _ : n => Set.pi Set.univ
      (fun _ : n => Metric.closedBall (0 : ℂ) 1)) : Set (Matrix n n ℂ)) := by
    intro M hM i _ j _
    have h := congrFun (congrFun (hU M hM) j) j
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
    have key : ∀ z : ℂ, star z * z = ((Complex.normSq z : ℝ) : ℂ) := by
      intro z
      rw [Complex.normSq_eq_conj_mul_self]
      rfl
    simp only [key] at h
    rw [← Complex.ofReal_sum, ← Complex.ofReal_one, Complex.ofReal_inj] at h
    have hle : Complex.normSq (M i j) ≤ 1 := by
      rw [← h]
      exact Finset.single_le_sum (f := fun x => Complex.normSq (M x j))
        (fun x _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
    rw [Metric.mem_closedBall, dist_zero_right]
    have h2 : ‖M i j‖ ^ 2 ≤ 1 := by
      rw [← Complex.normSq_eq_norm_sq]
      exact hle
    nlinarith [norm_nonneg (M i j)]
  have hK : IsCompact (Set.pi Set.univ (fun _ : n => Set.pi Set.univ
      (fun _ : n => Metric.closedBall (0 : ℂ) 1)) : Set (Matrix n n ℂ)) :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall 0 1))
  exact hK.of_isClosed_subset hT hsub

private theorem mul_star_eq_one_of_star_mul_eq_one {M : Matrix n n ℂ} (h : star M * M = 1) : M * star M = 1 := by
  first
  | exact mul_eq_one_comm.mp h
  | (rw [← Matrix.inv_eq_left_inv h]; exact Matrix.mul_nonsing_inv M (Matrix.isUnit_det_of_left_inverse h))

theorem isCompact_units_of_unitary {T : Set (Matrix n n ℂ)} (hT : IsClosed T)
    (hU : ∀ M ∈ T, star M * M = 1) :
    IsCompact {g : GL n ℂ | (g : Matrix n n ℂ) ∈ T} := by
  have hK : IsCompact T := isCompact_of_unitary hT hU
  haveI : CompactSpace T := isCompact_iff_compactSpace.mp hK
  let f : T → GL n ℂ := fun M =>
    ⟨M.1, star M.1, mul_star_eq_one_of_star_mul_eq_one (hU M.1 M.2), hU M.1 M.2⟩
  have hf : Continuous f := by
    rw [Units.continuous_iff]
    exact ⟨continuous_subtype_val, continuous_star.comp continuous_subtype_val⟩
  have hS : {g : GL n ℂ | (g : Matrix n n ℂ) ∈ T} = Set.range f := by
    ext g
    constructor
    · intro hg
      exact ⟨⟨g, hg⟩, Units.ext rfl⟩
    · rintro ⟨M, rfl⟩
      exact M.2
  rw [hS]
  exact isCompact_range hf

theorem mem_Upq_iff (p q : ℕ) (g : GL (Fin p ⊕ Fin q) ℂ) :
    g ∈ Formalism.UG.Upq p q ↔
      star (g : Matrix _ _ ℂ) * Formalism.UG.Jpq p q * (g : Matrix _ _ ℂ) = Formalism.UG.Jpq p q := by
  unfold Formalism.UG.Upq UJ
  first
  | (simp [cT_conj_eq_star]; done)
  | done

theorem Jpq_zero (p : ℕ) : Formalism.UG.Jpq p 0 = 1 := by
  unfold Formalism.UG.Jpq
  rw [← Matrix.fromBlocks_one]
  congr 1
  ext i j
  exact i.elim0

theorem indefinite_unitary_compact : Formalism.UG.UpqCompact := by
  intro p
  have hT : IsClosed {M : Matrix (Fin p ⊕ Fin 0) (Fin p ⊕ Fin 0) ℂ | star M * M = 1} :=
    isClosed_eq (continuous_star.mul continuous_id) continuous_const
  have h := isCompact_units_of_unitary hT (fun M hM => hM)
  convert h using 1
  ext g
  simp only [SetLike.mem_coe, mem_Upq_iff, Jpq_zero, mul_one, Set.mem_setOf_eq]

theorem Jpq_eq_diagonal (p q : ℕ) :
    Formalism.UG.Jpq p q = diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
  unfold Formalism.UG.Jpq
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · by_cases h : i = j <;> simp [h, Matrix.one_apply, Matrix.diagonal_apply]
  · simp [Matrix.diagonal_apply]
  · simp [Matrix.diagonal_apply]
  · by_cases h : i = j <;> simp [h, Matrix.one_apply, Matrix.diagonal_apply]

theorem Jpq_mul_self (p q : ℕ) : Formalism.UG.Jpq p q * Formalism.UG.Jpq p q = 1 := by
  rw [Jpq_eq_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  rcases i with i | i <;> simp

def JpqUnit (p q : ℕ) : GL (Fin p ⊕ Fin q) ℂ :=
  ⟨Formalism.UG.Jpq p q, Formalism.UG.Jpq p q, Jpq_mul_self p q, Jpq_mul_self p q⟩

theorem mem_blockDiag_iff (p q : ℕ) (g : GL (Fin p ⊕ Fin q) ℂ) :
    g ∈ Formalism.UG.blockDiag p q ↔
      Formalism.UG.Jpq p q * (g : Matrix _ _ ℂ) = (g : Matrix _ _ ℂ) * Formalism.UG.Jpq p q := by
  simp only [Formalism.UG.blockDiag, Set.mem_setOf_eq]
  rw [Jpq_eq_diagonal]
  constructor
  · intro h
    ext a b
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    rcases a with i | i <;> rcases b with j | j
    · simp
    · simp [(h i j).1]
    · simp [(h j i).2]
    · simp
  · intro h i j
    have h1 := congrFun (congrFun h (Sum.inl i)) (Sum.inr j)
    have h2 := congrFun (congrFun h (Sum.inr j)) (Sum.inl i)
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at h1 h2
    simp only [Sum.elim_inl, Sum.elim_inr, one_mul, mul_one, mul_neg, neg_mul] at h1 h2
    constructor
    · first | exact h1 | linear_combination h1 / 2 | linear_combination -h1 / 2
    · first | exact h2 | linear_combination h2 / 2 | linear_combination -h2 / 2

theorem maximal_compact_subgroup_compact : Formalism.UG.KpqSubgroupCompact := by
  intro p q
  have hJ : ((JpqUnit p q : GL (Fin p ⊕ Fin q) ℂ) : Matrix _ _ ℂ) = Formalism.UG.Jpq p q := rfl
  have hset : ((Formalism.UG.Upq p q ⊓ Subgroup.centralizer {JpqUnit p q} : Subgroup _) :
      Set (GL (Fin p ⊕ Fin q) ℂ)) = ↑(Formalism.UG.Upq p q) ∩ Formalism.UG.blockDiag p q := by
    ext g
    simp only [Subgroup.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, Subgroup.mem_centralizer_iff,
      Set.mem_singleton_iff, forall_eq, mem_blockDiag_iff]
    rw [Units.ext_iff, Units.val_mul, Units.val_mul, hJ]
  refine ⟨_, hset, ?_⟩
  rw [hset]
  have hT : IsClosed {M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ |
      star M * Formalism.UG.Jpq p q * M = Formalism.UG.Jpq p q ∧ Formalism.UG.Jpq p q * M = M * Formalism.UG.Jpq p q} := by
    apply IsClosed.inter
    · exact isClosed_eq ((continuous_star.mul continuous_const).mul continuous_id) continuous_const
    · exact isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)
  have hU : ∀ M ∈ {M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ |
      star M * Formalism.UG.Jpq p q * M = Formalism.UG.Jpq p q ∧ Formalism.UG.Jpq p q * M = M * Formalism.UG.Jpq p q},
      star M * M = 1 := by
    rintro M ⟨h1, h2⟩
    have hJJ := Jpq_mul_self p q
    calc star M * M = star M * M * (Formalism.UG.Jpq p q * Formalism.UG.Jpq p q) := by rw [hJJ, mul_one]
      _ = star M * (Formalism.UG.Jpq p q * M) * Formalism.UG.Jpq p q := by rw [h2]; simp only [mul_assoc]
      _ = 1 := by rw [← mul_assoc, h1, hJJ]
  convert isCompact_units_of_unitary hT hU using 1
  ext g
  simp only [Set.mem_inter_iff, SetLike.mem_coe, mem_Upq_iff, mem_blockDiag_iff, Set.mem_setOf_eq]

end Formalism.UG.P
