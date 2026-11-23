import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ParahoricIndexCount.Development

noncomputable section

open Matrix

namespace PI.ParahoricIdxZ.W

section A

variable {F : Type} [Field F] (O : Subring F) (ϖ : F)

theorem reindex_apply' {a t : ℕ} {R : Type} (A : Matrix (Fin (a + t)) (Fin (a + t)) R)
    (x y : Fin a ⊕ Fin t) :
    Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm A x y =
      A (finSumFinEquiv x) (finSumFinEquiv y) := by
  rfl

def theta {a t : ℕ} {R : Type} (A : Matrix (Fin a) (Fin a) R) (B : Matrix (Fin a) (Fin t) R)
    (C : Matrix (Fin t) (Fin a) R) (D : Matrix (Fin t) (Fin t) R) :
    Matrix (Fin (a + t)) (Fin (a + t)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A B C D)

theorem reindex_theta {a t : ℕ} {R : Type} (A : Matrix (Fin a) (Fin a) R)
    (B : Matrix (Fin a) (Fin t) R) (C : Matrix (Fin t) (Fin a) R) (D : Matrix (Fin t) (Fin t) R) :
    Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm (theta A B C D) =
      Matrix.fromBlocks A B C D := by
  ext x y
  simp [theta, Matrix.reindex_apply]

theorem theta_apply {a t : ℕ} {R : Type} (A : Matrix (Fin a) (Fin a) R)
    (B : Matrix (Fin a) (Fin t) R) (C : Matrix (Fin t) (Fin a) R) (D : Matrix (Fin t) (Fin t) R)
    (x y : Fin a ⊕ Fin t) :
    theta A B C D (finSumFinEquiv x) (finSumFinEquiv y) = Matrix.fromBlocks A B C D x y := by
  simp [theta, Matrix.reindex_apply]

theorem theta_injective {a t : ℕ} {R : Type} {A A' : Matrix (Fin a) (Fin a) R}
    {B B' : Matrix (Fin a) (Fin t) R} {C C' : Matrix (Fin t) (Fin a) R}
    {D D' : Matrix (Fin t) (Fin t) R} (h : theta A B C D = theta A' B' C' D') :
    A = A' ∧ B = B' ∧ C = C' ∧ D = D' := by
  have h2 := congrArg (Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm) h
  rw [reindex_theta, reindex_theta] at h2
  exact Matrix.fromBlocks_inj.mp h2

theorem theta_mul {a t : ℕ} {R : Type} [CommRing R] (A A' : Matrix (Fin a) (Fin a) R)
    (B B' : Matrix (Fin a) (Fin t) R) (C C' : Matrix (Fin t) (Fin a) R)
    (D D' : Matrix (Fin t) (Fin t) R) :
    theta A B C D * theta A' B' C' D' =
      theta (A * A' + B * C') (A * B' + B * D') (C * A' + D * C') (C * B' + D * D') := by
  simp only [theta, Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem theta_one {a t : ℕ} {R : Type} [CommRing R] :
    theta (1 : Matrix (Fin a) (Fin a) R) 0 0 (1 : Matrix (Fin t) (Fin t) R) = 1 := by
  simp [theta, Matrix.reindex_apply]

theorem intProd {l m n : Type} [Fintype m] {X : Matrix l m F} {Y : Matrix m n F}
    (hX : ∀ i j, X i j ∈ O) (hY : ∀ i j, Y i j ∈ O) : ∀ i j, (X * Y) i j ∈ O := by
  intro i j
  rw [Matrix.mul_apply]
  exact O.sum_mem fun k _ => O.mul_mem (hX i k) (hY k j)

theorem theta_int {a t : ℕ} {A : Matrix (Fin a) (Fin a) F} {B : Matrix (Fin a) (Fin t) F}
    {C : Matrix (Fin t) (Fin a) F} {D : Matrix (Fin t) (Fin t) F}
    (hA : ∀ i j, A i j ∈ O) (hB : ∀ i j, B i j ∈ O) (hC : ∀ i j, C i j ∈ O)
    (hD : ∀ i j, D i j ∈ O) : Formalism.DoubleCosetMeasures.IsInt O (theta A B C D) := by
  unfold Formalism.DoubleCosetMeasures.IsInt
  intro i j
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective j
  rw [theta_apply]
  rcases x with x | x <;> rcases y with y | y <;> simp [hA, hB, hC, hD]

variable {ϖ}

private theorem exists_GLint_eq_one_add_smul (hϖ : ϖ ∈ O) (hloc : Formalism.DoubleCosetMeasures.IsLocalAt O ϖ) {n : ℕ}
    (X : Matrix (Fin n) (Fin n) F) (hX : ∀ i j, X i j ∈ O) :
    ∃ k ∈ Formalism.DoubleCosetMeasures.GLint O n, (k : Matrix (Fin n) (Fin n) F) = 1 + ϖ • X := by
  let w : O := ⟨ϖ, hϖ⟩
  let Y : Matrix (Fin n) (Fin n) O := fun i j => ⟨X i j, hX i j⟩
  obtain ⟨c, hc⟩ : ∃ c : O, (1 + w • Y).det = 1 + c * w := by
    have h0 : Ideal.Quotient.mk (Ideal.span {w}) w = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self w)
    have h1 : (Ideal.Quotient.mk (Ideal.span {w})).mapMatrix (1 + w • Y) = 1 := by
      ext i j
      by_cases h : i = j
      · subst h; simp [h0]
      · simp [h0, Matrix.one_apply_ne h]
    have h2 : (1 + w • Y).det - 1 ∈ Ideal.span {w} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, RingHom.map_det, h1, Matrix.det_one, map_one,
        sub_self]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h2
    exact ⟨c, by rw [hc]; ring⟩
  have key : ∀ o ∈ O, ((1 + c * w : O) : F) ≠ ϖ * o := by
    intro o ho h
    apply hloc.1
    have h' : ϖ * (o - c) = 1 := by
      have h3 : (1 : F) + (c : F) * ϖ = ϖ * o := by simpa [w] using h
      linear_combination -h3
    rw [inv_eq_of_mul_eq_one_right h']
    exact O.sub_mem ho c.2
  have hz : ((1 + c * w : O) : F) ≠ 0 := fun h0 => key 0 O.zero_mem (by rw [h0, mul_zero])
  have hu : IsUnit (1 + w • Y).det := by
    rw [hc]
    refine isUnit_iff_exists_inv.mpr ⟨⟨((1 + c * w : O) : F)⁻¹, hloc.2 _ (1 + c * w).2 key⟩, ?_⟩
    apply Subtype.ext
    show ((1 + c * w : O) : F) * ((1 + c * w : O) : F)⁻¹ = 1
    exact mul_inv_cancel₀ hz
  refine ⟨Units.map (RingHom.mapMatrix O.subtype).toMonoidHom (Matrix.nonsingInvUnit _ hu), ?_, ?_⟩
  · exact ⟨fun i j => SetLike.coe_mem _, fun i j => SetLike.coe_mem _⟩
  · ext i j
    by_cases h : i = j
    · subst h; simp [Matrix.nonsingInvUnit, Y, w]; rfl
    · simp [Matrix.nonsingInvUnit, Y, w, Matrix.one_apply_ne h]; rfl

theorem cong_blockCond (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0) (hloc : Formalism.DoubleCosetMeasures.IsLocalAt O ϖ) {a t : ℕ}
    {J' : Subgroup (GL (Fin a) F)} (hKJ : Formalism.DoubleCosetMeasures.congSub O ϖ a ≤ J')
    {g : GL (Fin (a + t)) F} (hg : g ∈ Formalism.DoubleCosetMeasures.congSub O ϖ (a + t)) : blockCond O ϖ J' g := by
  obtain ⟨-, hgX⟩ := hg
  have hXO : ∀ u v, ϖ⁻¹ * ((g : Matrix (Fin (a + t)) (Fin (a + t)) F) u v -
      (1 : Matrix (Fin (a + t)) (Fin (a + t)) F) u v) ∈ O := by
    intro u v
    have h := hgX u v
    rwa [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] at h
  have hone : ∀ x y : Fin a ⊕ Fin t, (1 : Matrix (Fin (a + t)) (Fin (a + t)) F)
      (finSumFinEquiv x) (finSumFinEquiv y) = (1 : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) F) x y := by
    intro x y
    by_cases h : x = y
    · subst h; simp
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne (fun h' => h (finSumFinEquiv.injective h'))]
  have hG : ∀ x y : Fin a ⊕ Fin t,
      (g : Matrix (Fin (a + t)) (Fin (a + t)) F) (finSumFinEquiv x) (finSumFinEquiv y) =
      (1 : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) F) x y +
        ϖ * (ϖ⁻¹ * ((g : Matrix (Fin (a + t)) (Fin (a + t)) F) (finSumFinEquiv x) (finSumFinEquiv y) -
          (1 : Matrix (Fin (a + t)) (Fin (a + t)) F) (finSumFinEquiv x) (finSumFinEquiv y))) := by
    intro x y
    rw [mul_inv_cancel_left₀ hϖ0, hone]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨k, hk, hkeq⟩ := exists_GLint_eq_one_add_smul O hϖ hloc
      (fun i j : Fin a => ϖ⁻¹ * ((g : Matrix (Fin (a + t)) (Fin (a + t)) F) (finSumFinEquiv (Sum.inl i))
        (finSumFinEquiv (Sum.inl j)) - (1 : Matrix (Fin (a + t)) (Fin (a + t)) F)
          (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)))) (fun i j => hXO _ _)
    refine ⟨k, hKJ ⟨hk, ?_⟩, ?_⟩
    · intro i j
      rw [Matrix.smul_apply, Matrix.sub_apply, hkeq]
      show ϖ⁻¹ * ((1 : Matrix (Fin a) (Fin a) F) i j + ϖ * (ϖ⁻¹ * (_ - _)) -
        (1 : Matrix (Fin a) (Fin a) F) i j) ∈ O
      rw [add_sub_cancel_left, inv_mul_cancel_left₀ hϖ0]
      exact hXO _ _
    · rw [hkeq]
      ext i j
      show (1 : Matrix (Fin a) (Fin a) F) i j + ϖ * (ϖ⁻¹ * (_ - _)) =
        (g : Matrix (Fin (a + t)) (Fin (a + t)) F) (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j))
      rw [mul_inv_cancel_left₀ hϖ0, hone]
      simp [Matrix.one_apply]
  · intro i j
    show (g : Matrix (Fin (a + t)) (Fin (a + t)) F) (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) ∈ O
    rw [hG]
    exact O.add_mem (by simp [Matrix.one_apply, O.zero_mem]) (O.mul_mem hϖ (hXO _ _))
  · simp only [Formalism.DoubleCosetMeasures.IIset, Set.mem_setOf_eq]
    intro i j
    refine ⟨_, hXO (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)), ?_⟩
    show (g : Matrix (Fin (a + t)) (Fin (a + t)) F) (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = _
    conv_lhs => rw [hG]
    simp [Matrix.one_apply]
  · obtain ⟨k, hk, hkeq⟩ := exists_GLint_eq_one_add_smul O hϖ hloc
      (fun i j : Fin t => ϖ⁻¹ * ((g : Matrix (Fin (a + t)) (Fin (a + t)) F) (finSumFinEquiv (Sum.inr i))
        (finSumFinEquiv (Sum.inr j)) - (1 : Matrix (Fin (a + t)) (Fin (a + t)) F)
          (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)))) (fun i j => hXO _ _)
    refine ⟨k, hk, ?_⟩
    rw [hkeq]
    ext i j
    show (1 : Matrix (Fin t) (Fin t) F) i j + ϖ * (ϖ⁻¹ * (_ - _)) =
      (g : Matrix (Fin (a + t)) (Fin (a + t)) F) (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j))
    rw [mul_inv_cancel_left₀ hϖ0, hone]
    simp [Matrix.one_apply]

end A

end PI.ParahoricIdxZ.W
