import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient

open Matrix Module Function

open private exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot from
  Mathlib.LinearAlgebra.SymplecticGroup

namespace GlobalTheory

section Semilocal

variable {R : Type*} [CommRing R]

theorem isUnit_of_forall_maximalSpectrum_mk_ne_zero {x : R}
    (h : ∀ m : MaximalSpectrum R, Ideal.Quotient.mk m.asIdeal x ≠ 0) : IsUnit x := by
  by_contra hx
  obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hx)
  exact h ⟨m, hm⟩ (Ideal.Quotient.eq_zero_iff_mem.2 hxm)

theorem exists_lift_maximalSpectrum_pi [Finite (MaximalSpectrum R)] :
    ∃ s : (∀ m : MaximalSpectrum R, R ⧸ m.asIdeal) → R,
      ∀ x m, Ideal.Quotient.mk m.asIdeal (s x) = x m := by
  choose s hs using Ideal.pi_quotient_surjective (I := fun m : MaximalSpectrum R => m.asIdeal)
    fun _ _ => MaximalSpectrum.isCoprime_of_ne
  exact ⟨s, hs⟩

theorem exists_matrix_lift_maximalSpectrum [Finite (MaximalSpectrum R)] {m n : Type*}
    (Y : ∀ p : MaximalSpectrum R, Matrix m n (R ⧸ p.asIdeal)) :
    ∃ X : Matrix m n R, ∀ p, X.map (Ideal.Quotient.mk p.asIdeal) = Y p := by
  obtain ⟨s, hs⟩ := exists_lift_maximalSpectrum_pi (R := R)
  exact ⟨Matrix.of fun i j => s fun p => Y p i j, fun p => Matrix.ext fun i j => by simp [hs]⟩

end Semilocal

section SpecialLinear

variable {S R : Type*} [CommRing S] [CommRing R] {f : S →+* R}
  {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

def LiftsToDetOne (f : S →+* R) (A : Matrix n n R) : Prop :=
  ∃ B : Matrix n n S, B.det = 1 ∧ B.map f = A

namespace LiftsToDetOne

theorem one : LiftsToDetOne f (1 : Matrix n n R) := ⟨1, det_one, by simp⟩

theorem det_eq {A : Matrix n n R} (h : LiftsToDetOne f A) : A.det = 1 := by
  obtain ⟨B, hB, rfl⟩ := h
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hB, map_one]

theorem mul {A B : Matrix n n R} (hA : LiftsToDetOne f A) (hB : LiftsToDetOne f B) :
    LiftsToDetOne f (A * B) := by
  obtain ⟨A, hA, rfl⟩ := hA
  obtain ⟨B, hB, rfl⟩ := hB
  exact ⟨A * B, by simp [hA, hB], Matrix.map_mul⟩

theorem adjugate {A : Matrix n n R} (hA : LiftsToDetOne f A) : LiftsToDetOne f A.adjugate := by
  obtain ⟨A, hA, rfl⟩ := hA
  exact ⟨A.adjugate, by simp [det_adjugate, hA], f.map_adjugate A⟩

theorem of_mul_left {E A : Matrix n n R} (hE : LiftsToDetOne f E) (h : LiftsToDetOne f (E * A)) :
    LiftsToDetOne f A := by
  have := hE.adjugate.mul h
  rwa [← Matrix.mul_assoc, adjugate_mul, hE.det_eq, one_smul, Matrix.one_mul] at this

theorem of_reindex {A : Matrix n n R} (e : n ≃ m) (h : LiftsToDetOne f (reindex e e A)) :
    LiftsToDetOne f A := by
  obtain ⟨B, hB, h⟩ := h
  refine ⟨reindex e.symm e.symm B, by simpa using hB, ?_⟩
  ext i j
  simpa using congrFun (congrFun h (e i)) (e j)

theorem upper (hf : Surjective f) (X : Matrix n m R) :
    LiftsToDetOne f (fromBlocks (1 : Matrix n n R) X 0 (1 : Matrix m m R)) := by
  obtain ⟨s, hs⟩ := hf.hasRightInverse
  refine ⟨fromBlocks 1 (X.map s) 0 1, by simp, ?_⟩
  simp [fromBlocks_map, hs.comp_eq_id]

theorem lower (hf : Surjective f) (X : Matrix m n R) :
    LiftsToDetOne f (fromBlocks (1 : Matrix n n R) 0 X (1 : Matrix m m R)) := by
  obtain ⟨s, hs⟩ := hf.hasRightInverse
  refine ⟨fromBlocks 1 0 (X.map s) 1, by simp, ?_⟩
  simp [fromBlocks_map, hs.comp_eq_id]

theorem block {D : Matrix m m R} (h : LiftsToDetOne f D) :
    LiftsToDetOne f (fromBlocks (1 : Matrix n n R) 0 0 D) := by
  obtain ⟨D, hD, rfl⟩ := h
  exact ⟨fromBlocks 1 0 0 D, by simp [hD], by simp [fromBlocks_map]⟩

theorem transvection (hf : Surjective f) {i j : n} (hij : i ≠ j) (c : R) :
    LiftsToDetOne f (Matrix.transvection i j c) := by
  obtain ⟨c, rfl⟩ := hf c
  refine ⟨Matrix.transvection i j c, det_transvection_of_ne _ _ hij _, ?_⟩
  simp [Matrix.transvection, Matrix.map_add, Matrix.map_single]

end LiftsToDetOne

theorem exists_isUnit_corner [Finite (MaximalSpectrum R)] {A : Matrix (Unit ⊕ m) (Unit ⊕ m) R}
    (hA : IsUnit A.det) : ∃ t : Matrix Unit m R,
      IsUnit ((fromBlocks (1 : Matrix Unit Unit R) t 0 (1 : Matrix m m R) * A) (.inl ()) (.inl ())) := by
  have key : ∀ p : MaximalSpectrum R, ∃ t : Matrix Unit m (R ⧸ p.asIdeal),
      Ideal.Quotient.mk p.asIdeal (A (.inl ()) (.inl ())) +
        ∑ j, t () j * Ideal.Quotient.mk p.asIdeal (A (.inr j) (.inl ())) ≠ 0 := by
    intro p
    have := p.isMaximal
    by_cases h0 : Ideal.Quotient.mk p.asIdeal (A (.inl ()) (.inl ())) = 0
    · by_contra! hne
      have hcol : ∀ i, (A.map (Ideal.Quotient.mk p.asIdeal)) i (.inl ()) = 0 := by
        rintro (i | i)
        · exact h0
        · simpa [h0, Pi.single_apply] using hne (Matrix.of fun _ => Pi.single i 1)
      have hdet := det_eq_zero_of_column_eq_zero _ hcol
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at hdet
      exact (hA.map _).ne_zero hdet
    · exact ⟨0, by simpa using h0⟩
  choose t ht using key
  obtain ⟨T, hT⟩ := exists_matrix_lift_maximalSpectrum t
  refine ⟨T, isUnit_of_forall_maximalSpectrum_mk_ne_zero fun p => ?_⟩
  have := ht p
  rw [← hT p] at this
  simpa [Matrix.mul_apply, Fintype.sum_sum_type] using this

theorem liftsToDetOne_of_corner_eq_one (hf : Surjective f)
    (ih : ∀ D : Matrix m m R, D.det = 1 → LiftsToDetOne f D)
    {A : Matrix (Unit ⊕ m) (Unit ⊕ m) R} (hA : A.det = 1) (h1 : A (.inl ()) (.inl ()) = 1) :
    LiftsToDetOne f A := by
  have ha : A.toBlocks₁₁ = 1 := by
    ext ⟨⟩ ⟨⟩
    simpa [toBlocks₁₁] using h1
  have hdec : A = fromBlocks 1 0 A.toBlocks₂₁ 1 *
      fromBlocks 1 0 0 (A.toBlocks₂₂ - A.toBlocks₂₁ * A.toBlocks₁₂) *
        fromBlocks 1 A.toBlocks₁₂ 0 1 := by
    conv_lhs => rw [← A.fromBlocks_toBlocks, ha]
    simp [fromBlocks_multiply]
  have hD : (A.toBlocks₂₂ - A.toBlocks₂₁ * A.toBlocks₁₂).det = 1 := by
    rw [hdec] at hA
    simpa only [det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂, det_one, one_mul,
      mul_one] using hA
  rw [hdec]
  exact ((LiftsToDetOne.lower hf _).mul (ih _ hD).block).mul (LiftsToDetOne.upper hf _)

theorem liftsToDetOne_of_isUnit_corner (hf : Surjective f)
    (ih : ∀ D : Matrix m m R, D.det = 1 → LiftsToDetOne f D)
    {A : Matrix (Unit ⊕ m) (Unit ⊕ m) R} (hA : A.det = 1)
    (h1 : IsUnit (A (.inl ()) (.inl ()))) : LiftsToDetOne f A := by
  rcases isEmpty_or_nonempty m with hm | ⟨⟨j⟩⟩
  · refine liftsToDetOne_of_corner_eq_one hf ih hA ?_
    have : Subsingleton (Unit ⊕ m) := ⟨by rintro (i | i) (j | j) <;> first | rfl | exact hm.elim ‹_›⟩
    rw [← hA, det_eq_elem_of_subsingleton A (.inl ())]
  obtain ⟨a, ha⟩ := h1.exists_left_inv
  have e₁ := LiftsToDetOne.transvection (i := (.inr j : Unit ⊕ m)) (j := .inl ()) hf (by simp)
    ((1 - A (.inr j) (.inl ())) * a)
  have e₂ := LiftsToDetOne.transvection (i := (.inl () : Unit ⊕ m)) (j := .inr j) hf (by simp)
    (1 - A (.inl ()) (.inl ()))
  refine e₁.of_mul_left (e₂.of_mul_left (liftsToDetOne_of_corner_eq_one hf ih ?_ ?_))
  · rw [det_mul, det_mul, e₁.det_eq, e₂.det_eq, hA, one_mul, one_mul]
  · rw [transvection_mul_apply_same, transvection_mul_apply_same,
      transvection_mul_apply_of_ne _ _ _ _ (by simp), mul_assoc, ha]
    ring

theorem liftsToDetOne_of_det_eq_one [Finite (MaximalSpectrum R)] (hf : Surjective f)
    {A : Matrix n n R} (hA : A.det = 1) : LiftsToDetOne f A := by
  have key : ∀ (k : ℕ) (A : Matrix (Fin k) (Fin k) R), A.det = 1 → LiftsToDetOne f A := by
    intro k
    induction k with
    | zero => intro A _; rw [Subsingleton.elim A 1]; exact .one
    | succ k ih =>
      intro A hA
      let e : Fin (k + 1) ≃ Unit ⊕ Fin k := Fintype.equivOfCardEq (by simp [add_comm])
      refine .of_reindex e ?_
      have hA' : (reindex e e A).det = 1 := by simpa using hA
      obtain ⟨t, ht⟩ := exists_isUnit_corner (A := reindex e e A) (by simp [hA])
      refine (LiftsToDetOne.upper hf t).of_mul_left (liftsToDetOne_of_isUnit_corner hf ih ?_ ht)
      rw [det_mul, hA', (LiftsToDetOne.upper hf t).det_eq, one_mul]
  exact .of_reindex (Fintype.equivFin n) (key _ _ (by simpa using hA))

theorem specialLinearGroup_map_surjective [Finite (MaximalSpectrum R)] (hf : Surjective f) :
    Surjective (SpecialLinearGroup.map (n := n) f) := fun A => by
  obtain ⟨B, hB, h⟩ := liftsToDetOne_of_det_eq_one hf A.2
  exact ⟨⟨B, hB⟩, Subtype.ext h⟩

end SpecialLinear

section Symplectic

variable {S R : Type*} [CommRing S] [CommRing R] {f : S →+* R}
  {l : Type*} [Fintype l] [DecidableEq l]

def symplecticGroupMap (l : Type*) [Fintype l] [DecidableEq l] (f : S →+* R) :
    symplecticGroup l S →* symplecticGroup l R where
  toFun A := ⟨A.1.map f, SymplecticGroup.map_mem A.2 f⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext Matrix.map_mul

@[simp]
theorem coe_symplecticGroupMap (A : symplecticGroup l S) :
    (symplecticGroupMap l f A).1 = A.1.map f := rfl

def LiftsToSymplectic (f : S →+* R) (A : Matrix (l ⊕ l) (l ⊕ l) R) : Prop :=
  ∃ B ∈ symplecticGroup l S, B.map f = A

omit [Fintype l] [DecidableEq l] in
theorem exists_isSymm_map_eq (hf : Surjective f) {X : Matrix l l R} (hX : X.IsSymm) :
    ∃ Y : Matrix l l S, Y.IsSymm ∧ Y.map f = X := by
  obtain ⟨s, hs⟩ := hf.hasRightInverse
  exact ⟨X.map s, hX.map s, Matrix.ext fun i j => hs (X i j)⟩

namespace LiftsToSymplectic

theorem mul {A B : Matrix (l ⊕ l) (l ⊕ l) R} (hA : LiftsToSymplectic f A)
    (hB : LiftsToSymplectic f B) : LiftsToSymplectic f (A * B) := by
  obtain ⟨A, hA, rfl⟩ := hA
  obtain ⟨B, hB, rfl⟩ := hB
  exact ⟨A * B, mul_mem hA hB, Matrix.map_mul⟩

theorem J : LiftsToSymplectic f (Matrix.J l R) :=
  ⟨Matrix.J l S, SymplecticGroup.J_mem _ _, map_J _ _⟩

theorem upper (hf : Surjective f) {X : Matrix l l R} (hX : X.IsSymm) :
    LiftsToSymplectic f (fromBlocks 1 X 0 1) := by
  obtain ⟨Y, hY, rfl⟩ := exists_isSymm_map_eq hf hX
  exact ⟨fromBlocks 1 Y 0 1, by simp [SymplecticGroup.fromBlocks_mem_iff, hY.eq],
    by simp [fromBlocks_map]⟩

theorem lower (hf : Surjective f) {X : Matrix l l R} (hX : X.IsSymm) :
    LiftsToSymplectic f (fromBlocks 1 0 X 1) := by
  obtain ⟨Y, hY, rfl⟩ := exists_isSymm_map_eq hf hX
  exact ⟨fromBlocks 1 0 Y 1, by simp [SymplecticGroup.fromBlocks_mem_iff, hY.eq],
    by simp [fromBlocks_map]⟩

theorem levi_of_isSymm (hf : Surjective f) {X Y : Matrix l l R} (hX : X.IsSymm) (hY : Y.IsSymm)
    (h : X * Y = 1) : LiftsToSymplectic f (fromBlocks X 0 0 Y) := by
  have h' : Y * X = 1 := mul_eq_one_comm.1 h
  have := (((upper hf hX).mul (lower hf hY.neg)).mul (upper hf hX)).mul J
  simpa [fromBlocks_multiply, Matrix.J, h, h'] using this

theorem levi_of_det_eq_one [Finite (MaximalSpectrum R)] (hf : Surjective f) {X Y : Matrix l l R}
    (hX : X.det = 1) (h : Xᵀ * Y = 1) : LiftsToSymplectic f (fromBlocks X 0 0 Y) := by
  obtain ⟨A, hA, rfl⟩ := liftsToDetOne_of_det_eq_one hf hX
  have hA' : Aᵀ * Aᵀ.adjugate = 1 := by simp [mul_adjugate, hA]
  refine ⟨fromBlocks A 0 0 Aᵀ.adjugate, by simp [SymplecticGroup.fromBlocks_mem_iff, hA'], ?_⟩
  have : Aᵀ.adjugate.map f = Y := by
    refine right_inv_eq_right_inv ?_ h
    rw [← transpose_map, ← Matrix.map_mul, hA']
    simp
  simp [fromBlocks_map, this]

theorem levi [Finite (MaximalSpectrum R)] (hf : Surjective f) {X Y : Matrix l l R}
    (h : Xᵀ * Y = 1) : LiftsToSymplectic f (fromBlocks X 0 0 Y) := by
  rcases isEmpty_or_nonempty l with hl | ⟨⟨i⟩⟩
  · exact levi_of_det_eq_one hf det_isEmpty h
  have hd : X.det * Y.det = 1 := by simpa using congrArg det h
  let D : Matrix l l R := diagonal (Function.update 1 i X.det)
  let E : Matrix l l R := diagonal (Function.update 1 i Y.det)
  have hDE : D * E = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext j
    by_cases hj : j = i
    · simp [hj, hd]
    · simp [hj]
  have hED : E * D = 1 := mul_eq_one_comm.1 hDE
  have h₁ := levi_of_isSymm hf (isSymm_diagonal _) (isSymm_diagonal _) hDE
  have h₂ : LiftsToSymplectic f (fromBlocks (E * X) 0 0 (D * Y)) := by
    refine levi_of_det_eq_one hf ?_ ?_
    · rw [det_mul, det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
      simp [mul_comm, hd]
    · rw [transpose_mul, diagonal_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc _ D, hED,
        Matrix.one_mul, h]
  have := h₁.mul h₂
  rw [fromBlocks_multiply] at this
  simpa [← Matrix.mul_assoc, D, E, hDE, hED, -diagonal_mul_diagonal] using this

end LiftsToSymplectic

theorem exists_isSymm_isUnit_add_mul [Finite (MaximalSpectrum R)] {A B C D : Matrix l l R}
    (h : fromBlocks A B C D ∈ symplecticGroup l R) :
    ∃ X : Matrix l l R, X.IsSymm ∧ IsUnit (A + X * C).det := by
  have key : ∀ p : MaximalSpectrum R, ∃ Y : Matrix l l (R ⧸ p.asIdeal), Y.IsSymm ∧
      IsUnit (A.map (Ideal.Quotient.mk p.asIdeal) + Y * C.map (Ideal.Quotient.mk p.asIdeal)) := by
    intro p
    have := p.isMaximal
    let _ := Ideal.Quotient.field p.asIdeal
    have h' := SymplecticGroup.map_mem h (Ideal.Quotient.mk p.asIdeal)
    rw [fromBlocks_map] at h'
    refine exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot (fun x h₁ h₂ => ?_)
      (SymplecticGroup.fromBlocks_mem_iff.1 h').1
    have hu := (isUnit_iff_isUnit_det _).2 (SymplecticGroup.symplectic_det h')
    have := mulVec_injective_iff_isUnit.2 hu (a₁ := Sum.elim x 0) (a₂ := Sum.elim 0 0) (by
      rw [smul_eq_mulVec] at h₁ h₂
      simp [fromBlocks_mulVec, h₁, h₂])
    exact (Sum.elim_eq_iff.1 this).1
  choose Y hY hu using key
  obtain ⟨s, hs⟩ := exists_lift_maximalSpectrum_pi (R := R)
  refine ⟨Matrix.of fun i j => s fun p => Y p i j, ?_,
    isUnit_of_forall_maximalSpectrum_mk_ne_zero fun p => ?_⟩
  · ext i j
    simp only [transpose_apply, of_apply]
    exact congrArg s (funext fun p => (hY p).apply i j)
  · have := p.isMaximal
    have hX : (Matrix.of fun i j => s fun p => Y p i j).map (Ideal.Quotient.mk p.asIdeal) = Y p :=
      Matrix.ext fun i j => by simp [hs]
    rw [RingHom.map_det, map_add, map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
      RingHom.mapMatrix_apply, hX]
    exact ((isUnit_iff_isUnit_det _).1 (hu p)).ne_zero

theorem liftsToSymplectic_of_isUnit [Finite (MaximalSpectrum R)] (hf : Surjective f)
    {A B C D : Matrix l l R} (h : fromBlocks A B C D ∈ symplecticGroup l R) (hA : IsUnit A.det) :
    LiftsToSymplectic f (fromBlocks A B C D) := by
  have := A.invertibleOfIsUnitDet hA
  obtain ⟨h₁, h₂, h₃⟩ := SymplecticGroup.fromBlocks_mem_iff.1 h
  obtain ⟨h₄, -, -⟩ := SymplecticGroup.fromBlocks_mem_iff.1
    (fromBlocks_transpose A B C D ▸ SymplecticGroup.transpose_mem h)
  simp only [transpose_transpose] at h₄
  have hC : (C * A⁻¹).IsSymm := by
    have : Cᵀ = Aᵀ * C * A⁻¹ := by rw [h₁, mul_inv_cancel_right_of_invertible]
    rw [Matrix.IsSymm, transpose_mul, this, transpose_nonsing_inv, Matrix.mul_assoc,
      inv_mul_cancel_left_of_invertible]
  have hB : (A⁻¹ * B).IsSymm := by
    have : Bᵀ = A⁻¹ * (B * Aᵀ) := by rw [← h₄, inv_mul_cancel_left_of_invertible]
    rw [Matrix.IsSymm, transpose_mul, this, transpose_nonsing_inv, ← Matrix.mul_assoc,
      mul_inv_cancel_right_of_invertible]
  have hD : Aᵀ * (D - C * A⁻¹ * B) = 1 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h₁,
      mul_inv_cancel_right_of_invertible, h₃]
  have := ((LiftsToSymplectic.lower hf hC).mul (LiftsToSymplectic.levi hf hD)).mul
    (LiftsToSymplectic.upper hf hB)
  simpa [fromBlocks_multiply, Matrix.mul_assoc] using this

theorem liftsToSymplectic_of_mem [Finite (MaximalSpectrum R)] (hf : Surjective f)
    {M : Matrix (l ⊕ l) (l ⊕ l) R} (hM : M ∈ symplecticGroup l R) : LiftsToSymplectic f M := by
  rw [← M.fromBlocks_toBlocks] at hM ⊢
  obtain ⟨X, hX, hu⟩ := exists_isSymm_isUnit_add_mul hM
  have hmem : fromBlocks 1 X 0 1 ∈ symplecticGroup l R := by
    simp [SymplecticGroup.fromBlocks_mem_iff, hX.eq]
  have h := mul_mem hmem hM
  simp only [fromBlocks_multiply, Matrix.one_mul, Matrix.zero_mul, zero_add] at h
  have := (LiftsToSymplectic.upper hf hX.neg).mul (liftsToSymplectic_of_isUnit hf h hu)
  simpa only [fromBlocks_multiply, Matrix.one_mul, Matrix.zero_mul, zero_add, Matrix.neg_mul,
    add_neg_cancel_right] using this

theorem symplecticGroupMap_surjective [Finite (MaximalSpectrum R)] (hf : Surjective f) :
    Surjective (symplecticGroupMap l f) := fun A => by
  obtain ⟨B, hB, h⟩ := liftsToSymplectic_of_mem hf A.2
  exact ⟨⟨B, hB⟩, Subtype.ext h⟩

end Symplectic

section Gram

variable {R : Type*} [CommRing R] {l n : Type*} [Fintype l] [DecidableEq l] [Fintype n]
  [DecidableEq n]

theorem exists_mul_mul_eq_one_of_card_le_rank {K : Type*} [Field K] (G : Matrix n n K)
    (h : Fintype.card l ≤ G.rank) : ∃ (U : Matrix l n K) (V : Matrix n l K), U * G * V = 1 := by
  obtain ⟨U, V, e, -, -, heq⟩ := exists_rank_normal_form G
  obtain ⟨k⟩ : Nonempty (l ↪ Fin G.rank) := Function.Embedding.nonempty_of_card_le (by simpa)
  let σ : l → n := fun i => e.symm (.inl (k i))
  refine ⟨U.submatrix σ id, V.submatrix id σ, ?_⟩
  have : U.submatrix σ id * G * V.submatrix id σ = (U * G * V).submatrix σ σ := by
    ext i j
    simp [Matrix.mul_apply]
  rw [this, heq]
  ext i j
  simp [σ, Matrix.one_apply]

omit [DecidableEq n] in
theorem matrix_rank_sub_le {K : Type*} [Field K] (A B : Matrix n n K) :
    (A - B).rank ≤ A.rank + B.rank := by
  refine le_trans (Submodule.finrank_mono ?_) (Submodule.finrank_add_le_finrank_add_finrank
    (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin))
  rintro _ ⟨x, rfl⟩
  rw [mulVecLin_apply, sub_mulVec]
  exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨x, rfl⟩) (Submodule.mem_sup_right ⟨x, rfl⟩)

theorem exists_mul_mul_eq_one_of_isUnit_sub_transpose [Finite (MaximalSpectrum R)]
    {G : Matrix (l ⊕ l) (l ⊕ l) R} (h : IsUnit (G - Gᵀ).det) :
    ∃ (U : Matrix l (l ⊕ l) R) (V : Matrix (l ⊕ l) l R), U * G * V = 1 := by
  have key : ∀ p : MaximalSpectrum R, ∃ (U : Matrix l (l ⊕ l) (R ⧸ p.asIdeal))
      (V : Matrix (l ⊕ l) l (R ⧸ p.asIdeal)), U * G.map (Ideal.Quotient.mk p.asIdeal) * V = 1 := by
    intro p
    have := p.isMaximal
    let _ := Ideal.Quotient.field p.asIdeal
    refine exists_mul_mul_eq_one_of_card_le_rank _ ?_
    have h₁ := h.map (Ideal.Quotient.mk p.asIdeal)
    rw [RingHom.map_det, map_sub, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
      transpose_map, ← isUnit_iff_isUnit_det] at h₁
    have h₂ := matrix_rank_sub_le (G.map (Ideal.Quotient.mk p.asIdeal))
      (G.map (Ideal.Quotient.mk p.asIdeal))ᵀ
    rw [rank_of_isUnit _ h₁, rank_transpose, Fintype.card_sum] at h₂
    omega
  choose U V hUV using key
  obtain ⟨U', hU⟩ := exists_matrix_lift_maximalSpectrum U
  obtain ⟨V', hV⟩ := exists_matrix_lift_maximalSpectrum V
  have hu : IsUnit (U' * G * V').det := isUnit_of_forall_maximalSpectrum_mk_ne_zero fun p => by
    have := p.isMaximal
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.map_mul, hU, hV, hUV,
      det_one]
    exact one_ne_zero
  exact ⟨U', V' * (U' * G * V')⁻¹, by rw [← Matrix.mul_assoc, mul_nonsing_inv _ hu]⟩

end Gram

section Bases

variable {R M l : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype l] [DecidableEq l]
  {B : LinearMap.BilinForm R M}

omit [Fintype l] in
theorem isSymplecticFamily_iff_gram (hB : B.IsAlt) (v : l ⊕ l → M) :
    IsSymplecticFamily B (fun i => v (.inl i)) (fun i => v (.inr i)) (fun _ => 1) ↔
      (Matrix.of fun i j => B (v i) (v j)) = -Matrix.J l R := by
  constructor
  · intro h
    ext (i | i) (j | j)
    · simpa [Matrix.J] using h.left_left i j
    · simpa [Matrix.J, Matrix.one_apply] using h.left_right i j
    · have := h.right_left hB i j
      simp only [of_apply, Matrix.J, Matrix.neg_apply, fromBlocks_apply₂₁, Matrix.one_apply, this]
      split_ifs <;> simp
    · simpa [Matrix.J] using h.right_right i j
  · intro h
    refine ⟨fun i j => ?_, fun i j => ?_, fun i => ?_, fun i j hij => ?_⟩
    · simpa [Matrix.J] using congrFun (congrFun h (.inl i)) (.inl j)
    · simpa [Matrix.J] using congrFun (congrFun h (.inr i)) (.inr j)
    · simpa [Matrix.J] using congrFun (congrFun h (.inl i)) (.inr i)
    · simpa [Matrix.J, hij] using congrFun (congrFun h (.inl i)) (.inr j)

theorem IsSymplecticBasis.isSymplecticFamily_iff_toMatrix_mem {b : Basis (l ⊕ l) R M}
    (hb : IsSymplecticBasis B b) (hB : B.IsAlt) (v : l ⊕ l → M) :
    IsSymplecticFamily B (fun i => v (.inl i)) (fun i => v (.inr i)) (fun _ => 1) ↔
      b.toMatrix v ∈ symplecticGroup l R := by
  have h : (Matrix.of fun i j => B (v i) (v j)) =
      (b.toMatrix v)ᵀ * (-Matrix.J l R) * b.toMatrix v := by
    ext i j
    rw [← hb.toMatrix_eq hB, of_apply]
    conv_lhs => rw [← b.sum_toMatrix_smul_self v i, ← b.sum_toMatrix_smul_self v j]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Matrix.mul_apply, transpose_apply, LinearMap.BilinForm.toMatrix_apply]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [isSymplecticFamily_iff_gram hB, h, SymplecticGroup.mem_iff', Matrix.mul_neg, Matrix.neg_mul,
    neg_inj]

theorem IsSymplecticBasis.toMatrix_mem {b c : Basis (l ⊕ l) R M} (hb : IsSymplecticBasis B b)
    (hc : IsSymplecticBasis B c) (hB : B.IsAlt) : b.toMatrix c ∈ symplecticGroup l R :=
  (hb.isSymplecticFamily_iff_toMatrix_mem hB c).1 hc

theorem IsSymplecticBasis.exists_basis_of_toMatrix_mem {b : Basis (l ⊕ l) R M}
    (hb : IsSymplecticBasis B b) (hB : B.IsAlt) {v : l ⊕ l → M}
    (hv : b.toMatrix v ∈ symplecticGroup l R) :
    ∃ c : Basis (l ⊕ l) R M, IsSymplecticBasis B c ∧ ⇑c = v := by
  obtain ⟨h₁, h₂⟩ := (b.is_basis_iff_det (v := v)).2 (SymplecticGroup.symplectic_det hv)
  refine ⟨Basis.mk h₁ h₂.ge, ?_, Basis.coe_mk _ _⟩
  simpa [IsSymplecticBasis, IsSymplecticBasisOfType] using
    (hb.isSymplecticFamily_iff_toMatrix_mem hB v).2 hv

omit [DecidableEq l] in

theorem IsSymplecticBasis.mem_iff_repr_inr {b : Basis (l ⊕ l) R M} (hb : IsSymplecticBasis B b)
    {P : Submodule R M} (hP : ∀ x ∈ P, ∀ y ∈ P, B x y = 0) (h : ∀ i, b (.inl i) ∈ P) (x : M) :
    x ∈ P ↔ ∀ i, b.repr x (.inr i) = 0 := by
  refine ⟨fun hx i => by rw [← hb.apply_left, hP _ (h i) _ hx], fun hx => ?_⟩
  rw [← b.sum_repr x, Fintype.sum_sum_type]
  simpa [hx] using P.sum_mem fun i _ => P.smul_mem _ (h i)

omit [DecidableEq l] in
theorem IsSymplecticBasis.mem_iff_repr_inl {b : Basis (l ⊕ l) R M} (hb : IsSymplecticBasis B b)
    {Q : Submodule R M} (hQ : ∀ x ∈ Q, ∀ y ∈ Q, B x y = 0) (h : ∀ i, b (.inr i) ∈ Q) (x : M) :
    x ∈ Q ↔ ∀ i, b.repr x (.inl i) = 0 := by
  refine ⟨fun hx i => by rw [← hb.apply_right, hQ _ hx _ (h i)], fun hx => ?_⟩
  rw [← b.sum_repr x, Fintype.sum_sum_type]
  simpa [hx] using Q.sum_mem fun i _ => Q.smul_mem _ (h i)

omit [DecidableEq l] in
theorem IsSymplecticBasis.span_inl_eq {b : Basis (l ⊕ l) R M} (hb : IsSymplecticBasis B b)
    {P : Submodule R M} (hP : ∀ x ∈ P, ∀ y ∈ P, B x y = 0) (h : ∀ i, b (.inl i) ∈ P) :
    Submodule.span R (Set.range fun i => b (.inl i)) = P := by
  refine le_antisymm (Submodule.span_le.2 (Set.range_subset_iff.2 h)) fun x hx => ?_
  rw [← b.sum_repr x, Fintype.sum_sum_type]
  simpa [(hb.mem_iff_repr_inr hP h x).1 hx] using
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

omit [DecidableEq l] in
theorem IsSymplecticBasis.span_inr_eq {b : Basis (l ⊕ l) R M} (hb : IsSymplecticBasis B b)
    {Q : Submodule R M} (hQ : ∀ x ∈ Q, ∀ y ∈ Q, B x y = 0) (h : ∀ i, b (.inr i) ∈ Q) :
    Submodule.span R (Set.range fun i => b (.inr i)) = Q := by
  refine le_antisymm (Submodule.span_le.2 (Set.range_subset_iff.2 h)) fun x hx => ?_
  rw [← b.sum_repr x, Fintype.sum_sum_type]
  simpa [(hb.mem_iff_repr_inl hQ h x).1 hx] using
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

omit [DecidableEq l] in

theorem IsSymplecticBasis.exists_adapted [Finite (MaximalSpectrum R)] {b : Basis (l ⊕ l) R M}
    (hb : IsSymplecticBasis B b) (hB : B.IsAlt) {P Q : Submodule R M}
    (hP : ∀ x ∈ P, ∀ y ∈ P, B x y = 0) (hQ : ∀ x ∈ Q, ∀ y ∈ Q, B x y = 0) (hPQ : P ⊔ Q = ⊤) :
    ∃ c : Basis (l ⊕ l) R M, IsSymplecticBasis B c ∧ (∀ i, c (.inl i) ∈ P) ∧
      ∀ i, c (.inr i) ∈ Q := by
  classical
  have : ∀ i, ∃ p ∈ P, ∃ q ∈ Q, p + q = b i := fun i =>
    Submodule.mem_sup.1 (hPQ ▸ Submodule.mem_top)
  choose p hp q hq hpq using this
  let G : Matrix (l ⊕ l) (l ⊕ l) R := Matrix.of fun i j => B (p i) (q j)
  have hG : G - Gᵀ = -Matrix.J l R := by
    rw [← hb.toMatrix_eq hB]
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, ← hpq, ← hpq]
    simp [G, hP _ (hp i) _ (hp j), hQ _ (hq i) _ (hq j), ← hB.neg_eq (p j), sub_eq_add_neg,
      add_comm]
  obtain ⟨U, V, hUV⟩ := exists_mul_mul_eq_one_of_isUnit_sub_transpose (G := G)
    (hG ▸ SymplecticGroup.symplectic_det (SymplecticGroup.neg_mem (SymplecticGroup.J_mem l R)))
  let x : l → M := fun i => ∑ k, U i k • p k
  let y : l → M := fun j => ∑ k, V k j • q k
  have hx : ∀ i, x i ∈ P := fun i => P.sum_mem fun k _ => P.smul_mem _ (hp k)
  have hy : ∀ i, y i ∈ Q := fun i => Q.sum_mem fun k _ => Q.smul_mem _ (hq k)
  have hxy : ∀ i j, B (x i) (y j) = (1 : Matrix l l R) i j := fun i j => by
    rw [← hUV]
    simp only [x, y, G, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Matrix.mul_apply, of_apply]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  obtain ⟨c, hc, hcv⟩ := hb.exists_basis_of_toMatrix_mem hB
    ((hb.isSymplecticFamily_iff_toMatrix_mem hB (Sum.elim x y)).1
      ⟨fun i j => hP _ (hx i) _ (hx j), fun i j => hQ _ (hy i) _ (hy j),
        fun i => by simp [hxy], fun i j hij => by simp [hxy, hij]⟩)
  exact ⟨c, hc, fun i => hcv ▸ hx i, fun i => hcv ▸ hy i⟩

end Bases

section Lifting

variable {S R Λ M l : Type*} [CommRing S] [CommRing R] [Finite (MaximalSpectrum R)]
  [AddCommGroup Λ] [Module S Λ] [AddCommGroup M] [Module R M] [Fintype l]
  {f : S →+* R} {B : LinearMap.BilinForm S Λ} {B' : LinearMap.BilinForm R M}

omit [Finite (MaximalSpectrum R)] in
theorem repr_semilinear_of_map_basis {ι : Type*} [Fintype ι] (φ : Λ →ₛₗ[f] M) {b : Basis ι S Λ}
    {c : Basis ι R M} (h : ∀ i, φ (b i) = c i) (x : Λ) (i : ι) :
    c.repr (φ x) i = f (b.repr x i) := by
  conv_lhs => rw [← b.sum_repr x]
  simp only [map_sum φ, φ.map_smulₛₗ, h, c.repr_sum_self]

theorem IsSymplecticBasis.exists_lift (hf : Surjective f) (hB : B.IsAlt) (hB' : B'.IsAlt)
    (φ : Λ →ₛₗ[f] M) {b : Basis (l ⊕ l) S Λ} {b' : Basis (l ⊕ l) R M}
    (hb : IsSymplecticBasis B b) (hb' : IsSymplecticBasis B' b') (h : ∀ i, φ (b i) = b' i)
    {c' : Basis (l ⊕ l) R M} (hc' : IsSymplecticBasis B' c') :
    ∃ c : Basis (l ⊕ l) S Λ, IsSymplecticBasis B c ∧ ∀ i, φ (c i) = c' i := by
  classical
  obtain ⟨T, hT, hT'⟩ := liftsToSymplectic_of_mem hf (hb'.toMatrix_mem hc' hB')
  have hv : b.toMatrix (fun j => ∑ k, T k j • b k) = T := by
    ext i j
    rw [Basis.toMatrix_apply, b.repr_sum_self]
  obtain ⟨c, hc, hcv⟩ := hb.exists_basis_of_toMatrix_mem hB (hv.symm ▸ hT)
  refine ⟨c, hc, fun j => ?_⟩
  rw [hcv, ← b'.sum_toMatrix_smul_self c' j, ← hT']
  simp only [map_sum φ, φ.map_smulₛₗ, h, map_apply]

theorem IsSymplecticBasis.exists_lift_adapted (hf : Surjective f) (hB : B.IsAlt) (hB' : B'.IsAlt)
    (φ : Λ →ₛₗ[f] M) {b : Basis (l ⊕ l) S Λ} {b' : Basis (l ⊕ l) R M}
    (hb : IsSymplecticBasis B b) (hb' : IsSymplecticBasis B' b') (h : ∀ i, φ (b i) = b' i)
    {P Q : Submodule R M} (hP : ∀ x ∈ P, ∀ y ∈ P, B' x y = 0)
    (hQ : ∀ x ∈ Q, ∀ y ∈ Q, B' x y = 0) (hPQ : P ⊔ Q = ⊤) :
    ∃ c : Basis (l ⊕ l) S Λ, IsSymplecticBasis B c ∧
      Submodule.span R (Set.range fun i => φ (c (.inl i))) = P ∧
      Submodule.span R (Set.range fun i => φ (c (.inr i))) = Q ∧
      (∀ x, φ x ∈ P ↔ ∀ i, f (c.repr x (.inr i)) = 0) ∧
      ∀ x, φ x ∈ Q ↔ ∀ i, f (c.repr x (.inl i)) = 0 := by
  obtain ⟨c', hc', h₁, h₂⟩ := hb'.exists_adapted hB' hP hQ hPQ
  obtain ⟨c, hc, hcc⟩ := hb.exists_lift hf hB hB' φ hb' h hc'
  refine ⟨c, hc, ?_, ?_, fun x => ?_, fun x => ?_⟩
  · simpa only [hcc] using hc'.span_inl_eq hP h₁
  · simpa only [hcc] using hc'.span_inr_eq hQ h₂
  · simp only [hc'.mem_iff_repr_inr hP h₁, repr_semilinear_of_map_basis φ hcc]
  · simp only [hc'.mem_iff_repr_inl hQ h₂, repr_semilinear_of_map_basis φ hcc]

end Lifting

section Reduction

open TensorProduct

variable {S R Λ l : Type*} [CommRing S] [CommRing R] [AddCommGroup Λ] [Module S Λ] [Fintype l]
  {B : LinearMap.BilinForm S Λ}

omit [Fintype l] in

theorem IsSymplecticBasis.baseChange [Algebra S R] {b : Basis (l ⊕ l) S Λ}
    (hb : IsSymplecticBasis B b) : IsSymplecticBasis (B.baseChange R) (b.baseChange R) := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun i => ?_, fun i j hij => ?_⟩
  · simp [hb.left_left]
  · simp [hb.right_right]
  · simp [IsSymplecticFamily.left_right_self hb i]
  · simp [IsSymplecticFamily.left_right_ne hb i j hij]

theorem IsSymplecticBasis.exists_adapted_mod [Finite (MaximalSpectrum R)] {f : S →+* R}
    (hf : Surjective f) (hB : B.IsAlt) {b : Basis (l ⊕ l) S Λ} (hb : IsSymplecticBasis B b)
    {P Q : Submodule S Λ} (hIP : RingHom.ker f • ⊤ ≤ P) (hIQ : RingHom.ker f • ⊤ ≤ Q)
    (hP : ∀ x ∈ P, ∀ y ∈ P, f (B x y) = 0) (hQ : ∀ x ∈ Q, ∀ y ∈ Q, f (B x y) = 0)
    (hPQ : P ⊔ Q = ⊤) :
    ∃ c : Basis (l ⊕ l) S Λ, IsSymplecticBasis B c ∧
      (∀ x, x ∈ P ↔ ∀ i, f (c.repr x (.inr i)) = 0) ∧
      ∀ x, x ∈ Q ↔ ∀ i, f (c.repr x (.inl i)) = 0 := by
  classical
  have : RingHomSurjective f := ⟨hf⟩
  let φ : Λ →ₛₗ[f] (l ⊕ l → R) :=
    { toFun := fun x i => f (b.repr x i)
      map_add' := fun x y => by ext; simp
      map_smul' := fun a x => by ext; simp }
  have hφ : ∀ x y, standardAltForm (fun _ : l => (1 : R)) (φ x) (φ y) = f (B x y) := fun x y => by
    simp [standardAltForm_apply, hb.apply_eq_sum hB, φ]
  have hker : LinearMap.ker φ ≤ RingHom.ker f • ⊤ := fun x hx => by
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem_smul (congrFun hx i) Submodule.mem_top
  have hsurj : Surjective φ := fun y => by
    choose z hz using fun i => hf (y i)
    exact ⟨∑ i, z i • b i, funext fun i => (congrArg f (congrFun (b.repr_sum_self z) i)).trans (hz i)⟩
  have hmem : ∀ {T : Submodule S Λ}, RingHom.ker f • ⊤ ≤ T → ∀ x, φ x ∈ T.map φ ↔ x ∈ T :=
    fun hT x => by
      rw [← Submodule.mem_comap, Submodule.comap_map_eq, sup_eq_left.2 (hker.trans hT)]
  obtain ⟨c, hc, -, -, h₁, h₂⟩ := hb.exists_lift_adapted hf hB (isAlt_standardAltForm _) φ
    (isSymplecticBasisOfType_standardAltForm fun _ : l => (1 : R))
    (fun i => by ext j; simp [φ, Finsupp.single_apply, Pi.single_apply, eq_comm])
    (P := P.map φ) (Q := Q.map φ)
    (by rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩; rw [hφ, hP x hx y hy])
    (by rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩; rw [hφ, hQ x hx y hy])
    (by rw [← Submodule.map_sup, hPQ, Submodule.map_top, LinearMap.range_eq_top.2 hsurj])
  exact ⟨c, hc, fun x => by rw [← h₁, hmem hIP], fun x => by rw [← h₂, hmem hIQ]⟩

end Reduction

section Int

open TensorProduct

theorem specialLinearGroup_map_zmod_surjective (n : Type*) [Fintype n] [DecidableEq n] (N : ℕ) :
    Surjective (SpecialLinearGroup.map (n := n) (Int.castRingHom (ZMod N))) := by
  rcases eq_or_ne N 0 with rfl | hN
  · exact fun A => ⟨A, Subtype.ext (Matrix.ext fun _ _ => rfl)⟩
  · have : NeZero N := ⟨hN⟩
    exact specialLinearGroup_map_surjective (ZMod.ringHom_surjective _)

theorem symplecticGroupMap_zmod_surjective (l : Type*) [Fintype l] [DecidableEq l] (N : ℕ) :
    Surjective (symplecticGroupMap l (Int.castRingHom (ZMod N))) := by
  rcases eq_or_ne N 0 with rfl | hN
  · exact fun A => ⟨A, Subtype.ext (Matrix.ext fun _ _ => rfl)⟩
  · have : NeZero N := ⟨hN⟩
    exact symplecticGroupMap_surjective (ZMod.ringHom_surjective _)

variable {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  {B : LinearMap.BilinForm ℤ Λ}

theorem exists_isSymplecticBasis_adapted_dvd (hB : B.IsAlt) (hp : Bijective B) {g : ℕ}
    (hg : finrank ℤ Λ = 2 * g) {N : ℕ} (hN : N ≠ 0) {P Q : Submodule ℤ Λ}
    (hNP : ∀ x, (N : ℤ) • x ∈ P) (hNQ : ∀ x, (N : ℤ) • x ∈ Q)
    (hP : ∀ x ∈ P, ∀ y ∈ P, (N : ℤ) ∣ B x y) (hQ : ∀ x ∈ Q, ∀ y ∈ Q, (N : ℤ) ∣ B x y)
    (hPQ : P ⊔ Q = ⊤) :
    ∃ c : Basis (Fin g ⊕ Fin g) ℤ Λ, IsSymplecticBasis B c ∧
      (∀ x, x ∈ P ↔ ∀ i, (N : ℤ) ∣ c.repr x (.inr i)) ∧
      ∀ x, x ∈ Q ↔ ∀ i, (N : ℤ) ∣ c.repr x (.inl i) := by
  have : NeZero N := ⟨hN⟩
  obtain ⟨b, hb⟩ := exists_isSymplecticBasis_of_finrank hB hp hg
  have key : ∀ {T : Submodule ℤ Λ}, (∀ x, (N : ℤ) • x ∈ T) →
      RingHom.ker (Int.castRingHom (ZMod N)) • ⊤ ≤ T := fun hT =>
    Submodule.smul_le.2 fun r hr x _ => by
      obtain ⟨k, rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd r N).1 hr
      rw [mul_smul]
      exact hT _
  simpa only [eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] using
    hb.exists_adapted_mod (f := Int.castRingHom (ZMod N)) (ZMod.ringHom_surjective _) hB
      (key hNP) (key hNQ)
      (by simpa only [eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] using hP)
      (by simpa only [eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] using hQ) hPQ

end Int

end GlobalTheory
