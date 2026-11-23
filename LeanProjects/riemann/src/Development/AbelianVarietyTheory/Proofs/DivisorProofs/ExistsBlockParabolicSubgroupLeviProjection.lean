import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin.BlockPar

variable {F : Type} [Field F] {a b : ℕ}

def sm (M : Matrix (Fin (a + b)) (Fin (a + b)) F) : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) F :=
  M.submatrix finSumFinEquiv finSumFinEquiv

theorem tl_eq (M : Matrix (Fin (a + b)) (Fin (a + b)) F) : tl a M = (sm M).toBlocks₁₁ := by
  ext i j
  have hi : (i : ℕ) < a + b := by omega
  have hj : (j : ℕ) < a + b := by omega
  simp only [tl, ent, hi, hj, and_self, dif_pos, sm, Matrix.toBlocks₁₁, Matrix.of_apply,
    Matrix.submatrix_apply, finSumFinEquiv_apply_left]
  rfl

theorem br_eq (M : Matrix (Fin (a + b)) (Fin (a + b)) F) : br a b M = (sm M).toBlocks₂₂ := by
  ext i j
  have hi : a + (i : ℕ) < a + b := by omega
  have hj : a + (j : ℕ) < a + b := by omega
  simp only [br, ent, hi, hj, and_self, dif_pos, sm, Matrix.toBlocks₂₂, Matrix.of_apply,
    Matrix.submatrix_apply, finSumFinEquiv_apply_right]
  rfl

theorem inPar_iff (x : GL (Fin (a + b)) F) :
    InPar a x ↔ (sm (x : Matrix (Fin (a + b)) (Fin (a + b)) F)).toBlocks₂₁ = 0 := by
  constructor
  · intro h
    ext i j
    simp only [sm, Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.submatrix_apply, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, Matrix.zero_apply]
    apply h <;> simp
  · intro h i j hj hi
    obtain ⟨i', rfl⟩ : ∃ i' : Fin b, Fin.natAdd a i' = i :=
      ⟨⟨i - a, by omega⟩, Fin.ext (by simp; omega)⟩
    obtain ⟨j', rfl⟩ : ∃ j' : Fin a, Fin.castAdd b j' = j := ⟨⟨j, hj⟩, rfl⟩
    have := congrFun (congrFun h i') j'
    simpa [sm, Matrix.toBlocks₂₁] using this

theorem sm_eq {M : Matrix (Fin (a + b)) (Fin (a + b)) F} (h : (sm M).toBlocks₂₁ = 0) :
    sm M = Matrix.fromBlocks (tl a M) (sm M).toBlocks₁₂ 0 (br a b M) := by
  rw [tl_eq, br_eq, ← h, Matrix.fromBlocks_toBlocks]

theorem sm_mul (M N : Matrix (Fin (a + b)) (Fin (a + b)) F) : sm (M * N) = sm M * sm N :=
  (Matrix.submatrix_mul_equiv M N _ _ _).symm

theorem mul_blocks {M N : Matrix (Fin (a + b)) (Fin (a + b)) F} (hM : (sm M).toBlocks₂₁ = 0)
    (hN : (sm N).toBlocks₂₁ = 0) :
    (sm (M * N)).toBlocks₂₁ = 0 ∧ tl a (M * N) = tl a M * tl a N ∧ br a b (M * N) = br a b M * br a b N := by
  have e : sm (M * N) = Matrix.fromBlocks (tl a M * tl a N)
      (tl a M * (sm N).toBlocks₁₂ + (sm M).toBlocks₁₂ * br a b N) 0 (br a b M * br a b N) := by
    rw [sm_mul, sm_eq hM, sm_eq hN, Matrix.fromBlocks_multiply]
    simp
  refine ⟨by rw [e, Matrix.toBlocks_fromBlocks₂₁], ?_, ?_⟩
  · rw [tl_eq (M * N), e, Matrix.toBlocks_fromBlocks₁₁]
  · rw [br_eq (M * N), e, Matrix.toBlocks_fromBlocks₂₂]

theorem det_eq {M : Matrix (Fin (a + b)) (Fin (a + b)) F} (h : (sm M).toBlocks₂₁ = 0) :
    M.det = (tl a M).det * (br a b M).det := by
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M]
  change (sm M).det = _
  rw [sm_eq h, Matrix.det_fromBlocks_zero₂₁]

theorem charpoly_eq {M : Matrix (Fin (a + b)) (Fin (a + b)) F} (h : (sm M).toBlocks₂₁ = 0) :
    M.charpoly = (tl a M).charpoly * (br a b M).charpoly := by
  rw [← Matrix.charpoly_reindex finSumFinEquiv.symm M]
  have : Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm M = sm M := by
    rw [Matrix.reindex_apply, Equiv.symm_symm]; rfl
  rw [this, sm_eq h, Matrix.charpoly_fromBlocks_zero₂₁]

theorem toG_val {m : ℕ} {M : Matrix (Fin m) (Fin m) F} (h : IsUnit M) : ((toG M : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = M := by
  unfold toG; rw [dif_pos h]; rfl

theorem units_of_par (x : GL (Fin (a + b)) F) (h : InPar a x) :
    IsUnit (tl a (x : Matrix (Fin (a + b)) (Fin (a + b)) F)) ∧ IsUnit (br a b (x : Matrix (Fin (a + b)) (Fin (a + b)) F)) := by
  have hu : IsUnit (x : Matrix (Fin (a + b)) (Fin (a + b)) F).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 x.isUnit
  rw [det_eq ((inPar_iff x).1 h)] at hu
  exact ⟨(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_left hu),
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right hu)⟩

theorem inPar_inv (x : GL (Fin (a + b)) F) (h : InPar a x) : InPar a x⁻¹ := by
  let β : Fin (a + b) → Bool := fun i => decide (a ≤ (i : ℕ))
  have hb : (x : Matrix (Fin (a + b)) (Fin (a + b)) F).BlockTriangular β := by
    intro i j hij
    rw [Bool.lt_iff] at hij
    simp only [β, decide_eq_false_iff_not, decide_eq_true_eq, not_le] at hij
    exact h i j hij.1 hij.2
  haveI := x.invertible
  have hb' := Matrix.blockTriangular_inv_of_blockTriangular hb
  intro i j hj hi
  rw [Matrix.coe_units_inv]
  exact hb' (by rw [Bool.lt_iff]; simp [β]; omega)

theorem block_par : ∀ (F : Type) [Field F] (a b n : ℕ), n = a + b → ∃ (H : Subgroup (GL (Fin n) F)) (π : H →* GL (Fin a) F × GL (Fin b) F), (∀ x, x ∈ H ↔ InPar a x) ∧ Function.Surjective π ∧ (∀ p : H, π p = (tlG a p.1, brG a b p.1)) ∧ (∀ p : H, ((π p).1 : Matrix (Fin a) (Fin a) F) = tl a (p.1 : Matrix (Fin n) (Fin n) F) ∧ ((π p).2 : Matrix (Fin b) (Fin b) F) = br a b (p.1 : Matrix (Fin n) (Fin n) F)) ∧ ∀ p : H, Matrix.charpoly (p.1 : Matrix (Fin n) (Fin n) F) = Matrix.charpoly ((π p).1 : Matrix (Fin a) (Fin a) F) * Matrix.charpoly ((π p).2 : Matrix (Fin b) (Fin b) F) := by
  intro F _ a b n hn
  subst hn
  let H : Subgroup (GL (Fin (a + b)) F) :=
    { carrier := {x | InPar a x}
      one_mem' := by
        intro i j hj hi
        rw [Units.val_one, Matrix.one_apply_ne]
        intro e; subst e; omega
      mul_mem' := by
        intro x y hx hy
        exact (inPar_iff _).2 (mul_blocks ((inPar_iff x).1 hx) ((inPar_iff y).1 hy)).1
      inv_mem' := fun {x} hx => inPar_inv x hx }
  have hH : ∀ x, x ∈ H ↔ InPar a x := fun _ => Iff.rfl
  have hpar : ∀ p : H, (sm ((p.1 : GL (Fin (a + b)) F) : Matrix (Fin (a + b)) (Fin (a + b)) F)).toBlocks₂₁ = 0 :=
    fun p => (inPar_iff _).1 p.2
  have hval : ∀ p : H, ((tlG a p.1 : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = tl a (p.1 : Matrix (Fin (a + b)) (Fin (a + b)) F) ∧
      ((brG a b p.1 : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) = br a b (p.1 : Matrix (Fin (a + b)) (Fin (a + b)) F) :=
    fun p => ⟨toG_val (units_of_par _ p.2).1, toG_val (units_of_par _ p.2).2⟩
  let π : H →* GL (Fin a) F × GL (Fin b) F :=
    MonoidHom.mk' (fun p => (tlG a p.1, brG a b p.1)) (by
      intro p q
      have hm := mul_blocks (hpar p) (hpar q)
      refine Prod.ext (Units.ext ?_) (Units.ext ?_)
      · change ((tlG a (p * q).1 : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = ((tlG a p.1 : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) * ((tlG a q.1 : GL (Fin a) F) : Matrix (Fin a) (Fin a) F)
        rw [(hval (p * q)).1, (hval p).1, (hval q).1]
        exact hm.2.1
      · change ((brG a b (p * q).1 : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) = ((brG a b p.1 : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) * ((brG a b q.1 : GL (Fin b) F) : Matrix (Fin b) (Fin b) F)
        rw [(hval (p * q)).2, (hval p).2, (hval q).2]
        exact hm.2.2)
  have hπ : ∀ p : H, π p = (tlG a p.1, brG a b p.1) := fun _ => rfl
  refine ⟨H, π, hH, ?_, hπ, fun p => hval p, fun p => ?_⟩
  · rintro ⟨u, v⟩
    let M : Matrix (Fin (a + b)) (Fin (a + b)) F :=
      (Matrix.fromBlocks (u : Matrix (Fin a) (Fin a) F) 0 0 (v : Matrix (Fin b) (Fin b) F)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm
    have hsm : sm M = Matrix.fromBlocks (u : Matrix (Fin a) (Fin a) F) 0 0 (v : Matrix (Fin b) (Fin b) F) := by
      simp only [sm, M, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id]
    have h21 : (sm M).toBlocks₂₁ = 0 := by rw [hsm, Matrix.toBlocks_fromBlocks₂₁]
    have htl : tl a M = u := by rw [tl_eq, hsm, Matrix.toBlocks_fromBlocks₁₁]
    have hbr : br a b M = v := by rw [br_eq, hsm, Matrix.toBlocks_fromBlocks₂₂]
    have hu : IsUnit M := by
      rw [Matrix.isUnit_iff_isUnit_det, det_eq h21, htl, hbr]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 u.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).1 v.isUnit)
    have hmem : hu.unit ∈ H := by
      rw [hH, inPar_iff]
      exact h21
    refine ⟨⟨hu.unit, hmem⟩, ?_⟩
    have hv := hval ⟨hu.unit, hmem⟩
    simp only [IsUnit.unit_spec] at hv
    rw [hπ]
    refine Prod.ext (Units.ext ?_) (Units.ext ?_)
    · exact hv.1.trans htl
    · exact hv.2.trans hbr
  · rw [hπ, (hval p).1, (hval p).2]
    exact charpoly_eq (hpar p)

end GlobalTheory.Shin.BlockPar
