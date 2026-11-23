import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

section SlopeTestRemainingChoices

open UpperTheory.V.Af.Fin GroundTheory.Automorphic.AutomorphicForm

private theorem cn_ne {r s : ℕ} (i : Fin r) (j : Fin s) : Fin.castAdd s i ≠ Fin.natAdd r j := fun h => by
  have := congrArg Fin.val h
  simp at this
  omega

private theorem block_embedding_first_val {R : Type} [CommRing R] {r s : ℕ} (m : GL (Fin r) R) :
    (emb (e1 r s) m).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks m.val 0 0 1) := by
  ext i j
  rw [coe_emb, Matrix.add_apply]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · have := matrixExtendByZero_apply (e1 r s) (m.val - 1) i j
    simp only [orderedCechToCatCochainsOne_apply_valueAtSubset] at this
    rw [this]
    simp [Matrix.one_apply]
  · rw [matrixExtendByZero_apply_of_outside_col _ _ _ fun k => (cn_ne k j).symm]
    simp [Matrix.one_apply_ne (cn_ne i j)]
  · rw [extendByZero_apply_eq_zero_of_row_not_mem _ _ fun k => (cn_ne k i).symm]
    simp [Matrix.one_apply_ne (cn_ne j i).symm]
  · rw [extendByZero_apply_eq_zero_of_row_not_mem _ _ fun k => (cn_ne k i).symm]
    simp [Matrix.one_apply]

private theorem block_embedding_second_val {R : Type} [CommRing R] {r s : ℕ} (m : GL (Fin s) R) :
    (emb (e2 r s) m).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 0 0 m.val) := by
  ext i j
  rw [coe_emb, Matrix.add_apply]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [extendByZero_apply_eq_zero_of_row_not_mem _ _ fun k => (cn_ne i k)]
    simp [Matrix.one_apply]
  · rw [extendByZero_apply_eq_zero_of_row_not_mem _ _ fun k => (cn_ne i k)]
    simp [Matrix.one_apply_ne (cn_ne i j)]
  · rw [matrixExtendByZero_apply_of_outside_col _ _ _ fun k => (cn_ne j k)]
    simp [Matrix.one_apply_ne (cn_ne j i).symm]
  · have := matrixExtendByZero_apply (e2 r s) (m.val - 1) i j
    simp only [alternatingToOrderedCechDegreeTwo_apply_valueAtSubset] at this
    rw [this]
    simp [Matrix.one_apply]

private theorem unip_val {R : Type} [CommRing R] {r s : ℕ} (Y : Matrix (Fin r) (Fin s) R) :
    ∃ X : UPos (r + s) r → R,
      unipMatrix X = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 Y 0 1) := by
  refine ⟨fun p => Y ⟨p.1.1, p.2.1⟩ ⟨p.1.2 - r, by have := p.2.2; have := p.1.2.2; omega⟩, ?_⟩
  ext i j
  rw [unipMatrix, Matrix.add_apply, blockEntry_apply]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp [Matrix.one_apply]
  · simp [Matrix.one_apply_ne (cn_ne i j)]
  · simp [Matrix.one_apply_ne (cn_ne j i).symm]
  · simp [Matrix.one_apply]

private theorem block_form {R : Type} [CommRing R] {r s : ℕ} (b : GL (Fin (r + s)) R) (m₁ : GL (Fin r) R)
    (m₂ : GL (Fin s) R) (h₁ : ∀ i j, b.val (Fin.castAdd s i) (Fin.castAdd s j) = m₁.val i j)
    (h₂ : ∀ i j, b.val (Fin.natAdd r i) (Fin.natAdd r j) = m₂.val i j)
    (h₀ : ∀ i j, b.val (Fin.natAdd r i) (Fin.castAdd s j) = 0) :
    ∃ X : UPos (r + s) r → R, b = unipGL X * blk m₁ m₂ := by
  let B : Matrix (Fin r) (Fin s) R := b.val.submatrix (Fin.castAdd s) (Fin.natAdd r)
  have hb' : b.val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks m₁.val B 0 m₂.val) := by
    ext i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [h₁]
    · simp [B]
    · simp [h₀]
    · simp [h₂]
  obtain ⟨X, hX⟩ := unip_val (B * (m₂⁻¹).val)
  refine ⟨X, Units.ext ?_⟩
  rw [blk, Units.val_mul, Units.val_mul, coe_unipGL, hX, block_embedding_first_val, block_embedding_second_val, hb']
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [Matrix.mul_assoc]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Cj.S.matBlock :
    UpperTheory.V.Cj.S.MatBlock := by
  intro L _ O r s π hπ S c
  refine block_form _ _ _ (fun i j => ?_) (fun i j => ?_) fun i j => ?_
  · have hm : ∀ k, k ∈ sub1 S ↔ Fin.castAdd s k ∈ S := fun k => by simp [sub1]
    have hN : satakeN O S c (Fin.castAdd s i) (Fin.castAdd s j) = satakeN O (sub1 S) (c ∘ pair1 S) i j := by
      unfold satakeN
      by_cases h : i ∈ sub1 S ∧ j ∉ sub1 S ∧ i < j
      · rw [dif_pos h, dif_pos ⟨(hm i).1 h.1, fun h' => h.2.1 ((hm j).2 h'), h.2.2⟩]
        rfl
      · rw [dif_neg h, dif_neg fun h' => h ⟨(hm i).2 h'.1, fun h'' => h'.2.1 ((hm j).1 h''), h'.2.2⟩]
    rw [satakeGL_apply, satakeGL_apply, hN]
    simp [Matrix.one_apply, hm]
  · have hm : ∀ k, k ∈ sub2 S ↔ Fin.natAdd r k ∈ S := fun k => by simp [sub2]
    have hN : satakeN O S c (Fin.natAdd r i) (Fin.natAdd r j) = satakeN O (sub2 S) (c ∘ pair2 S) i j := by
      unfold satakeN
      by_cases h : i ∈ sub2 S ∧ j ∉ sub2 S ∧ i < j
      · rw [dif_pos h, dif_pos ⟨(hm i).1 h.1, fun h' => h.2.1 ((hm j).2 h'), Nat.add_lt_add_left h.2.2 r⟩]
        rfl
      · rw [dif_neg h, dif_neg fun h' => h ⟨(hm i).2 h'.1, fun h'' => h'.2.1 ((hm j).1 h''),
          Nat.lt_of_add_lt_add_left h'.2.2⟩]
    rw [satakeGL_apply, satakeGL_apply, hN]
    simp [Matrix.one_apply, hm]
  · apply satakeGL_lower
    change (Fin.castAdd s j).val < (Fin.natAdd r i).val
    simp
    omega
