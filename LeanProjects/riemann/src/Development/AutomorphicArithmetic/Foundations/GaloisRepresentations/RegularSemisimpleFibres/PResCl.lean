import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat

noncomputable section

open GlobalTheory.Shin

namespace UpperTheory.Gal.InertialTypesAlt

section Blocks

variable {F : Type} [Field F] {a b : ℕ}

private def blk (M : Matrix (Fin (a + b)) (Fin (a + b)) F) :
    Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) F :=
  M.submatrix finSumFinEquiv finSumFinEquiv

private theorem blk_mul (M N : Matrix (Fin (a + b)) (Fin (a + b)) F) :
    blk (M * N) = blk M * blk N :=
  (Matrix.submatrix_mul_equiv M N _ _ _).symm

private theorem tl_eq (M : Matrix (Fin (a + b)) (Fin (a + b)) F) :
    tl a M = (blk M).toBlocks₁₁ := by
  ext i j
  have hi : (i : ℕ) < a + b := by omega
  have hj : (j : ℕ) < a + b := by omega
  simp [tl, ent, blk, Matrix.toBlocks₁₁, hi, hj]
  rfl

private theorem br_eq (M : Matrix (Fin (a + b)) (Fin (a + b)) F) :
    br a b M = (blk M).toBlocks₂₂ := by
  ext i j
  simp [br, ent, blk, Matrix.toBlocks₂₂]
  rfl

private theorem inPar_iff (x : GL (Fin (a + b)) F) :
    InPar a x ↔ (blk (x : Matrix (Fin (a + b)) (Fin (a + b)) F)).toBlocks₂₁ = 0 := by
  constructor
  · intro h
    ext i j
    exact h _ _ (by simp) (by simp)
  · intro h i j hj hi
    obtain ⟨i', rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j', rfl⟩ := finSumFinEquiv.surjective j
    rcases j' with j' | j'
    · rcases i' with i' | i'
      · simp at hi; omega
      · exact congrFun (congrFun h i') j'
    · simp at hj

private def dg (a : ℕ) (z : GL (Fin b) F) : GL (Fin (a + b)) F where
  val := (Matrix.fromBlocks 1 0 0 (z : Matrix (Fin b) (Fin b) F)).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm
  inv := (Matrix.fromBlocks 1 0 0 ((z⁻¹ : GL (Fin b) F) : Matrix (Fin b) (Fin b) F)).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm
  val_inv := by
    rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp
  inv_val := by
    rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp

private theorem blk_conj (z : GL (Fin b) F) (p : GL (Fin (a + b)) F) :
    blk (((dg a z)⁻¹ * p * dg a z : GL (Fin (a + b)) F) : Matrix (Fin (a + b)) (Fin (a + b)) F) =
      Matrix.fromBlocks (blk (p : Matrix (Fin (a + b)) (Fin (a + b)) F)).toBlocks₁₁
        ((blk (p : Matrix (Fin (a + b)) (Fin (a + b)) F)).toBlocks₁₂ * (z : Matrix (Fin b) (Fin b) F))
        (((z⁻¹ : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) *
          (blk (p : Matrix (Fin (a + b)) (Fin (a + b)) F)).toBlocks₂₁)
        (((z⁻¹ : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) *
          (blk (p : Matrix (Fin (a + b)) (Fin (a + b)) F)).toBlocks₂₂ *
            (z : Matrix (Fin b) (Fin b) F)) := by
  have h1 : blk (((dg a z)⁻¹ : GL (Fin (a + b)) F) : Matrix (Fin (a + b)) (Fin (a + b)) F) =
      Matrix.fromBlocks 1 0 0 ((z⁻¹ : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) := by
    ext i j
    simp [blk, dg, Units.inv_mk]
  have h2 : blk ((dg a z : GL (Fin (a + b)) F) : Matrix (Fin (a + b)) (Fin (a + b)) F) =
      Matrix.fromBlocks 1 0 0 (z : Matrix (Fin b) (Fin b) F) := by
    ext i j
    simp [blk, dg]
  rw [Units.val_mul, Units.val_mul, blk_mul, blk_mul, h1, h2,
    ← Matrix.fromBlocks_toBlocks (blk (p : Matrix (Fin (a + b)) (Fin (a + b)) F))]
  simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, Matrix.fromBlocks_multiply]
  simp

private theorem toG_conj (z : GL (Fin b) F) (M : Matrix (Fin b) (Fin b) F) :
    toG (((z⁻¹ : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) * M * (z : Matrix (Fin b) (Fin b) F)) =
      z⁻¹ * toG M * z := by
  by_cases h : IsUnit M
  · have h' : IsUnit (((z⁻¹ : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) * M *
        (z : Matrix (Fin b) (Fin b) F)) :=
      ((Units.isUnit _).mul h).mul (Units.isUnit _)
    apply Units.ext
    simp [toG, h, h']
  · have h' : ¬ IsUnit (((z⁻¹ : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) * M *
        (z : Matrix (Fin b) (Fin b) F)) := by
      intro hu
      apply h
      have : M = (z : Matrix (Fin b) (Fin b) F) *
          (((z⁻¹ : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) * M * (z : Matrix (Fin b) (Fin b) F)) *
            ((z⁻¹ : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) := by
        simp [mul_assoc]
      rw [this]
      exact ((Units.isUnit _).mul hu).mul (Units.isUnit _)
    simp [toG, h, h']

private theorem inPar_conj (z : GL (Fin b) F) (p : GL (Fin (a + b)) F) :
    InPar a ((dg a z)⁻¹ * p * dg a z) ↔ InPar a p := by
  rw [inPar_iff, inPar_iff, blk_conj, Matrix.toBlocks_fromBlocks₂₁]
  constructor
  · intro h
    have := congrArg (fun X => (z : Matrix (Fin b) (Fin b) F) * X) h
    simpa [← mul_assoc] using this
  · intro h
    rw [h]
    exact Matrix.mul_zero _

private theorem tlG_conj (z : GL (Fin b) F) (p : GL (Fin (a + b)) F) :
    tlG a ((dg a z)⁻¹ * p * dg a z) = tlG a p := by
  unfold tlG
  rw [tl_eq, tl_eq, blk_conj, Matrix.toBlocks_fromBlocks₁₁]

private theorem brG_conj (z : GL (Fin b) F) (p : GL (Fin (a + b)) F) :
    brG a b ((dg a z)⁻¹ * p * dg a z) = z⁻¹ * brG a b p * z := by
  unfold brG
  rw [br_eq, br_eq, blk_conj, Matrix.toBlocks_fromBlocks₂₂, toG_conj]

end Blocks

theorem resCl : ResCl := by
  intro F _ _ a b n hn T hT x y z
  subst hn
  unfold resT
  rw [← finsum_comp_equiv (MulAut.conj (dg a z)⁻¹).toEquiv]
  refine finsum_congr fun p => ?_
  have e : (MulAut.conj (dg a z)⁻¹).toEquiv p = (dg a z)⁻¹ * p * dg a z := by
    show (dg a z)⁻¹ * p * ((dg a z)⁻¹)⁻¹ = _
    rw [inv_inv]
  rw [e, inPar_conj, tlG_conj, brG_conj, hT]
  have : z⁻¹ * brG a b p * z = z⁻¹ * y * z ↔ brG a b p = y := by
    simp
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd ⟨h1.1, h1.2.1, this.1 h1.2.2⟩ h2
  · exact absurd ⟨h2.1, h2.2.1, this.2 h2.2.2⟩ h1
  · rfl

end UpperTheory.Gal.InertialTypesAlt
