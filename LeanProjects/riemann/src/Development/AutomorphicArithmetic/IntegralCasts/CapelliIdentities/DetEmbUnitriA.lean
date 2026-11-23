import Mathlib

theorem UpperTheory.Reformulated.B.Qe13.aux1 :
    ∀ (R : Type) [inst : CommRing R] (n : ℕ),
      Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) (0 : Matrix (Fin n) (Fin (1 : ℕ)) R)
          (0 : Matrix (Fin (1 : ℕ)) (Fin n) R) (1 : Matrix (Fin (1 : ℕ)) (Fin (1 : ℕ)) R) =
        (1 : Matrix (Fin n ⊕ Fin (1 : ℕ)) (Fin n ⊕ Fin (1 : ℕ)) R) := by
  intro R _ n
  exact Matrix.fromBlocks_one

theorem UpperTheory.Reformulated.B.Qe13.aux2 :
    ∀ (R : Type) [inst : CommRing R] (n : ℕ) (A B : Matrix (Fin n) (Fin n) R),
      Matrix.fromBlocks (A * B) (0 : Matrix (Fin n) (Fin (1 : ℕ)) R) (0 : Matrix (Fin (1 : ℕ)) (Fin n) R)
          (1 : Matrix (Fin (1 : ℕ)) (Fin (1 : ℕ)) R) =
        Matrix.fromBlocks A (0 : Matrix (Fin n) (Fin (1 : ℕ)) R) (0 : Matrix (Fin (1 : ℕ)) (Fin n) R)
            (1 : Matrix (Fin (1 : ℕ)) (Fin (1 : ℕ)) R) *
          Matrix.fromBlocks B (0 : Matrix (Fin n) (Fin (1 : ℕ)) R) (0 : Matrix (Fin (1 : ℕ)) (Fin n) R)
            (1 : Matrix (Fin (1 : ℕ)) (Fin (1 : ℕ)) R) := by
  intro R _ n A B
  rw [Matrix.fromBlocks_multiply]
  simp

noncomputable def UpperTheory.Reformulated.B.Qe13.blkHom :
    (R : Type) →
      [inst : CommRing R] → (n : ℕ) → Matrix (Fin n) (Fin n) R →* Matrix (Fin n ⊕ Fin (1 : ℕ)) (Fin n ⊕ Fin (1 : ℕ)) R :=
    fun (R : Type) [CommRing R] (n : ℕ) ↦
      {
        toFun := fun (A : Matrix (Fin n) (Fin n) R) ↦
          Matrix.fromBlocks A (0 : Matrix (Fin n) (Fin (1 : ℕ)) R) (0 : Matrix (Fin (1 : ℕ)) (Fin n) R)
            (1 : Matrix (Fin (1 : ℕ)) (Fin (1 : ℕ)) R),
        map_one' := UpperTheory.Reformulated.B.Qe13.aux1 R n, map_mul' := UpperTheory.Reformulated.B.Qe13.aux2 R n :
        Matrix (Fin n) (Fin n) R →* Matrix (Fin n ⊕ Fin (1 : ℕ)) (Fin n ⊕ Fin (1 : ℕ)) R }

noncomputable def UpperTheory.Reformulated.B.Qe13.embGL :
    (R : Type) → [inst : CommRing R] → (n N : ℕ) → n + (1 : ℕ) = N → GL (Fin n) R →* GL (Fin N) R :=
    fun (R : Type) [CommRing R] (n N : ℕ) (h : n + (1 : ℕ) = N) ↦
      Units.map
        ((↑(↑(Matrix.reindexAlgEquiv R R (finSumFinEquiv.trans (finCongr h))) :
                    Matrix (Fin n ⊕ Fin (1 : ℕ)) (Fin n ⊕ Fin (1 : ℕ)) R →ₐ[R] Matrix (Fin N) (Fin N) R).toRingHom :
              Matrix (Fin n ⊕ Fin (1 : ℕ)) (Fin n ⊕ Fin (1 : ℕ)) R →* Matrix (Fin N) (Fin N) R).comp
          (UpperTheory.Reformulated.B.Qe13.blkHom R n))

theorem UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A :
    ∀ {n : ℕ} (g : GL (Fin n) ℂ),
      (∀ (i j : Fin n), j < i → (↑g : Matrix (Fin n) (Fin n) ℂ) i j = (0 : ℂ)) →
        (∀ (i : Fin n), (↑g : Matrix (Fin n) (Fin n) ℂ) i i = (1 : ℂ)) →
          (Matrix.GeneralLinearGroup.det : GL (Fin (n + (1 : ℕ))) ℂ → ℂˣ)
              ((UpperTheory.Reformulated.B.Qe13.embGL ℂ n (n + (1 : ℕ)) rfl : GL (Fin n) ℂ → GL (Fin (n + (1 : ℕ))) ℂ) g) =
            (1 : ℂˣ) := by
  intro n g hlow hdiag
  have htri : (↑g : Matrix (Fin n) (Fin n) ℂ).BlockTriangular id := fun i j hij => hlow i j hij
  have hg : (↑g : Matrix (Fin n) (Fin n) ℂ).det = 1 := by
    rw [Matrix.det_of_upperTriangular htri]
    exact Finset.prod_eq_one fun i _ => hdiag i
  apply Units.ext
  change Matrix.det (Matrix.reindex (finSumFinEquiv.trans (finCongr rfl)) (finSumFinEquiv.trans (finCongr rfl))
    (Matrix.fromBlocks (↑g : Matrix (Fin n) (Fin n) ℂ) (0 : Matrix (Fin n) (Fin 1) ℂ)
      (0 : Matrix (Fin 1) (Fin n) ℂ) (1 : Matrix (Fin 1) (Fin 1) ℂ))) = 1
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, hg, Matrix.det_one, mul_one]
