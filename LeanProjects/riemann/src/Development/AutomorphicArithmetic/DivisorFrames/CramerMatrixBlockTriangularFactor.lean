import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

private def UpperTheory.lastRowCofactor {K : Type} [Field K] {n r : ℕ} (X : Matrix (Fin n) (Fin r) K) (σ : Fin r → Fin n)
    (k : Fin r) (j : Fin ((k : ℕ) + 1)) : K :=
  (-1) ^ ((k : ℕ) + (j : ℕ)) *
    (Matrix.of fun a l : Fin (k : ℕ) => X (σ (Fin.castLE k.2.le a)) (Fin.castLE k.2 (j.succAbove l))).det

private theorem UpperTheory.colMinor_expand_last_row {K : Type} [Field K] {n r : ℕ} (X : Matrix (Fin n) (Fin r) K) (σ : Fin r → Fin n)
    (k : Fin r) (ρ : Fin n) :
    colMinor X (k + 1) k.2 (fun a => if (a : ℕ) < k then σ (Fin.castLE k.2 a) else ρ) =
      ∑ j : Fin ((k : ℕ) + 1), X ρ (Fin.castLE k.2 j) * UpperTheory.lastRowCofactor X σ k j := by
  unfold colMinor UpperTheory.lastRowCofactor
  rw [Matrix.det_succ_row _ (Fin.last (k : ℕ))]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : (Matrix.of fun a l : Fin ((k : ℕ) + 1) =>
      X (if (a : ℕ) < k then σ (Fin.castLE k.2 a) else ρ) (Fin.castLE k.2 l)).submatrix
        (Fin.last (k : ℕ)).succAbove j.succAbove =
      Matrix.of fun a l : Fin (k : ℕ) => X (σ (Fin.castLE k.2.le a)) (Fin.castLE k.2 (j.succAbove l)) := by
    ext a l
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.succAbove_last, Fin.val_castSucc, a.2, if_true]
    rfl
  rw [h]
  simp only [Matrix.of_apply, Fin.val_last, lt_irrefl, if_false]
  ring

private theorem UpperTheory.lastRowCofactor_last_eq_lead {K : Type} [Field K] {n r : ℕ} (X : Matrix (Fin n) (Fin r) K)
    (σ : Fin r → Fin n) (k : Fin r) :
    UpperTheory.lastRowCofactor X σ k (Fin.last (k : ℕ)) = lead X σ k k.2.le := by
  unfold UpperTheory.lastRowCofactor lead colMinor
  rw [Fin.val_last, Even.neg_one_pow (Even.add_self _), _root_.one_mul]
  congr 1
  ext a l
  simp only [Matrix.of_apply, Fin.succAbove_last]
  rfl

theorem UpperTheory.cramer_matrix_block_triangular_factor :
    ∀ (K : Type) [Field K] (n r : ℕ) (X : Matrix (Fin n) (Fin r) K) (σ : Fin r → Fin n), (∀ k (hk : k ≤ r), lead X σ k hk ≠ 0) → ∃ β : Matrix (Fin r) (Fin r) K, β.BlockTriangular id ∧ cram X σ = X * β ∧ (∀ i : Fin r, β i i * lead X σ ((i : ℕ) + 1) i.2 = lead X σ i i.2.le) ∧ ((cram X σ).submatrix σ id).det = 1 := by
  intro K _ n r X σ h
  refine ⟨Matrix.of fun l k => if hl : (l : ℕ) < (k : ℕ) + 1 then
      UpperTheory.lastRowCofactor X σ k ⟨l, hl⟩ / lead X σ (k + 1) k.2 else 0, ?_, ?_, ?_, ?_⟩
  · intro l k hlk
    have : (k : ℕ) < l := hlk
    rw [Matrix.of_apply, dif_neg (by omega)]
  · ext ρ k
    rw [Matrix.mul_apply, cram, Matrix.of_apply, UpperTheory.colMinor_expand_last_row, Finset.sum_div]
    refine Fintype.sum_of_injective (Fin.castLE k.2) (Fin.castLE_injective _) _ _ ?_ ?_
    · intro l hl
      rw [Matrix.of_apply, dif_neg, mul_zero]
      intro hl'
      exact hl ⟨⟨l, hl'⟩, rfl⟩
    · intro j
      have hj : ((Fin.castLE k.2 j : Fin r) : ℕ) < (k : ℕ) + 1 := j.2
      rw [Matrix.of_apply, dif_pos hj, mul_div_assoc]
      rfl
  · intro i
    rw [Matrix.of_apply, dif_pos (Nat.lt_succ_self _), div_mul_cancel₀ _ (h _ _)]
    exact UpperTheory.lastRowCofactor_last_eq_lead X σ i
  · rw [Matrix.det_of_lowerTriangular]
    · refine Finset.prod_eq_one fun k _ => ?_
      rw [Matrix.submatrix_apply, cram, Matrix.of_apply, id, div_eq_one_iff_eq (h _ _)]
      unfold lead
      congr 1
      funext a
      split_ifs with ha
      · rfl
      · congr 1
        have := a.2
        exact Fin.ext (by simp only [Fin.val_castLE]; omega)
    · intro j k hjk
      have hjk' : (j : ℕ) < k := hjk
      rw [Matrix.submatrix_apply, cram, Matrix.of_apply, id, div_eq_zero_iff]
      left
      unfold colMinor
      refine Matrix.det_zero_of_row_eq (i := ⟨j, by omega⟩) (j := Fin.last (k : ℕ)) ?_ ?_
      · intro e
        have := congrArg Fin.val e
        simp only [Fin.val_last] at this
        omega
      · funext l
        simp only [Matrix.of_apply, hjk', if_true, Fin.val_last, lt_irrefl, if_false]
        rfl
