import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.InertPrimesSquareNormOfGeneral

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.GramProductBounds

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Minors

variable {K : Type} [Field K]

theorem sum_castLE {n l : ℕ} (hl : l ≤ n) (g : Fin n → K) (hg : ∀ k : Fin n, l ≤ k.val → g k = 0) :
    ∑ k, g k = ∑ k' : Fin l, g (Fin.castLE hl k') := by
  symm
  rw [show (∑ k' : Fin l, g (Fin.castLE hl k')) = ∑ k ∈ Finset.univ.map (Fin.castLEEmb hl), g k by
    rw [Finset.sum_map]; rfl]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k _ hk
  apply hg
  by_contra h
  push Not at h
  exact hk (Finset.mem_map.2 ⟨⟨k.val, h⟩, Finset.mem_univ _, Fin.ext rfl⟩)

theorem submatrix_triple_mul_of_triangular {n l : ℕ} (hl : l ≤ n) (A Z B : Matrix (Fin n) (Fin n) K)
    (hA : ∀ a b : Fin n, a < b → A a b = 0) (hB : ∀ a b : Fin n, b < a → B a b = 0) :
    (A * Z * B).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      A.submatrix (Fin.castLE hl) (Fin.castLE hl) * Z.submatrix (Fin.castLE hl) (Fin.castLE hl) *
        B.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [sum_castLE hl]
  · refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
    rw [sum_castLE hl]
    intro k hk
    rw [hA _ _ (Fin.lt_def.2 (by simp only [Fin.val_castLE]; omega)), zero_mul]
  · intro m hm
    rw [hB _ _ (Fin.lt_def.2 (by simp only [Fin.val_castLE]; omega)), mul_zero]

theorem lead_ZEquiv {E : Type} [Field E] [NumberField E] {n : ℕ} {Z Z₂ : Matrix (Fin n) (Fin n) E}
    (h : ZEquiv Z Z₂) (l : ℕ) : leadMinorE Z₂ l = leadMinorE Z l := by
  obtain ⟨A, B, hA0, hA1, hB0, hB1, rfl⟩ := h
  unfold leadMinorE
  split_ifs with hl
  · rw [submatrix_triple_mul_of_triangular hl _ _ _ (fun a b hab => by simp [hA0 a b hab]) (fun a b hab => by simp [hB0 a b hab]),
      Matrix.det_mul, Matrix.det_mul]
    have h1 : ((A.map (fun x : 𝓞 E => (x : E))).submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
      rw [Matrix.det_of_isLowerTriangular]
      · simp [hA1]
      · intro i j hij
        have hij' : i < j := hij
        have h0 : A (Fin.castLE hl i) (Fin.castLE hl j) = 0 :=
          hA0 _ _ (Fin.lt_def.2 (by simp only [Fin.val_castLE]; exact Fin.lt_def.1 hij'))
        simp [h0]
    have h2 : ((B.map (fun x : 𝓞 E => (x : E))).submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
      rw [Matrix.det_of_isUpperTriangular]
      · simp [hB1]
      · intro i j hij
        have hij' : j < i := hij
        have h0 : B (Fin.castLE hl i) (Fin.castLE hl j) = 0 :=
          hB0 _ _ (Fin.lt_def.2 (by simp only [Fin.val_castLE]; exact Fin.lt_def.1 hij'))
        simp [h0]
    rw [h1, h2, one_mul, mul_one]
  · rfl

end Minors

section Class

variable (D : D7) (u u' : D.what₂.Word)

theorem absDl_ZEquiv {Z Z₂ : GramM D} (h : ZEquiv Z Z₂) (l : ℕ) (τ : D.what₂.Tau) :
    Cnt.absDl D Z₂ l τ = Cnt.absDl D Z l τ := by
  unfold Cnt.absDl
  rw [lead_ZEquiv h]

theorem Gz_ZEquiv {Z Z₂ : GramM D} (h : ZEquiv Z Z₂) (T T' : ℝ) (τ : D.what₂.Tau) :
    Cnt.Gz D T T' Z₂ τ = Cnt.Gz D T T' Z τ := by
  unfold Cnt.Gz
  rw [absDl_ZEquiv D h, absDl_ZEquiv D h]

theorem gram_product_equiv_invariant {Z Z₂ : GramM D} (h : ZEquiv Z Z₂) : localGramProduct D u u' Z₂ = localGramProduct D u u' Z := by
  unfold localGramProduct
  simp only [Gz_ZEquiv D h]

end Class

end Formalism.MainNotions.GramProductBounds

end
