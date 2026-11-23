import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.AdMatConjTranspose
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFockB

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

theorem fockBasis_eq (S : Finset (Fin (n * n))) :
    fockBasis n S = ExteriorAlgebra.ιMulti ℂ S.card
      (fun i => Pi.single (finProdFinEquiv.symm (S.orderEmbOfFin rfl i)) (1 : ℂ)) := by
  have hb : fockBasis n S = ExteriorAlgebra.ιMulti ℂ S.card
      (((Pi.basisFun ℂ (Fin n × Fin n)).reindex finProdFinEquiv) ∘ S.orderEmbOfFin rfl) := by
    rw [fockBasis, ExteriorAlgebra.basis_apply]
    rfl
  have hv : ((Pi.basisFun ℂ (Fin n × Fin n)).reindex finProdFinEquiv) ∘ S.orderEmbOfFin rfl =
      fun i => Pi.single (finProdFinEquiv.symm (S.orderEmbOfFin rfl i)) (1 : ℂ) := by
    funext i
    simp
  rw [hb, hv]

theorem adPhys_single (k : Matrix (Fin n) (Fin n) ℂ) (y : Fin n × Fin n) :
    adPhys ε k (Pi.single y 1) = ∑ x, adMat ε k x y • Pi.single x (1 : ℂ) := by
  funext z
  simp [adPhys, Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_apply]

theorem adPhys_diag_single (s : Fin n → ℂ) (x : Fin n × Fin n) :
    adPhys ε (Matrix.diagonal s) (Pi.single x 1) = modeChar ε s x • Pi.single x (1 : ℂ) := by
  funext y
  simp only [adPhys, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.smul_apply, smul_eq_mul]
  by_cases h : y = x
  · subst h
    by_cases hy : IsPhys ε y <;> simp [adMat, modeChar, hy]
  · simp only [h, if_false]
    obtain ⟨y1, y2⟩ := y
    obtain ⟨x1, x2⟩ := x
    simp only [adMat, Matrix.diagonal_apply]
    split_ifs <;> simp_all

theorem ff_diag (s : Fin n → ℂ) (S : Finset (Fin (n * n))) :
    ff ε (Matrix.diagonal s) (fockBasis n S) =
      (∏ m ∈ S, modeChar ε s (finProdFinEquiv.symm m)) • fockBasis n S := by
  rw [fockBasis_eq, ff, ExteriorAlgebra.map_apply_ιMulti]
  simp only [Function.comp_def, adPhys_diag_single]
  rw [AlternatingMap.map_smul_univ]
  congr 1
  conv_rhs => rw [← S.map_orderEmbOfFin_univ rfl]
  rw [Finset.prod_map]
  rfl

def adPoly (ε : Fin n → Bool) (x y : Fin n × Fin n) : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ :=
  if IsPhys ε x then
    (if IsPhys ε y then MvPolynomial.X (Sum.inl (x.1, y.1)) * MvPolynomial.X (Sum.inr (x.2, y.2)) else 0)
  else if x = y then 1 else 0

theorem eval_adPoly (k : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n × Fin n) :
    MvPolynomial.eval (Sum.elim (fun p => k p.1 p.2) (fun p => star (k p.1 p.2))) (adPoly ε x y) =
      adMat ε k x y := by
  unfold adPoly adMat
  split_ifs <;> simp

theorem ffMat_eq (k : Matrix (Fin n) (Fin n) ℂ) (S T : Finset (Fin (n * n))) :
    ffMat ε k S T = ∑ h : Fin T.card → Fin n × Fin n,
      (∏ i, adMat ε k (h i) (finProdFinEquiv.symm (T.orderEmbOfFin rfl i))) *
        (fockBasis n).repr (ExteriorAlgebra.ιMulti ℂ T.card (fun i => Pi.single (h i) (1 : ℂ))) S := by
  rw [ffMat, LinearMap.toMatrix_apply, AlgHom.toLinearMap_apply, fockBasis_eq, ff,
    ExteriorAlgebra.map_apply_ιMulti]
  simp only [Function.comp_def, adPhys_single]
  have h := (ExteriorAlgebra.ιMulti ℂ T.card).toMultilinearMap.map_sum
    (fun i x => adMat ε k x (finProdFinEquiv.symm (T.orderEmbOfFin rfl i)) • Pi.single x (1 : ℂ))
  simp only [AlternatingMap.coe_multilinearMap] at h
  rw [h, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [AlternatingMap.map_smul_univ, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem ffMat_poly (S T : Finset (Fin (n * n))) :
    ∃ P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ, ∀ k : Matrix (Fin n) (Fin n) ℂ,
      ffMat ε k S T = MvPolynomial.eval (Sum.elim (fun p => k p.1 p.2) (fun p => star (k p.1 p.2))) P := by
  refine ⟨∑ h : Fin T.card → Fin n × Fin n,
    (∏ i, adPoly ε (h i) (finProdFinEquiv.symm (T.orderEmbOfFin rfl i))) *
      MvPolynomial.C ((fockBasis n).repr (ExteriorAlgebra.ιMulti ℂ T.card (fun i => Pi.single (h i) (1 : ℂ))) S),
    fun k => ?_⟩
  rw [ffMat_eq, map_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [map_mul, map_prod, MvPolynomial.eval_C]
  simp only [eval_adPoly]

theorem ffMat_continuous (S T : Finset (Fin (n * n))) :
    Continuous fun k : Matrix (Fin n) (Fin n) ℂ => ffMat ε k S T := by
  obtain ⟨P, hP⟩ := ffMat_poly (ε := ε) S T
  simp only [hP]
  refine (MvPolynomial.continuous_eval P).comp ?_
  refine continuous_pi fun p => ?_
  rcases p with p | p
  · exact (continuous_apply p.2).comp (continuous_apply p.1)
  · exact continuous_star.comp ((continuous_apply p.2).comp (continuous_apply p.1))

end ReciprocityTheory.ChartRestriction.DS.TRGap
