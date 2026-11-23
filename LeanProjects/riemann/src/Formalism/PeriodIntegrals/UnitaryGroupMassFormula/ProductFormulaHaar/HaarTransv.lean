import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.HaarBox

noncomputable section

open ValuativeRel Module Matrix

namespace PI.ProdFormulaE.HaarBox

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {E : Type} [AddCommGroup E] [Module K E] [TopologicalSpace E] [IsModuleTopology K E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem repr_toLin (b : Basis ι K E) (A : Matrix ι ι K) (x : E) :
    b.repr (Matrix.toLin b b A x) = A *ᵥ b.repr x := by
  have h := LinearMap.toMatrix_mulVec_repr b b (Matrix.toLin b b A) x
  rw [LinearMap.toMatrix_toLin] at h
  exact h.symm

theorem transvection_mulVec (t : Matrix.TransvectionStruct ι K) (v : ι → K) (k : ι) :
    (t.toMatrix *ᵥ v) k = v k + if k = t.i then t.c * v t.j else 0 := by
  simp only [Matrix.TransvectionStruct.toMatrix, Matrix.transvection, Matrix.add_mulVec,
    Matrix.one_mulVec, Pi.add_apply, add_right_inj]
  by_cases hk : k = t.i
  · rw [if_pos hk, hk]
    simp [Matrix.mulVec, dotProduct, Matrix.single_apply, ite_mul]
  · rw [if_neg hk]
    simp [Matrix.mulVec, dotProduct, Ne.symm hk]

def tγ (t : Matrix.TransvectionStruct ι K) : ι → ValueGroupWithZero K :=
  Function.update 1 t.i (max (valuation K t.c) 1)

theorem tγ_inv (t : Matrix.TransvectionStruct ι K) : tγ t.inv = tγ t := by
  simp [tγ, Matrix.TransvectionStruct.inv, Valuation.map_neg]

private theorem tGamma_apply_of_ne (t : Matrix.TransvectionStruct ι K) {k : ι}
    (hk : k ≠ t.i) : tγ t k = 1 := by
  simp [tγ, hk]

private theorem tGamma_apply_self (t : Matrix.TransvectionStruct ι K) :
    tγ t t.i = max (valuation K t.c) 1 := by
  simp [tγ]

theorem toLin_mem_box (b : Basis ι K E) (t : Matrix.TransvectionStruct ι K) (x : E)
    (hx : x ∈ box b (tγ t)) : Matrix.toLin b b t.toMatrix x ∈ box b (tγ t) := by
  change ∀ k, valuation K (b.repr x k) ≤ tγ t k at hx
  change ∀ k, valuation K (b.repr (Matrix.toLin b b t.toMatrix x) k) ≤ tγ t k
  intro k
  have e : b.repr (Matrix.toLin b b t.toMatrix x) k
      = b.repr x k + if k = t.i then t.c * b.repr x t.j else 0 := by
    rw [congrFun (repr_toLin b t.toMatrix x) k, transvection_mulVec]
  rw [e]
  by_cases hk : k = t.i
  · rw [if_pos hk]
    have hj : valuation K (b.repr x t.j) ≤ 1 := by
      have h := hx t.j
      rwa [tGamma_apply_of_ne t t.hij.symm] at h
    have hR : tγ t k = max (valuation K t.c) 1 := by
      rw [hk]; exact tGamma_apply_self t
    have hxi : valuation K (b.repr x k) ≤ max (valuation K t.c) 1 := by
      rw [← hR]; exact hx k
    rw [hR]
    refine (Valuation.map_add _ _ _).trans (max_le hxi ?_)
    rw [Valuation.map_mul]
    calc valuation K t.c * valuation K (b.repr x t.j) ≤ valuation K t.c * 1 := by
          first
          | exact mul_le_mul_left' hj _
          | gcongr
      _ = valuation K t.c := mul_one _
      _ ≤ max (valuation K t.c) 1 := le_max_left _ _
  · rw [if_neg hk, add_zero]
    exact hx k

theorem transvection_box (b : Basis ι K E) (t : Matrix.TransvectionStruct ι K) :
    ∃ γ : ι → ValueGroupWithZero K, (∀ i, γ i ≠ 0) ∧
      Matrix.toLin b b t.toMatrix '' box b γ = box b γ := by
  refine ⟨tγ t, ?_, ?_⟩
  · intro i
    have h1 : (1 : ValueGroupWithZero K) ≤ tγ t i := by
      by_cases hi : i = t.i
      · rw [hi, tGamma_apply_self]
        exact le_max_right _ _
      · rw [tGamma_apply_of_ne t hi]
    exact (lt_of_lt_of_le zero_lt_one h1).ne'
  · apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact toLin_mem_box b t x hx
    · intro y hy
      refine ⟨Matrix.toLin b b t.inv.toMatrix y, ?_, ?_⟩
      · have h := toLin_mem_box b t.inv y (by rwa [tγ_inv])
        rwa [tγ_inv] at h
      · show ((Matrix.toLin b b t.toMatrix).comp (Matrix.toLin b b t.inv.toMatrix)) y = y
        rw [← Matrix.toLin_mul, Matrix.TransvectionStruct.mul_inv, Matrix.toLin_one,
          LinearMap.id_apply]

end PI.ProdFormulaE.HaarBox

end
