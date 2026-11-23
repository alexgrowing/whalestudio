import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ActLPos

noncomputable section

open TensorProduct

namespace PositivityTheory.KB.NaturalTheta

section

variable (G : Type) [Group G]

def bdZ (m : ℕ) : ((Fin (m + 1) → G) →₀ ℤ) →ₗ[ℤ] ((Fin m → G) →₀ ℤ) :=
  Finsupp.linearCombination ℤ fun g =>
    Finsupp.single (fun i => g i.succ) 1 +
      ∑ j : Fin (m + 1), ((-1 : ℤ) ^ ((j : ℕ) + 1)) • Finsupp.single (Fin.contractNth j (· * ·) g) 1

theorem bdZ_single (m : ℕ) (g : Fin (m + 1) → G) (a : ℤ) :
    bdZ G m (Finsupp.single g a) = Finsupp.single (fun i => g i.succ) a +
      ∑ j : Fin (m + 1),
        Finsupp.single (Fin.contractNth j (· * ·) g) ((-1 : ℤ) ^ ((j : ℕ) + 1) * a) := by
  simp only [bdZ, Finsupp.linearCombination_single, smul_add, Finset.smul_sum, Finsupp.smul_single,
    smul_eq_mul, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

def eC (n : ℕ) : ℝ ⊗[ℤ] ((Fin n → G) →₀ ℤ) ≃ₗ[ℝ] Chn G n :=
  letI := Classical.decEq (Fin n → G)
  TensorProduct.finsuppScalarRight ℤ ℝ ℝ (Fin n → G)

omit [Group G] in
theorem eC_single (n : ℕ) (r : ℝ) (g : Fin n → G) (a : ℤ) :
    eC G n (r ⊗ₜ Finsupp.single g a) = Finsupp.single g ((a : ℝ) * r) := by
  letI := Classical.decEq (Fin n → G)
  ext i
  rw [eC, TensorProduct.finsuppScalarRight_apply_tmul_apply, zsmul_eq_mul]
  by_cases h : g = i
  · subst h; simp
  · simp [h]

theorem bd_eC (m : ℕ) :
    bd G m ∘ₗ (eC G (m + 1)).toLinearMap = (eC G m).toLinearMap ∘ₗ (bdZ G m).baseChange ℝ := by
  refine TensorProduct.AlgebraTensorModule.ext fun r x => ?_
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, tmul_add,
      map_add] at hx hy ⊢
    rw [hx, hy]
  | single g a =>
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.baseChange_tmul, eC_single, bdZ_single, tmul_add, tmul_sum, map_add, map_sum,
      bd, Finsupp.linearCombination_single, smul_add, Finset.smul_sum, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    congr 1 <;> (try funext j) <;> congr 1 <;> push_cast <;> ring

theorem cmap_eC {H : Type} [Group H] (f : G →* H) (n : ℕ) :
    cmap f n ∘ₗ (eC G n).toLinearMap =
      (eC H n).toLinearMap ∘ₗ
        (Finsupp.lmapDomain ℤ ℤ (fun (g : Fin n → G) i => f (g i))).baseChange ℝ := by
  refine TensorProduct.AlgebraTensorModule.ext fun r x => ?_
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, tmul_add,
      map_add] at hx hy ⊢
    rw [hx, hy]
  | single g a =>
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.baseChange_tmul, eC_single, cmap, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single]

end

end PositivityTheory.KB.NaturalTheta
