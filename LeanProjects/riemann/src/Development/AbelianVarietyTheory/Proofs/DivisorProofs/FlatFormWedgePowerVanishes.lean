import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.FlatTopPower

variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]

theorem block_update {k : ℕ} (v : Fin k × Fin 2 → T) (a : Fin k) (b : Fin 2) (z : T) :
    (fun i c => Function.update v (a, b) z (i, c)) =
      Function.update (fun i c => v (i, c)) a (Function.update (fun c => v (a, c)) b z) := by
  ext i c
  by_cases hi : i = a
  · subst hi
    by_cases hc : c = b
    · subst hc; simp
    · simp [Function.update_apply, hc]
  · simp [Function.update_apply, hi]

theorem pairProd_key {k : ℕ} (α : T [⋀^Fin 2]→L[ℝ] ℝ) (v : Fin k × Fin 2 → T) (a : Fin k)
    (b : Fin 2) (z : T) :
    ∏ i, α (fun c => Function.update v (a, b) z (i, c)) =
      α (Function.update (fun c => v (a, c)) b z) *
        ∏ i ∈ Finset.univ \ {a}, α (fun c => v (i, c)) := by
  rw [← Finset.prod_update_of_mem (Finset.mem_univ a) (fun i => α (fun c => v (i, c)))]
  refine Finset.prod_congr rfl fun i _ => ?_
  have := congrFun (block_update v a b z) i
  by_cases hi : i = a
  · subst hi
    simp only [Function.update_self] at this ⊢
    exact congrArg α this
  · simp only [Function.update_of_ne hi] at this ⊢
    exact congrArg α this

def pairProd (α : T [⋀^Fin 2]→L[ℝ] ℝ) (k : ℕ) :
    MultilinearMap ℝ (fun _ : Fin k × Fin 2 => T) ℝ where
  toFun v := ∏ i, α (fun c => v (i, c))
  map_update_add' := by
    intro inst v j x y
    obtain rfl : inst = (fun a b => instDecidableEqProd a b) := Subsingleton.elim _ _
    obtain ⟨a, b⟩ := j
    rw [pairProd_key, pairProd_key, pairProd_key, α.map_update_add, add_mul]
  map_update_smul' := by
    intro inst v j r x
    obtain rfl : inst = (fun a b => instDecidableEqProd a b) := Subsingleton.elim _ _
    obtain ⟨a, b⟩ := j
    rw [pairProd_key, pairProd_key, α.map_update_smul, smul_eq_mul, smul_eq_mul, mul_assoc]

theorem pairProd_apply (α : T [⋀^Fin 2]→L[ℝ] ℝ) (k : ℕ) (v : Fin k × Fin 2 → T) :
    pairProd α k v = ∏ i, α ![v (i, 0), v (i, 1)] := by
  show ∏ i, α (fun c => v (i, c)) = _
  refine Finset.prod_congr rfl fun i _ => congrArg α ?_
  ext c; fin_cases c <;> rfl

theorem wedgePow_eq (α : T [⋀^Fin 2]→L[ℝ] ℝ) (k : ℕ) (v : Fin k × Fin 2 → T) :
    wedgePow α k v = (1 / 2 ^ k) * MultilinearMap.alternatization (pairProd α k) v := by
  rw [wedgePow, MultilinearMap.alternatization_apply]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [MultilinearMap.domDomCongr_apply, pairProd_apply,
    Units.smul_def, zsmul_eq_mul]

theorem wedgePow_eq_zero_of_not_linearIndependent (α : T [⋀^Fin 2]→L[ℝ] ℝ) (k : ℕ)
    (v : Fin k × Fin 2 → T) (hv : ¬ LinearIndependent ℝ v) : wedgePow α k v = 0 := by
  rw [wedgePow_eq, AlternatingMap.map_linearDependent _ v hv, mul_zero]

theorem wedgePow_comp {T' : Type*} [NormedAddCommGroup T'] [NormedSpace ℝ T']
    (α : T' [⋀^Fin 2]→L[ℝ] ℝ) (L : T →L[ℝ] T') (k : ℕ) (v : Fin k × Fin 2 → T) :
    wedgePow (α.compContinuousLinearMap L) k v = wedgePow α k (L ∘ v) := by
  unfold wedgePow
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  ext c; fin_cases c <;> rfl

theorem wedgePow_succ_eq_zero {g : ℕ} (α : Fl g [⋀^Fin 2]→L[ℝ] ℝ)
    (v : Fin (g + 1) × Fin 2 → Fl g) : wedgePow α (g + 1) v = 0 := by
  refine wedgePow_eq_zero_of_not_linearIndependent α _ v fun hv => ?_
  have h := hv.fintype_card_le_finrank
  simp [Module.finrank_fintype_fun_eq_card] at h
  omega

theorem flatForm_wedgePow_succ_eq_zero :
    ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
      {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ},
      IsPeriodMap B τ → ∀ P ∈ cov B g, ∀ v, wedgePow (om0 τ P) (g + 1) v = 0 := by
  intro g E _ _ _ B τ _ P _ v
  rw [om0, wedgePow_comp]
  exact wedgePow_succ_eq_zero _ _

end GlobalTheory.FlatTopPower
