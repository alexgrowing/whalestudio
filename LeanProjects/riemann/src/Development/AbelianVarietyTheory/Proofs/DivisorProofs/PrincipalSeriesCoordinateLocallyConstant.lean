import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WEMulNUMulTD

noncomputable section

open ValuativeRel Matrix Topology

namespace GlobalTheory.PrinTwo

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nU_zero : (nU (0 : k) : GL (Fin (1 + 1)) k) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem nU_inv (x : k) : (nU x : GL (Fin (1 + 1)) k)⁻¹ = nU (-x) := by
  rw [inv_eq_iff_mul_eq_one, nU_mul_nU, add_neg_cancel, nU_zero]

theorem continuous_val_nU :
    Continuous (fun x : k => ((nU x : GL (Fin (1 + 1)) k) : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k)) := by
  simp only [val_nU]
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_nU : Continuous (nU : k → GL (Fin (1 + 1)) k) := by
  refine Units.continuous_iff.2 ⟨continuous_val_nU, ?_⟩
  have h : (fun x : k => (((nU x : GL (Fin (1 + 1)) k)⁻¹ : GL (Fin (1 + 1)) k) : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k)) =
      fun x => ((nU (-x) : GL (Fin (1 + 1)) k) : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) := by
    funext x; rw [nU_inv]
  rw [h]
  exact continuous_val_nU.comp continuous_neg

theorem exists_unit_ball_subset {U : Set k} (hU : U ∈ 𝓝 (0 : k)) :
    ∃ r : kˣ, {y : k | valuation k y ≤ valuation k (r : k)} ⊆ U := by
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff U).mp hU
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero k)
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact γ.ne_zero (by simpa using hy.symm)
  obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have hr0 : r ≠ 0 := by simpa using hr
  refine ⟨Units.mk0 (r * y) (mul_ne_zero hr0 hy0), fun z hz => hγ ?_⟩
  have hz' : valuation k z ≤ valuation k (r * y) := hz
  refine lt_of_le_of_lt hz' ?_
  show valuation k (r * y) < (γ : ValueGroupWithZero k)
  rw [map_mul, hy]
  exact mul_lt_of_lt_one_left (by simp [zero_lt_iff]) hr1

theorem coord_isLC : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (μ₁ μ₂ : kˣ →* ℂˣ) (f : GlobalTheory.PrinTwo.PSp μ₁ μ₂), GlobalTheory.PrinTwo.IsLC (GlobalTheory.PrinTwo.coord f) := by
  intro k _ _ _ _ μ₁ μ₂ f
  have hO : IsOpen (_ : Set (GL (Fin (1 + 1)) k)) := f.2
  have hmem := (continuous_nU (k := k)).continuousAt.preimage_mem_nhds (x := 0)
    (by rw [nU_zero]; exact hO.mem_nhds (by show _ = _; rw [map_one]; rfl))
  obtain ⟨r, hr⟩ := exists_unit_ball_subset hmem
  refine ⟨r, fun x y hy => ?_⟩
  have hfix := hr hy
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at hfix
  have h2 := congrArg (fun F => TensorProduct.lid ℂ ℂ (F.1 (wE * nU x))) hfix
  simp only [coord, ev, ← nU_mul_nU, ← mul_assoc]
  exact h2

end GlobalTheory.PrinTwo
