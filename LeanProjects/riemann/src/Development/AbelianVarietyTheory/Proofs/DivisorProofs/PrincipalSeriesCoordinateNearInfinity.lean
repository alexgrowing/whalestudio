import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WEMulNUMulTD

noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped Topology

namespace GlobalTheory.PrinTwo

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nL_inv (x : k) : ((nL x)⁻¹ : GL (Fin (1 + 1)) k) = nL (-x) := by
  rw [inv_eq_iff_mul_eq_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem continuous_nL : Continuous (nL : k → GL (Fin (1 + 1)) k) := by
  have h : Continuous fun x : k => ((nL x : GL (Fin (1 + 1)) k) : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [nL_inv]
  exact h.comp continuous_neg

theorem nL_zero : (nL (0 : k) : GL (Fin (1 + 1)) k) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem exists_ev_nL_eq {μ₁ μ₂ : kˣ →* ℂˣ} (f : PSp μ₁ μ₂) :
    ∃ r : kˣ, ∀ z : k, valuation k z < valuation k (r : k) → ev f (nL z) = ev f 1 := by
  have hS : IsOpen {g : GL (Fin (1 + 1)) k | psRep μ₁ μ₂ g f = f} := isSmooth_parInd _ _ f
  have hU : nL ⁻¹' {g : GL (Fin (1 + 1)) k | psRep μ₁ μ₂ g f = f} ∈ 𝓝 (0 : k) :=
    (hS.preimage continuous_nL).mem_nhds (by simp [nL_zero])
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff _).mp hU
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero k)
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact γ.ne_zero (by simpa using hy.symm)
  refine ⟨Units.mk0 y hy0, fun z hz => ?_⟩
  have hz' : psRep μ₁ μ₂ (nL z) f = f := hγ (by rw [← hy]; exact hz)
  rw [← one_mul (nL z), ← ev_act, hz']

theorem coord_eq_of_far : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (μ₁ μ₂ : kˣ →* ℂˣ) (f : GlobalTheory.PrinTwo.PSp μ₁ μ₂), ∃ R : kˣ, ∀ x : kˣ,
    ValuativeRel.valuation k (R : k) < ValuativeRel.valuation k (x : k) →
      GlobalTheory.PrinTwo.coord f x = GlobalTheory.PrinTwo.bchar μ₁ μ₂ (-x⁻¹) x * GlobalTheory.PrinTwo.ev f 1 := by
  intro k _ _ _ _ μ₁ μ₂ f
  obtain ⟨r, hr⟩ := exists_ev_nL_eq f
  refine ⟨r⁻¹, fun x hx => ?_⟩
  rw [coord, wE_mul_nU_eq, ev_bor, hr]
  have hx0 : (0 : ValueGroupWithZero k) < valuation k (x : k) := by simp [zero_lt_iff]
  have hr0 : (0 : ValueGroupWithZero k) < valuation k (r : k) := by simp [zero_lt_iff]
  simp only [Units.val_inv_eq_inv_val, map_inv₀] at hx ⊢
  exact (inv_lt_comm₀ hr0 hx0).mp hx

end GlobalTheory.PrinTwo
