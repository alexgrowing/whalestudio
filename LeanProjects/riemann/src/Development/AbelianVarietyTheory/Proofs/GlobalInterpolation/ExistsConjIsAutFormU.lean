import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AutFormDefiniteUnitaryEqSumPolynomialMulAutFormStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsConjPolynomialDefiniteUnitaryRationalStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DefiniteUnitaryRealApproxAndFiniteInfiniteSplitStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsDefiniteUnitaryFunctionPolynomialMulSmoothStatement

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.UnitaryBC

theorem exists_conj_isAutFormU (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : ℂ ≃+* ℂ)
    (φ : UA E n → ℂ) (hφ : IsAutFormU φ) :
    ∃ φ' : UA E n → ℂ, IsAutFormU φ' ∧ ∀ g ∈ finU E n, φ' g = σ (φ g) := by
  obtain ⟨m, p, e, hpe, hdec⟩ := GlobalTheory.T.autFormDefiniteUnitary_eq_sum_polynomial_mul_autForm E n φ hφ
  choose p' hp' hpp using fun i => GlobalTheory.T.exists_conj_polynomial_definiteUnitary_rational E n σ (p i) (hpe i).1
  obtain ⟨hD, -, -, a, b, -, -, hab, -⟩ := GlobalTheory.T.definiteUnitary_realApprox_and_finite_infinite_split E n
  obtain ⟨φ', hc, hl, hk, hv⟩ := GlobalTheory.T.exists_definiteUnitary_function_polynomial_mul_smooth E n m p' (fun i g => σ (e i g.1)) hp' (fun i => by
    refine ⟨
      { carrier := {k : finU E n | RU E n k (e i) = e i}
        one_mem' := by simp
        mul_mem' := fun {x y} hx hy => by
          simp only [Set.mem_setOf_eq] at hx hy ⊢
          rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hy, hx]
        inv_mem' := fun {x} hx => by
          simp only [Set.mem_setOf_eq] at hx ⊢
          conv_lhs => rw [← hx]
          rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply] }, ?_, ?_⟩
    · exact (hpe i).2.level
    · intro u hu g
      exact congrArg σ (congrFun (show RU E n u (e i) = e i from hu) g.1))
  have key : ∀ γ ∈ ratU E n, ∀ x : UA E n, cInf x = cInf γ → φ' x = σ (φ x) := by
    intro γ hγ x hx
    have h1 : cInf (b x).1 = cInf γ := by
      rw [← hx]
      conv_rhs => rw [hab x, map_mul, show cInf (a x).1 = 1 from (a x).2, one_mul]
    conv_lhs => rw [hab x, hv]
    conv_rhs => rw [hab x, hdec, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hpp i γ hγ _ h1]
  refine ⟨φ', ⟨hc, fun γ hγ g => ?_, hl, hk⟩, fun g hg => key 1 (one_mem _) g (by rw [map_one]; exact hg)⟩
  have hc2 : Continuous fun x => φ' (γ * x) := hc.comp (continuous_const.mul continuous_id)
  refine congrFun (Continuous.ext_on hD hc2 hc ?_) g
  rintro _ ⟨δ, hδ, u, hu, rfl⟩
  have hu' : cInf u = 1 := hu
  change φ' (γ * (δ * u)) = φ' (δ * u)
  rw [key (γ * δ) (mul_mem hγ hδ) _ (by simp only [map_mul, hu', mul_one]),
    key δ hδ _ (by simp only [map_mul, hu', mul_one]), hφ.left γ hγ]

end GlobalTheory.UnitaryBC
