import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankGraphJetsLeChooseStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory

theorem count_kernel_nonzero : ∀ {κ κ' : Type} [Field κ] [Field κ'] [Algebra ℂ κ] [Algebra ℂ κ'] (k c M l : ℕ) (ρ : Fin c → (κ →ₐ[ℂ] κ'))
    (w : Fin l → κ), (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) → c * (M + k - 1).choose k < l →
  ∃ b : Fin l → κ', b ≠ 0 ∧ ∀ i, ∑ j, w j ⊗ₜ[ℂ] b j ∈
    (RingHom.ker (Algebra.TensorProduct.productMap (ρ i) (AlgHom.id ℂ κ'))) ^ M := by
  intro κ κ' _ _ _ _ k c M l ρ w hz hlt
  letI : Algebra κ' (κ ⊗[ℂ] κ') := Algebra.TensorProduct.rightAlgebra
  set J : Fin c → Ideal (κ ⊗[ℂ] κ') := fun i =>
    (RingHom.ker (Algebra.TensorProduct.productMap (ρ i) (AlgHom.id ℂ κ'))) ^ M with hJ
  have hjet := fun i => GlobalTheory.T.finrank_graphJets_le_choose k M (ρ i) hz
  haveI : ∀ i, Module.Finite κ' ((κ ⊗[ℂ] κ') ⧸ J i) := fun i => (hjet i).2
  let g : (Fin l → κ') →ₗ[κ'] (κ ⊗[ℂ] κ') := Fintype.linearCombination κ' (fun j => w j ⊗ₜ[ℂ] (1 : κ'))
  have hg : ∀ b, g b = ∑ j, w j ⊗ₜ[ℂ] b j := by
    intro b
    simp only [g, Fintype.linearCombination_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def]
    show (1 ⊗ₜ[ℂ] b j) * (w j ⊗ₜ[ℂ] (1 : κ')) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  let f : (Fin l → κ') →ₗ[κ'] ((i : Fin c) → (κ ⊗[ℂ] κ') ⧸ J i) :=
    LinearMap.pi fun i => (Ideal.Quotient.mkₐ κ' (J i)).toLinearMap.comp g
  have hdim : Module.finrank κ' ((i : Fin c) → (κ ⊗[ℂ] κ') ⧸ J i) < Module.finrank κ' (Fin l → κ') := by
    rw [Module.finrank_pi_fintype, Module.finrank_fin_fun]
    calc ∑ i, Module.finrank κ' ((κ ⊗[ℂ] κ') ⧸ J i) ≤ ∑ _i : Fin c, (M + k - 1).choose k :=
          Finset.sum_le_sum fun i _ => (hjet i).1
      _ = c * (M + k - 1).choose k := by simp
      _ < l := hlt
  obtain ⟨b, hbker, hb0⟩ := (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hdim)
  refine ⟨b, hb0, fun i => ?_⟩
  have := congr_fun (LinearMap.mem_ker.mp hbker) i
  simp only [f, LinearMap.pi_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, Pi.zero_apply] at this
  rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, hg] at this
  exact this

end GlobalTheory
