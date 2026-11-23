import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import Development.WeilBound.CoreStatements.FlagImmersions.IntersectionMultilinearExpansion
import Development.WeilBound.CoreStatements.FlagImmersions.IntersectionMonomialLines

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

namespace Ii

theorem lin_prod_expand {J : Type} [Fintype J] [DecidableEq J] (d : ℕ) (Φ : MvPolynomial J ℝ →ₗ[ℝ] ℝ)
    (c : J → ℝ) :
    Φ ((∑ j, C (c j) * X j) ^ d) =
      ∑ w : Fin d → J, (∏ k, c (w k)) * Φ (monomial (∑ k, Finsupp.single (w k) 1) 1) := by
  rw [← Fin.prod_const, Fintype.prod_sum, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hm : ∏ k, C (c (w k)) * X (w k) = C (∏ k, c (w k)) * monomial (∑ k, Finsupp.single (w k) 1) (1 : ℝ) := by
    rw [Finset.prod_mul_distrib, map_prod, monomial_sum_one]
    rfl
  rw [hm, C_mul', map_smul, smul_eq_mul]

theorem prod_weight {α : Type} [DecidableEq α] {d : ℕ} (w : Fin d → Option α) (x : ℝ) :
    ∏ k, (if w k = none then x else 1) = x ^ (∑ k, Finsupp.single (w k) 1 : Option α →₀ ℕ) none := by
  rw [Finsupp.finsetSum_apply, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finsupp.single_apply]
  split_ifs <;> simp

end Ii

open Ii in
theorem root_model_arithmetic_intersection : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), (∀ j, (n j : ℝ) = q * M.coef lam s j) → II M.K M.ι M.P (dimFl Ψ N + 1) (fun _ => combLine (M.line t) n) = M.δ * (q : ℝ) ^ (dimFl Ψ N + 1) * M.arFun II t (linA lam s ^ (dimFl Ψ N + 1)) := by
  intro II hII Ψ _ N M t lam s q n hn
  classical
  have hsm : ∀ j, IsSmoothHerm (M.line t j) := by
    intro j
    cases j with
    | none => exact M.A_smooth
    | some r => exact M.x_smooth t r
  rw [RootFieldNumerics.intersection_multilinear_expansion II hII M.K M.ι M.P (dimFl Ψ N + 1) _ (M.line t) (fun _ => n) M.arith hsm]
  let cc : Option (Ψ × Fin N) → ℝ := fun j => Option.elim j s (fun r => -lam r.1 r.2)
  have hlin : linA lam s = ∑ j, C (cc j) * X j := by
    rw [Fintype.sum_option]
    simp [cc, linA, toA, linRoot, map_sum, map_neg, rename_X, Finset.sum_neg_distrib, add_comm]
  rw [hlin, lin_prod_expand, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  obtain ⟨hdeg, σ, _, hII2⟩ := RootFieldNumerics.intersection_monomial_lines II hII.1 M.K M.ι M.P (dimFl Ψ N + 1) _ (M.line t) w M.arith hsm
  have hmono : M.arFun II t (monomial (∑ k, Finsupp.single (w k) 1) 1) =
      II M.K M.ι M.P (dimFl Ψ N + 1) (fun k => M.line t (w k)) /
        (M.δ * (M.kA : ℝ) ^ (∑ k, Finsupp.single (w k) 1 : Option (Ψ × Fin N) →₀ ℕ) none) := by
    have hb : (monomial (∑ k, Finsupp.single (w k) 1) (1 : ℝ) : RPA Ψ N) =
        basisMonomials (Option (Ψ × Fin N)) ℝ (∑ k, Finsupp.single (w k) 1) := by
      rw [coe_basisMonomials]
    rw [RootModel.arFun, hb, Module.Basis.constr_basis, RootModel.arMono, if_pos hdeg, hII2]
  have hc : ∏ k, cc (w k) = (∏ k, M.coef lam s (w k)) *
      (M.kA : ℝ) ^ (∑ k, Finsupp.single (w k) 1 : Option (Ψ × Fin N) →₀ ℕ) none := by
    rw [← prod_weight w (M.kA : ℝ), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    have hk : (M.kA : ℝ) ≠ 0 := by exact_mod_cast M.kA_pos.ne'
    cases w k with
    | none =>
      simp [cc, RootModel.coef]
      field_simp
    | some r => simp [cc, RootModel.coef]
  have hnp : ∏ k, (n (w k) : ℝ) = (q : ℝ) ^ (dimFl Ψ N + 1) * ∏ k, M.coef lam s (w k) := by
    simp_rw [hn]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hδ : (M.δ : ℝ) ≠ 0 := by exact_mod_cast M.δ_pos.ne'
  have hk : (M.kA : ℝ) ≠ 0 := by exact_mod_cast M.kA_pos.ne'
  rw [hmono, hc, hnp]
  field_simp

end RootFieldNumerics
