import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

theorem root_coef_add {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (lam mu : Wt Ψ N) (s s' : ℝ)
    (j : Option (Ψ × Fin N)) : M.coef (lam + mu) (s + s') j = M.coef lam s j + M.coef mu s' j := by
  cases j with
  | none => simp only [RootModel.coef]; ring
  | some r => simp only [RootModel.coef, Pi.add_apply]; ring

theorem root_coef_smul {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (lam : Wt Ψ N) (a s : ℝ)
    (j : Option (Ψ × Fin N)) : M.coef (a • lam) (a * s) j = a * M.coef lam s j := by
  cases j with
  | none => simp only [RootModel.coef, mul_div_assoc]
  | some r => simp only [RootModel.coef, Pi.smul_apply, smul_eq_mul]; ring

theorem root_coef_split {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (lam : Wt Ψ N) (s : ℝ)
    (j : Option (Ψ × Fin N)) : M.coef lam s j = M.coef lam 0 j + s * M.coef 0 1 j := by
  cases j with
  | none => simp only [RootModel.coef]; ring
  | some r => simp only [RootModel.coef, Pi.zero_apply]; ring

theorem root_coef_weighted_sum_split {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (lam : Wt Ψ N) (s : ℝ)
    (g : Option (Ψ × Fin N) → ℝ) :
    ∑ j, M.coef lam s j * g j = ∑ j, M.coef lam 0 j * g j + s * ∑ j, M.coef 0 1 j * g j := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [root_coef_split M lam s j]
  ring

end RootFieldNumerics

theorem RootFieldNumerics.curveDeg_linear_and_nef : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (lam mu : Wt Ψ N) (s s' a : ℝ), (∀ W, M.curveDeg (lam + mu) (s + s') W = M.curveDeg lam s W + M.curveDeg mu s' W) ∧ (∀ W, M.curveDeg (a • lam) (a * s) W = a * M.curveDeg lam s W) ∧ (∀ p, 0 ≤ s → M.NefAt p lam 0 → M.NefAt p 0 1 → M.NefAt p lam s) ∧ (0 ≤ s → M.NefGen lam 0 → M.NefGen 0 1 → M.NefGen lam s) := by
  intro Ψ _ N M lam mu s s' a
  refine ⟨fun W => ?_, fun W => ?_, fun p hs h1 h2 W hW => ?_, fun hs h1 h2 W hW hP => ?_⟩
  · simp only [RootModel.curveDeg]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [RootFieldNumerics.root_coef_add]; ring
  · simp only [RootModel.curveDeg]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [RootFieldNumerics.root_coef_smul]; ring
  · have e : M.curveDeg lam s W = M.curveDeg lam 0 W + s * M.curveDeg 0 1 W :=
      RootFieldNumerics.root_coef_weighted_sum_split M lam s _
    rw [e]
    exact add_nonneg (h1 W hW) (mul_nonneg hs (h2 W hW))
  · have e : ∑ j, M.coef lam s j * geomDeg W (M.line 1 j) 1
        = ∑ j, M.coef lam 0 j * geomDeg W (M.line 1 j) 1
          + s * ∑ j, M.coef 0 1 j * geomDeg W (M.line 1 j) 1 :=
      RootFieldNumerics.root_coef_weighted_sum_split M lam s _
    rw [e]
    exact add_nonneg (h1 W hW hP) (mul_nonneg hs (h2 W hW hP))
