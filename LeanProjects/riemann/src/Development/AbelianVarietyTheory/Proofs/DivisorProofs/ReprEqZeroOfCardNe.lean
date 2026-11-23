import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.LineForm

namespace GlobalTheory.PullTop

theorem repr_eq_zero_of_card_ne {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M] [LinearOrder I]
    (b : Module.Basis I R M) {k : ℕ} (x : ⋀[R]^k M) {S : Finset I} (hS : S.card ≠ k) :
    b.ExteriorAlgebra.repr (x : ExteriorAlgebra R M) S = 0 := by
  have h : (Finsupp.lapply S ∘ₗ b.ExteriorAlgebra.repr.toLinearMap ∘ₗ (⋀[R]^k M).subtype) = 0 := by
    refine (b.exteriorPower k).ext fun s => ?_
    have hs : (s : Finset I) ≠ S := fun e => hS (e ▸ s.2)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, ← ExteriorAlgebra.basis_eq_coe_basis,
      LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply, LinearMap.zero_apply]
    exact Finsupp.single_eq_of_ne' hs
  exact LinearMap.congr_fun h x

theorem repr_map_eq_zero {R M N I J : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [LinearOrder I] [LinearOrder J] [Fintype I] (b : Module.Basis I R M) (c : Module.Basis J R N) (f : M →ₗ[R] N)
    {S : Finset J} (hS : Fintype.card I < S.card) (β : ExteriorAlgebra R M) :
    c.ExteriorAlgebra.repr (ExteriorAlgebra.map f β) S = 0 := by
  have h : (Finsupp.lapply S ∘ₗ c.ExteriorAlgebra.repr.toLinearMap ∘ₗ (ExteriorAlgebra.map f).toLinearMap) = 0 := by
    refine b.ExteriorAlgebra.ext fun T => ?_
    have hT : S.card ≠ T.card := ((Finset.card_le_univ T).trans_lt hS).ne'
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearEquiv.coe_coe, Finsupp.lapply_apply,
      LinearMap.zero_apply]
    rw [ExteriorAlgebra.basis_apply b T, ExteriorAlgebra.map_apply_ιMulti,
      ← exteriorPower.ιMulti_apply_coe]
    exact repr_eq_zero_of_card_ne c _ hT
  exact LinearMap.congr_fun h β

theorem repr_pull_univ {n : ℕ} (L : ReciprocityTheory.L2DbarEstimates.V (n + 1) →L[ℂ] ReciprocityTheory.L2DbarEstimates.V n) (β : Alt n) :
    (bas (n + 1)).repr (pull L β) Finset.univ = 0 :=
  repr_map_eq_zero ((Pi.basisFun ℂ (Fin n ⊕ Fin n)).reindex finSumFinEquiv) _ _ (by simp; omega) β

end GlobalTheory.PullTop
