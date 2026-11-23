import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.ProjVar.Var

theorem interPoly_eq_zero_of_isHomogeneous (F : Type) [Field F] (Y : Var F) (κ : Type) (gr : κ → Y.Dv) (k : ℕ)
    (P : MvPolynomial κ ℝ) (hP : P.IsHomogeneous k) (hk : k ≠ Y.dim) : Y.interPoly gr P = 0 := by
  rw [P.as_sum, map_sum]
  refine Finset.sum_eq_zero fun d hd => ?_
  have hw : Finsupp.weight 1 d = k := hP (mem_support_iff.mp hd)
  have e : monomial d (coeff d P) = coeff d P • basisMonomials κ ℝ d := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul, interPoly, Module.Basis.constr_basis, dif_neg, smul_zero]
  rintro ⟨s, hs⟩
  apply hk
  rw [← hw, ← hs, map_sum]
  simp [Finsupp.weight_apply, Finsupp.sum_single_index]

end GlobalTheory.ProjVar.Var
