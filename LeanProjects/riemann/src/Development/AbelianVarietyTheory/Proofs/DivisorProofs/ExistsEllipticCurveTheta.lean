import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory NumberField

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TateCurve

abbrev realQuadraticSqrtTwentynine : IntermediateField ℚ ℝ := IntermediateField.adjoin ℚ {Real.sqrt 29}

theorem isIntegral_sqrt_twentynine : IsIntegral ℚ (Real.sqrt 29) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C 29, ?_, ?_⟩
  · exact Polynomial.monic_X_pow_sub_C _ (by norm_num)
  · simp [Real.sq_sqrt (show (0:ℝ) ≤ 29 by norm_num)]

instance : FiniteDimensional ℚ realQuadraticSqrtTwentynine := IntermediateField.adjoin.finiteDimensional isIntegral_sqrt_twentynine

instance : NumberField realQuadraticSqrtTwentynine where

def s29 : realQuadraticSqrtTwentynine := ⟨Real.sqrt 29, IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)⟩

theorem sqrt_twentynine_sq : s29 ^ 2 = 29 := by
  apply Subtype.ext
  simp [s29, Real.sq_sqrt (show (0:ℝ) ≤ 29 by norm_num)]
  rfl

def epsK : realQuadraticSqrtTwentynine := (5 + s29) / 2

theorem epsK_sq : epsK ^ 2 = 5 * epsK + 1 := by
  have h := sqrt_twentynine_sq
  unfold epsK
  linear_combination h / 4

theorem isIntegral_epsK : IsIntegral ℤ epsK := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C 5 * Polynomial.X - 1, ?_, ?_⟩
  · have : (Polynomial.X ^ 2 - Polynomial.C 5 * Polynomial.X - 1 : Polynomial ℤ)
        = Polynomial.X ^ 2 - (Polynomial.C 5 * Polynomial.X + Polynomial.C 1) := by
      simp [sub_sub]
    rw [this]
    exact Polynomial.monic_X_pow_sub (by compute_degree!)
  · have h := epsK_sq
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.eval₂_one]
    simp
    linear_combination h

def eps : 𝓞 realQuadraticSqrtTwentynine := ⟨epsK, isIntegral_epsK⟩

theorem eps_sq : eps ^ 2 = 5 * eps + 1 := by
  apply RingOfIntegers.coe_injective
  simp only [map_pow, map_add, map_mul, map_one, map_ofNat]
  exact epsK_sq

def tateW : WeierstrassCurve (𝓞 realQuadraticSqrtTwentynine) := ⟨1, 0, eps ^ 2, 0, 0⟩

theorem tateW_Δ : tateW.Δ = -eps ^ 10 := by
  have h := eps_sq
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, tateW]
  linear_combination (eps ^ 6 * (eps ^ 2 + 5 * eps - 1)) * h

theorem isUnit_tateW_Δ : IsUnit tateW.Δ := by
  rw [tateW_Δ]
  have h := eps_sq
  have hu : IsUnit eps := isUnit_iff_exists_inv.mpr ⟨eps - 5, by linear_combination h⟩
  exact (hu.pow 10).neg

instance : tateW.IsElliptic := ⟨isUnit_tateW_Δ⟩

end GlobalTheory.TateCurve

open GlobalTheory.TateCurve in

theorem GlobalTheory.exists_ppas_g_one_hasTheta :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (E : PPAS (Sp (𝓞 K))), E.g = 1 ∧ E.HasTheta :=
  ⟨realQuadraticSqrtTwentynine, inferInstance, inferInstance, PPAS.ofPolAV (GlobalTheory.WeierstrassCurve.ellPolAV tateW),
    GlobalTheory.WeierstrassCurve.ellPolAV_g tateW, PPAS.hasTheta_ofPolAV _⟩
