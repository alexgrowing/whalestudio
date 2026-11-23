import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

noncomputable section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.WeierstrassCurve (scheme ptHom IsUnimodularSol)

namespace GlobalTheory.CMTorsion

def curve (Λ : PeriodPair) (Ω : ℂ) : WeierstrassCurve ℂ :=
  ⟨0, 0, 0, -(Λ.g₂ / Ω ^ 4 / 4), -(Λ.g₃ / Ω ^ 6 / 4)⟩

open Classical in

def coords (Λ : PeriodPair) (Ω : ℂ) (z : ℂ) : Fin 3 → ℂ :=
  if z ∈ Λ.lattice then ![0, 1, 0] else ![Λ.weierstrassP z / Ω ^ 2, Λ.derivWeierstrassP z / (2 * Ω ^ 3), 1]

theorem isUnimodularSol_coords (Λ : PeriodPair) (Ω z : ℂ) :
    IsUnimodularSol ((curve Λ Ω).map (RingHom.id ℂ)) (coords Λ Ω z) := by
  rw [WeierstrassCurve.map_id]
  unfold coords
  split_ifs with hz
  · exact GlobalTheory.WeierstrassCurve.isUnimodularSol_zero _
  · refine GlobalTheory.WeierstrassCurve.isUnimodularSol_some ?_
    rw [WeierstrassCurve.Affine.equation_iff]
    have h := Λ.derivWeierstrassP_sq z hz
    simp only [curve]
    by_cases hΩ : Ω = 0
    · subst hΩ; simp
    · field_simp
      linear_combination 4 * h

def pt (Λ : PeriodPair) (Ω : ℂ) (z : ℂ) : Sp ℂ ⟶ scheme (curve Λ Ω) :=
  ptHom (curve Λ Ω) (RingHom.id ℂ) (coords Λ Ω z) (isUnimodularSol_coords Λ Ω z)

theorem isUnimodularSol_tan (W : WeierstrassCurve ℂ) (c : ℂ) :
    IsUnimodularSol (W.map (algebraMap ℂ (DualNumber ℂ))) ![c • DualNumber.eps, -1, 0] := by
  refine GlobalTheory.WeierstrassCurve.isUnimodularSol_origin ?_
  rw [GlobalTheory.WeierstrassCurve.equation_origin_iff]
  have : (c • DualNumber.eps : DualNumber ℂ) ^ 3 = 0 := by
    rw [pow_succ, pow_two, smul_mul_smul_comm, DualNumber.eps_mul_eps, smul_zero, zero_mul]
  simp [this]

def tan (W : WeierstrassCurve ℂ) (c : ℂ) : Sp (DualNumber ℂ) ⟶ scheme W :=
  ptHom W (algebraMap ℂ (DualNumber ℂ)) ![c • DualNumber.eps, -1, 0] (isUnimodularSol_tan W c)

theorem curve_map {Λ₀ Λ₁ : PeriodPair} {Ω₀ Ω₁ : ℂ} (g : ℂ →+* ℂ) (h₂ : g (Λ₀.g₂ / Ω₀ ^ 4) = Λ₁.g₂ / Ω₁ ^ 4)
    (h₃ : g (Λ₀.g₃ / Ω₀ ^ 6) = Λ₁.g₃ / Ω₁ ^ 6) : (curve Λ₀ Ω₀).map g = curve Λ₁ Ω₁ := by
  ext <;> simp [curve, h₂, h₃, map_neg, map_div₀, map_ofNat]

end GlobalTheory.CMTorsion
