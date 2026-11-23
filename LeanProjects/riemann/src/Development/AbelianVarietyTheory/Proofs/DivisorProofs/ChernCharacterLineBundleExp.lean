import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondChernDegreeFubiniStudyLine

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory

namespace GlobalTheory.CxForm

theorem chPart_rank_one (j : ℕ) : chPart 1 j =
    ((j.factorial : ℚ)⁻¹) • (⟨esymm (Fin 1) ℚ 1, esymm_isSymmetric _ _ 1⟩ : symmetricSubalgebra (Fin 1) ℚ) ^ j := by
  unfold chPart
  congr 1
  exact Subtype.ext (by simp [MvPolynomial.psum, esymm_one])

theorem ArRing.ch_ofLB (B : BottChern) (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ)
    (h : IsRegVar p D) (R : ArRing B h) (L : HermLB p) :
    R.ch (.ofLB L) = ∑ j ∈ Finset.range (D + 2), ((j.factorial : ℚ)⁻¹) • R.c1 L ^ j := by
  have e : R.cl (.ofLB L) 1 = R.c1 L := by
    rw [R.cl_one]
    exact (R.firstChernCongr _ _ (ChTwoModel.isometric_det_ofLB L)).symm
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [chPart_rank_one, map_smul, map_pow, R.char_esymm, e]

end GlobalTheory.CxForm
