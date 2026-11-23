import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem genericPoint_notMem_of_snc (Y : Scheme.{0}) [IsIntegral Y] (B : Closeds Y)
    (h : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B)) : genericPoint Y ∉ B := by
  obtain ⟨-, U, hy, n, f, J, ⟨-, hn⟩, hI⟩ := h (genericPoint Y)
  have hdim : ringKrullDim (Y.presheaf.stalk (genericPoint Y)) = 0 :=
    ringKrullDim_eq_zero_of_field Y.functionField
  rw [hdim] at hn
  have hn0 : n = 0 := by exact_mod_cast hn
  subst hn0
  have hJ : J = ∅ := Finset.eq_empty_of_isEmpty J
  subst hJ
  intro hB
  have hs : genericPoint Y ∈ (Scheme.IdealSheafData.vanishingIdeal B).support := by
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hB
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hy, hI, Scheme.mem_zeroLocus_iff] at hs
  refine hs 1 (Ideal.subset_span (by simp)) ?_
  simpa using hy

end GlobalTheory.PairStep
