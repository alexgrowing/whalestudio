import Mathlib
import Formalism.DivisorInequality.StatementObj
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.KappaNormalise
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.TransferMean
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.StepDiii
import Formalism.ThetaSupremumBounds.GaussianShiftBounds.Assembly
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ConjugateWeightLatticeOfGeneral
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.PlaceSumSquares
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.DualMu
import Formalism.MeanHeightDescent.AverageDegreeBounds.CovolumeAssemblyHolds
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.LocalConditionsGlobalForm
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic

open Module NumberField IsDedekindDomain Finset
open scoped Matrix ComplexOrder

namespace Formalism.DivisorInequality

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism.LatticeIndexTer (ph)

theorem ramified_places_weighted_sum_le_one (K : Type) [Field K] [NumberField K] [StarRing K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∑ y ∈ S, lw y * ((ramw y : ℝ) * (2 / (plc y : ℝ) ^ 2)) ≤ 1 := by
  have h1 := Formalism.EigenvalueLevelCeiling.place_sum K S (fun p => 2 / (p : ℝ) ^ 2) (fun p => by positivity)
  have h2 := Formalism.DivisionValues.prime_mod_six_of_large.1 (S.image plc) (by
    intro p hp
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hp
    exact (Formalism.EigenvalueLevelCeiling.ramified_basic_bound K y).1)
  have h3 : ∑ p ∈ S.image plc, Real.log (p : ℝ) * (2 / (p : ℝ) ^ 2) =
      ∑ p ∈ S.image plc, 2 * Real.log (p : ℝ) / (p : ℝ) ^ 2 :=
    Finset.sum_congr rfl (fun p _ => by ring)
  linarith

theorem places_ell_weighted_sum_le_one (K : Type) [Field K] [NumberField K] [StarRing K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∑ y ∈ S, lw y * (2 / ellw y ^ 2) ≤ 1 := by
  have h := ramified_places_weighted_sum_le_one K (S.filter fun y => (0:ℝ) ≤ (ramw y : ℝ))
  rw [Finset.sum_filter] at h
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun y _ => ?_)) h
  by_cases hr : (0:ℝ) ≤ (ramw y : ℝ)
  · rw [if_pos hr, ellw, div_pow, Real.sq_sqrt hr, div_div_eq_mul_div]
    ring
  · rw [if_neg hr, ellw, Real.sqrt_eq_zero'.mpr (not_le.mp hr).le]
    simp

theorem slope_bounds : BoundsMu := by
  intro K _ _ _ _ K0 hK0 v0 hv0 D XE hD hXE Tup μ0 μ hμc hμfin XQ hXQ abelian₂ hLam ι hι J _ XW hXW
    M hM HT XT hHT0 hHTw Tl hT θ hθ κ hκ ρt ρr hρr hρ0 hρpos hρv hdet0 hdet Gm eb hLB hG nH Hm hH hHpos Pm hP
    hQ Mt hMt hLamP hGR R hR hRloc Sy Tw hTw hS hA0
    LG E3 E1 E2 elly gy Fy erry Jy ηy hF0 hGb hLG hI hJ hE1 hE2 hE3
  obtain ⟨err', Jx', η', -, hI', hJ', hs1, hs2, hs3⟩ := untwisted_choice (HeightOneSpectrum (𝓞 K)) J
    Sy Tw D hD hTw lw elly (fun y j => (idx y (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ))
    (fun y j => (idx (conjPl y) (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ))
    (fun y j => (jw (HT j (μ y)) y (Tl j (μ y)) : ℝ)) Fy erry Jy ηy hA0 hF0 hI hJ
  have hch := divisor_bounds_chain_weak K K0 hK0 v0 hv0 D XE hXE Tup μ0 μ hμc hμfin XQ hXQ abelian₂ hLam ι hι J
    (fun _ => D) XW hXW M hM HT XT hHT0 hHTw Tl hT θ hθ κ hκ ρt ρr hρr hρ0 hρpos hρv hdet0 hdet Gm eb hLB hG
    nH Hm hH hHpos Pm hP hQ Mt hMt hLamP hGR R hR hRloc Sy hS LG E3
    (fun j => lcv (XW j) (M j) / D) E1 E2 elly gy Fy err' Jx' η' hD hGb hLG (fun _ => le_rfl) hI' hJ'
    (fun j => by rw [hs1 j]; exact hE1 j) (fun j => by rw [hs2 j]; exact hE2 j) hE3
  have hF : ∑ j, ∑ y ∈ Sy, lw y * Fy y j = ∑ j, ∑ y ∈ Tw, lw y * Fy y j :=
    Finset.sum_congr rfl (fun j _ => hs3 j)
  rw [hF] at hch
  refine ⟨?_, fun j => ?_⟩
  · rw [dual_lattice_measure K D hD XE hXE R hR]
    exact hch
  · rw [Formalism.ExtensionFiltration.log_covolume_slope_mu K D hD (XW j) (hXW j) (M j) (hM j)]
    have : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    field_simp

end Formalism.DivisorInequality
