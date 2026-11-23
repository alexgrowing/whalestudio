import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetInd
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WS

theorem unramified_apply_eq_zpow_ord {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {μ : Fˣ →* ℂˣ} (hμ : IsUnramifiedChar μ) (u : Fˣ) :
    ((μ u : ℂˣ) : ℂ) = ((μ (unifUnit F) : ℂˣ) : ℂ) ^ ord (u : F) := by
  have h0 : (unifUnit F ^ (-ord (u : F)) * u) ∈ ordShell F 0 := by
    rw [mem_ordShell, ord_units_mul, ord_unifUnit_zpow]
    omega
  have h1 : μ (unifUnit F ^ (-ord (u : F)) * u) = 1 := isUnramifiedChar_iff.mp hμ _ h0
  have h2 : μ u = μ (unifUnit F) ^ ord (u : F) := by
    rw [map_mul, map_zpow, _root_.zpow_neg] at h1
    exact (inv_mul_eq_one.mp h1).symm
  rw [h2, Units.val_zpow_eq_zpow_val]

theorem integral_unramified_shells : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (μ : Fˣ →* ℂˣ), IsUnramifiedChar μ → ∀ A D : ℤ, ∫ u : Fˣ, (if -A ≤ ord (u : F) ∧ ord (u : F) ≤ -D then ((μ u : ℂˣ) : ℂ) else 0) ∂multHaar F = ∑ j ∈ Finset.Icc D A, ((μ (unifUnit F) : ℂˣ) : ℂ) ^ (-j) := by
  intro F _ _ _ _ _ _ μ hμ A D
  have hpt : (fun u : Fˣ => if -A ≤ ord (u : F) ∧ ord (u : F) ≤ -D then ((μ u : ℂˣ) : ℂ) else 0) =
      fun u => ∑ j ∈ Finset.Icc D A,
        (ordShell F (-j)).indicator (fun _ => ((μ (unifUnit F) : ℂˣ) : ℂ) ^ (-j)) u := by
    funext u
    by_cases h : -A ≤ ord (u : F) ∧ ord (u : F) ≤ -D
    · rw [if_pos h, Finset.sum_eq_single (-ord (u : F))]
      · rw [Set.indicator_of_mem (by rw [mem_ordShell]; omega), neg_neg,
          unramified_apply_eq_zpow_ord hμ]
      · intro j _ hj
        refine Set.indicator_of_notMem (fun hu => hj ?_) _
        rw [mem_ordShell] at hu
        omega
      · intro hn
        exact absurd (Finset.mem_Icc.mpr (by omega)) hn
    · rw [if_neg h]
      symm
      refine Finset.sum_eq_zero fun j hj => Set.indicator_of_notMem (fun hu => h ?_) _
      rw [mem_ordShell] at hu
      have := Finset.mem_Icc.mp hj
      omega
  have hint : ∀ j : ℤ, Integrable
      ((ordShell F (-j)).indicator (fun _ => ((μ (unifUnit F) : ℂˣ) : ℂ) ^ (-j))) (multHaar F) := by
    intro j
    rw [integrable_indicator_iff (measurableSet_ordShell _)]
    exact integrableOn_const (by rw [multHaar_ordShell]; exact ENNReal.one_ne_top)
  rw [hpt, integral_finset_sum _ fun j _ => hint j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_indicator (measurableSet_ordShell _), setIntegral_const, measureReal_def,
    multHaar_ordShell]
  simp

end GlobalTheory.CompanionTheory.WS
