import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeometricSumBelowThreshold
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol

namespace GlobalTheory.CompanionTheory.ModulusWeight

theorem integrable_modulus_rpow_indicator : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (δ B : ℝ), 0 < δ → Integrable (fun a : Fˣ => Set.indicator {a : Fˣ | (modulus (a : F) : ℝ) ≤ B} (fun a : Fˣ => (modulus (a : F) : ℝ) ^ δ) a) (multHaar F) := by
  intro F _ _ _ _ _ _ δ B hδ
  have hq : (1 : ℝ) < residueCard F := by exact_mod_cast one_lt_residueCard (K := F)
  have hq0 : (0 : ℝ) < residueCard F := zero_lt_one.trans hq
  have hmod : ∀ u : Fˣ, (modulus (u : F) : ℝ) = (residueCard F : ℝ) ^ (-ord (u : F)) := fun u => by
    rw [modulus_of_ne_zero u.ne_zero, NNReal.coe_zpow, NNReal.coe_natCast]
  by_cases hB : 0 < B
  swap
  · have hz : (fun a : Fˣ => Set.indicator {a : Fˣ | (modulus (a : F) : ℝ) ≤ B}
        (fun a : Fˣ => (modulus (a : F) : ℝ) ^ δ) a) = 0 := by
      funext u
      refine Set.indicator_of_notMem ?_ _
      simp only [Set.mem_setOf_eq, not_le, hmod]
      exact (not_lt.mp hB).trans_lt (zpow_pos hq0 _)
    rw [hz]
    exact integrable_zero _ _ _
  have hm : Continuous fun a : Fˣ => (modulus (a : F) : ℝ) :=
    NNReal.continuous_coe.comp (continuous_modulus.comp Units.continuous_val)
  have hS : MeasurableSet {a : Fˣ | (modulus (a : F) : ℝ) ≤ B} :=
    (isClosed_le hm continuous_const).measurableSet
  have hc : Continuous fun a : Fˣ => (modulus (a : F) : ℝ) ^ δ :=
    hm.rpow_const fun _ => Or.inr hδ.le
  refine ⟨hc.aestronglyMeasurable.indicator hS, ?_⟩
  let b : ℤ → ENNReal := fun n => if (residueCard F : ℝ) ^ n ≤ B then
    ENNReal.ofReal ((residueCard F : ℝ) ^ (δ * (n : ℝ))) else 0
  have hbound : ∀ u : Fˣ, ‖Set.indicator {a : Fˣ | (modulus (a : F) : ℝ) ≤ B}
      (fun a : Fˣ => (modulus (a : F) : ℝ) ^ δ) u‖ₑ ≤ (fun k : ℤ => b (-k)) (ord (u : F)) := by
    intro u
    by_cases hu : (modulus (u : F) : ℝ) ≤ B
    · have hu' : (residueCard F : ℝ) ^ (-ord (u : F)) ≤ B := hmod u ▸ hu
      rw [Set.indicator_of_mem (by exact hu)]
      simp only [b]
      rw [if_pos hu', ← ofReal_norm, Real.norm_of_nonneg (by positivity), hmod u,
        ← Real.rpow_intCast, ← Real.rpow_mul hq0.le, mul_comm]
    · rw [Set.indicator_of_notMem (by exact hu), enorm_zero]
      exact bot_le
  have hle := lintegral_multHaar_le_tsum (K := F) _ (fun k : ℤ => b (-k)) hbound
  have hsum : ∑' k : ℤ, b (-k) = ∑' n : ℤ, b n := (Equiv.neg ℤ).tsum_eq b
  rw [hsum] at hle
  exact hle.trans_lt ((GlobalTheory.CompanionTheory.GeomSum.tsum_zpow_le_rpow_div _ δ B hq hδ hB).trans_lt ENNReal.ofReal_lt_top)

end GlobalTheory.CompanionTheory.ModulusWeight
