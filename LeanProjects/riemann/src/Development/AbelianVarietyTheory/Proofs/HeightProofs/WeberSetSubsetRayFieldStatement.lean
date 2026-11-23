import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberSetSubsetRayField
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weber_set_subset_ray_field : ∀ (K : IntermediateField ℚ ℂ) [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → discr K < -4 → ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) → ∀ n : ℕ, Odd n → 3 ≤ n → ∀ (R : IntermediateField K ℂ) [NumberField R] [IsAbelianGalois K R], IsRay R (Ideal.span {(n : 𝓞 K)}) → weberSet L n ⊆ R := by
  first | exact @GlobalTheory.FieldSize.InRay.weberSet_subset | exact GlobalTheory.FieldSize.InRay.weberSet_subset | (intros; apply GlobalTheory.FieldSize.InRay.weberSet_subset <;> assumption)
