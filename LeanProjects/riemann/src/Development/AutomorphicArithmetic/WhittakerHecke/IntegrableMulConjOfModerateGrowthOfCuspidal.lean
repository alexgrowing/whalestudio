import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CapRDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.ContinuousLev
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.UmgOps
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.RapidDecay
open MeasureTheory NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW

theorem UpperTheory.integrable_mul_conj_of_moderateGrowth_of_cuspidal :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r : ℕ) (Φ ψ : Sm E r), 0 < r → Umg Φ → Umg ψ → Cusp ψ.1 →
          Integrable (fun y => onQ Φ.1 y * starRingEnd ℂ (onQ ψ.1 y)) (muQ E r) := by
  intro E _ _ _ r Φ ψ _ hΦ hψ hc
  obtain ⟨N, hN⟩ := hΦ.growth
  obtain ⟨B, hB⟩ := hN 1
  rw [map_one] at hB
  obtain ⟨C, hC⟩ := rapidDecay E r ψ hψ hc N
  exact Pair.pair_int hΦ.left hψ.left ((umgOps E r).2 Φ hΦ).1 ((umgOps E r).2 ψ hψ).1 (fun x => hB x) hC
