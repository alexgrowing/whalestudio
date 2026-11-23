import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapLinearEquivAddHaarLocalFieldStatement

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem map_mul_left_eq_norm_smul (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (z : Eˣ) :
    μ.map (fun x => (z : E) * x) =
      (distribHaarChar F ((Units.map (Algebra.norm F : E →* F)) z))⁻¹ • μ := by
  obtain ⟨b, -, -⟩ := hE.basis
  have : FiniteDimensional F E := Module.Finite.of_basis b
  let T : E ≃ₗ[F] E :=
    { LinearMap.mulLeft F (z : E) with
      invFun := fun x => ((z⁻¹ : Eˣ) : E) * x
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  have hT : LinearEquiv.det T = Units.map (Algebra.norm F : E →* F) z := by
    ext
    rw [LinearEquiv.coe_det, Units.coe_map, Algebra.norm_apply]
    rfl
  rw [← hT]
  exact GlobalTheory.T.map_linearEquiv_addHaar_localField F E μ T

end GlobalTheory.KSp
