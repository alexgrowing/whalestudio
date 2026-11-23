import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSmoothCharCompNorm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WcEqZero
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol
open GlobalTheory.CompanionTheory.WcB
open scoped Topology

namespace GlobalTheory.CompanionTheory.WcB

theorem continuous_gaussI : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle), Continuous χ → ∀ (μ : Measure E) [μ.IsAddHaarMeasure] (Φ : E → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ → Continuous fun p : F × E => gaussI χ μ Φ p.1 p.2 := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ χ hχ μ _ Φ hΦ hΦc
  haveI := GroundTheory.LocalField.isModuleTopology F E
  have hc : Continuous (algebraMap F E) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap F E)
  have hTr : Continuous (Algebra.trace F E) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace F E)
  have hN : Continuous (Algebra.norm F : E → F) := GlobalTheory.LBC.Inh.continuous_algNorm hc
  have hΦ' : Continuous Φ := hΦ.continuous
  have hint : Integrable Φ μ := hΦ'.integrable_of_hasCompactSupport hΦc
  unfold gaussI
  refine continuous_of_dominated (bound := fun u => ‖Φ u‖) ?_ ?_ hint.norm ?_
  · intro p
    refine Continuous.aestronglyMeasurable ?_
    refine Continuous.mul ?_ hΦ'
    refine continuous_subtype_val.comp (hχ.comp ?_)
    exact (continuous_const.mul hN).sub (hTr.comp (continuous_const.mul continuous_id))
  · intro p
    refine Filter.Eventually.of_forall fun u => ?_
    rw [norm_mul, Circle.norm_coe, one_mul]
  · refine Filter.Eventually.of_forall fun u => ?_
    refine Continuous.mul ?_ continuous_const
    refine continuous_subtype_val.comp (hχ.comp ?_)
    exact (continuous_fst.mul continuous_const).sub
      (hTr.comp (continuous_snd.mul continuous_const))

end GlobalTheory.CompanionTheory.WcB
