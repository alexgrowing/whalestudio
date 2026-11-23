import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzNormFormPullback
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GTil
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_norm_form_pullback : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (f : F → ℂ), f ∈ schwartzBruhat F → (fun x : E => f (Algebra.norm F x)) ∈ schwartzBruhat E := by
  first | exact @GlobalTheory.CompanionTheory.NormSB.comp_norm_mem_schwartzBruhat | exact GlobalTheory.CompanionTheory.NormSB.comp_norm_mem_schwartzBruhat | (intros; apply GlobalTheory.CompanionTheory.NormSB.comp_norm_mem_schwartzBruhat <;> assumption)
