import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormGroupIndexTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GTil
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_group_index_two : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (η : Fˣ →* ℂˣ), Continuous η → (∀ a : Fˣ, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) → ∀ κ : ℝ, FibProp F E κ → ∀ f : F → ℂ, f ∈ schwartzBruhat F → localZeta (fun x : E => f (Algebra.norm F x)) 1 (1 / 2) = (κ / 2 : ℂ) * (localZeta f 1 (1 / 2) + localZeta f η (1 / 2)) := by
  first | exact @GlobalTheory.CompanionTheory.GaussLam.localZeta_comp_norm_half | exact GlobalTheory.CompanionTheory.GaussLam.localZeta_comp_norm_half | (intros; apply GlobalTheory.CompanionTheory.GaussLam.localZeta_comp_norm_half <;> assumption)
