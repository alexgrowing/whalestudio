import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzArchContinuousIntegrable
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSplitK
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_arch_continuous_integrable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (κ : Ainf F ⊗[F] E ≃+* (NumberField.InfinitePlace F → ℂ)), IsHomeomorph κ → ∀ (n M d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzArch φ → Continuous φ ∧ Integrable φ (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M) ∧ (∃ B : ℝ, ∀ X, ‖φ X‖ ≤ B) ∧ ∀ k : ℕ, ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ X, X ∉ GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ (fun _ _ => R) → ‖φ X‖ ≤ C / R ^ k := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.AvgInf.SchwartzTuple.schwartzArch_facts | exact GlobalTheory.CompanionTheory.WhitFree.AvgInf.SchwartzTuple.schwartzArch_facts | (intros; apply GlobalTheory.CompanionTheory.WhitFree.AvgInf.SchwartzTuple.schwartzArch_facts <;> assumption)
