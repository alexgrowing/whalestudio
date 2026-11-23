import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericFiniteByInduction
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_finite_by_induction : (∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), CuspFin E a) → (∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), (∀ b < a, GenFin E b) → ∀ r, 0 < r → r < a → CTFin E a r) → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), GenFin E a := by
  first | exact @GlobalTheory.CompanionTheory.AffglAssembly.genFin_of_chapters | exact GlobalTheory.CompanionTheory.AffglAssembly.genFin_of_chapters | (intros; apply GlobalTheory.CompanionTheory.AffglAssembly.genFin_of_chapters <;> assumption)
