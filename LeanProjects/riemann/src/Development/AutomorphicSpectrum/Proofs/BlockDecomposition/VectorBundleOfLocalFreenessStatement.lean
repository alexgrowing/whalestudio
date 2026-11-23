import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VectorBundleOfLocalFreeness
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vector_bundle_of_local_freeness : ∀ (R W : Type) [CommRing R] [AddCommGroup W] [Module R W] (g : ℕ), (∀ p : PrimeSpectrum R, ∃ r : R, r ∉ p.asIdeal ∧ Module.Free (Localization.Away r) (Localization.Away r ⊗[R] W) ∧ Module.Finite (Localization.Away r) (Localization.Away r ⊗[R] W) ∧ Module.finrank (Localization.Away r) (Localization.Away r ⊗[R] W) = g) → VB R W g := by
  first | exact @GlobalTheory.CompanionTheory.Cot.vb_of_free_on_basicOpens | exact GlobalTheory.CompanionTheory.Cot.vb_of_free_on_basicOpens | (intros; apply GlobalTheory.CompanionTheory.Cot.vb_of_free_on_basicOpens <;> assumption)
