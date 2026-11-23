import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectOfGenericIso
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.LBSpreads
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.SpreadingModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perfect_of_generic_iso : ∀ {R : Type} [CommRing R] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of R)) {M M' : LB Y}, M.IsLB → M'.IsLB → ∀ (w : LB.Iso M M'), w.IsGen → Perf f M' → Nonempty (Perf f M) := by
  first | exact @GlobalTheory.CompanionTheory.PerfIso.perf_of_iso | exact GlobalTheory.CompanionTheory.PerfIso.perf_of_iso | (intros; apply GlobalTheory.CompanionTheory.PerfIso.perf_of_iso <;> assumption)
