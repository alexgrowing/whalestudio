import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCentreAnnihilatorCompatibleMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_centreAnnihilatorCompatibleMaps : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsAutForm φ → ∀ L : Subgroup (GL (Fin a) (Af E)), IsOpen (L : Set (GL (Fin a) (Af E))) → FiniteDimensional ℂ (mapsJ φ L) := by
  first | exact @GlobalTheory.AutGrowth.KilledFin.finiteDimensional_mapsJ | exact GlobalTheory.AutGrowth.KilledFin.finiteDimensional_mapsJ | (intros; apply GlobalTheory.AutGrowth.KilledFin.finiteDimensional_mapsJ <;> assumption)
