import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleSectionsAvoidClosedPoints
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open NumberField CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.Mean4O

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_sections_avoid_closed_points : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) (L M : HermLB V.p), IsAmpleLB (L.B.pull V.j) → ∃ (n m : ℕ) (s : Fin m → (ArInt.comb ![L, M] ![(n : ℤ), 1]).B.Sec), ∀ w : V.G, IsClosed ({w} : Set V.G) → ∃ i, V.j w ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s i) := by
  first | exact @GlobalTheory.GenFibreSecs.main | exact GlobalTheory.GenFibreSecs.main | (intros; apply GlobalTheory.GenFibreSecs.main <;> assumption)
