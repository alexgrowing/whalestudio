import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmplePullbackOfInducedHermitianBundle
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open NumberField CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.Mean4O

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_pullback_of_induced_hermitian_bundle : ∀ {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F} (V : Cover Y) (A : Adl C Y) (L : HermLB V.p) (k : ℕ), 0 < k → V.Induces A L k → Y.ample A.D → IsAmpleLB (L.B.pull V.j) := by
  first | exact @GlobalTheory.Mean4O.Cover.isAmpleLB_pull_of_induces | exact GlobalTheory.Mean4O.Cover.isAmpleLB_pull_of_induces | (intros; apply GlobalTheory.Mean4O.Cover.isAmpleLB_pull_of_induces <;> assumption)
