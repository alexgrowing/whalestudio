import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiPshPotentialFundamentalWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open AlgebraicGeometry CategoryTheory MeasureTheory Set GlobalTheory.ShFam GlobalTheory.ChernReg GlobalTheory.CxPts GlobalTheory.TrueGeo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ProjVar Formalism.L2.Pj Formalism.L2.Geo GlobalTheory
open ReciprocityTheory.AnForm.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasi_psh_potential_fundamental_weight : Hypotheses2 → HypothesesH → OnObj fun D O _ T _ R => ∀ c a τ (i : Fin O.N), (i : ℕ) + 1 < O.N → ∃ v : (T.M c).X a → EReal, GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.IsQuasiPsh ((T.M c).A a) ((T.F c).th (fund τ i) a) v ∧ ∀ z, z ∉ (T.M c).Z a → v z = ((2 * (T.F c).ph (fund τ i) a z : ℝ) : EReal) := by
  first | exact @GlobalTheory.FundWeightExt.exists_quasiPsh_ext | exact GlobalTheory.FundWeightExt.exists_quasiPsh_ext | (intros; apply GlobalTheory.FundWeightExt.exists_quasiPsh_ext <;> assumption)
