import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodLevelMultipleSameAdelicPart
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionValuationBoundsDifferent
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_goodLevel_multiple_same_adelicPart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H), ∃ l₂ : Level H, l.Dvd l₂ ∧ l₂.A = l.A ∧ ∀ q : ℕ, q.Prime → l₂.GoodAt q := by
  first | exact @GlobalTheory.GoodMultipleLevel.exists_good_multiple | exact GlobalTheory.GoodMultipleLevel.exists_good_multiple | (intros; apply GlobalTheory.GoodMultipleLevel.exists_good_multiple <;> assumption)
