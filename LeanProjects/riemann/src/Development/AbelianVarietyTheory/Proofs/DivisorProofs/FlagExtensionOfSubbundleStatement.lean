import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagExtensionOfSubbundle
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_extension_of_subbundle : ∀ (X : Scheme.{0}) (E K : X.Modules) (i : K ⟶ E) (r : ℕ), IsSubbundle i → IsVB E (r + 1) → Vert.Flag K r → Nonempty (Vert.Flag E (r + 1)) := by
  first | exact @GlobalTheory.Vert.Flag.nonempty_extend | exact GlobalTheory.Vert.Flag.nonempty_extend | (intros; apply GlobalTheory.Vert.Flag.nonempty_extend <;> assumption)
