import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatToSpecField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSpMapEv
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_to_spec_field' : ∀ (K : Type) [Field K] (Z : Scheme.{0}) (f : Z ⟶ Sp K), Flat f := by
  first | exact @GlobalTheory.flat_to_spec_field | exact GlobalTheory.flat_to_spec_field | (intros; apply GlobalTheory.flat_to_spec_field <;> assumption)
