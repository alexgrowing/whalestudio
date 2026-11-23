import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenbundleFrameAffineAtlas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSpMapEv
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigenbundleFrameAffineAtlas : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)), PushInvertible Y.t.G Y.t.PP.L → Nonempty (Atlas Y p) := by
  first | exact @GlobalTheory.FlagMod.FieldFlag.exists_atlas | exact GlobalTheory.FlagMod.FieldFlag.exists_atlas | (intros; apply GlobalTheory.FlagMod.FieldFlag.exists_atlas <;> assumption)
