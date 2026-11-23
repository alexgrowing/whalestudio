import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoordinateSectionsOfWeight
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoordAtConstMulIff
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coordinate_sections_of_weight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (Y : FlagCpt Z e) (k : Type) [Field k] [Algebra c.F k] (P : FrPt Xo c k) (ex : Ix Dw → ℤ), ex none = 0 → ∀ f ∈ GlobalTheory.AllWt.secZ Xo c ex, ∀ a : k, CoordAt Y P (fun z => -ex (some z)) (Y.val f) a ↔ Carried Y P ∧ a = evR Xo c f P := by
  first | exact @GlobalTheory.ShFam.ValCoord.coordAt_val_iff | exact GlobalTheory.ShFam.ValCoord.coordAt_val_iff | (intros; apply GlobalTheory.ShFam.ValCoord.coordAt_val_iff <;> assumption)
