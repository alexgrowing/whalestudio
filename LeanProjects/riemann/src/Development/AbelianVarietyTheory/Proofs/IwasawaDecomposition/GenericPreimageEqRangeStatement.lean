import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericPreimageEqRange
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_preimage_eq_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (X : Model Xo c β) (Y : Model Xo c (RingHom.id c.F))
    (ρ : gen Y ⟶ gen X), Y.jQ ≫ ρ = X.jQ → ρ ⁻¹' Set.range X.jQ = Set.range Y.jQ := by
  first | exact @GlobalTheory.TorRef.preimage_range_jQ_eq | exact GlobalTheory.TorRef.preimage_range_jQ_eq | (intros; apply GlobalTheory.TorRef.preimage_range_jQ_eq <;> assumption)
