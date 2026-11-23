import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricChartsOfIso
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toric_charts_of_iso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (Z : GMod Xo c) (e : gen Y ≅ gen Z), Y.jQ ≫ e.hom = Z.jQ → (∀ x ∈ genBd Y, HasToricChart Y x) → ∀ x ∈ genBd Z, HasToricChart Z x := by
  first | exact @GlobalTheory.TorRef.hasToricChart_of_genIso | exact GlobalTheory.TorRef.hasToricChart_of_genIso | (intros; apply GlobalTheory.TorRef.hasToricChart_of_genIso <;> assumption)
