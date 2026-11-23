import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationPartBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemiabelianExtensionDvr
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mean4 GlobalTheory.Mean4O
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_part_base_change : ∀ (O : Type) [CommRing O] (c : O →+* O) (K K' : Type) [Field K] [Field K'] (f : K →+* K') (G : Over (Sp K)) [GrpObj G] (i : OAct O G) (G' : Over (Sp K')) [GrpObj G'] (i' : OAct O G') (φ : G'.left ⟶ G.left), IsActPull i' i (spMap f) φ → PolPart c i → PolPart c i' := by
  first | exact @GlobalTheory.PolPartPull.polPart_of_isActPull | exact GlobalTheory.PolPartPull.polPart_of_isActPull | (intros; apply GlobalTheory.PolPartPull.polPart_of_isActPull <;> assumption)
