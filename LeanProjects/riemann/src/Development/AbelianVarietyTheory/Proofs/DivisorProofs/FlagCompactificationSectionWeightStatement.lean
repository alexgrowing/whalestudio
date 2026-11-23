import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCompactificationSectionWeight
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DrAtNonneg
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenframeGenericAffineOpen
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
open AlgebraicGeometry CategoryTheory
open GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_compactification_section_weight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (C : FlagCpt Z e) (ex : Ix Dw → ℤ) (g : Rul Xo c), ex none = 0 → g ∈ AllWt.secZ Xo c ex → ∀ (K : Type) [Field K] [Algebra c.F K] (yC : FrPt Xo c K) (xg : Sp K ⟶ Z.X) (gf : EigFrame Z (algebraMap c.F K) xg), (∀ τ i, ∃ w : Sp (DualNumber K) ⟶ Z.oF.t.G.left, w ≫ Z.oF.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ AllWt.ptF yC ∧ w ≫ Z.m0.toSABMap.φ = yC.u τ i ∧ w ≫ Z.m.φ = gf.v τ i) → ∀ x : Sp K ⟶ C.Y.X, x ≫ C.π = AllWt.ptF yC ≫ Z.jQ → C.Carries x gf → IsCoord C x gf (fun z => -ex (some z)) (C.val g) (evR Xo c g yC) := by
  first | exact @GlobalTheory.ShFam.CoordField.isCoord_val_field | exact GlobalTheory.ShFam.CoordField.isCoord_val_field | (intros; apply GlobalTheory.ShFam.CoordField.isCoord_val_field <;> assumption)
