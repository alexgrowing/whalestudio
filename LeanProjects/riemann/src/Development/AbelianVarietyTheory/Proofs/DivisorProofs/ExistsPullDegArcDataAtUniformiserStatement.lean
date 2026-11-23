import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullDegArcDataAtUniformiser
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedLevelPointsOfLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PelOKOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegCompOfInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pullDeg_arcData_at_uniformiser : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (T : Formalism.L2.Pj.CDVR) (b : O →+* T.V) (D : DegData T.V (maximalIdeal T.V)) [Module (𝓞 E) D.toPre.X] (oD : letI := H.starRing; D.toPre.OAct (𝓞 E)) (ϖ : T.V) (hϖ : Irreducible ϖ) (hX : Nontrivial D.toPre.X) (hw : letI := H.starRing; TraceFormTwistIso D.toPre oD H.w0) (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ GlobalTheory.TraitArc.beF D hϖ a a') (pA : Dm.La → QkPt D.toPre (FractionRing T.V) l.A) (pM : Dm.La → QkPt D.toPre (FractionRing T.V) l.M) (hLie : GlobalTheory.TraitArc.LieCl D oD Dm β b) (hTate : GlobalTheory.TraitArc.TateCl D oD hϖ Dm β b hdiv pA pM) (Xo : Moduli Dm l) (Y : Model Xo c β) (y : Sp T.V ⟶ Y.X), Y.HasArcData (GlobalTheory.TraitArc.arc D oD hϖ β b hX hw hdiv pA pM hLie hTate) (maximalIdeal T.V) (RingHom.id T.V) ϖ y → ∃ (t : SAB H (Sp T.V)) (_ : SABMap t Y.t y) (P : PELUnif (maximalIdeal T.V) t), Nonempty (IsPullDeg (RingHom.id T.V) D.toPre P.D.toPre) := by
  first | exact @GlobalTheory.TraitArcMatch.exists_isPullDeg_arc | exact GlobalTheory.TraitArcMatch.exists_isPullDeg_arc | (intros; apply GlobalTheory.TraitArcMatch.exists_isPullDeg_arc <;> assumption)
