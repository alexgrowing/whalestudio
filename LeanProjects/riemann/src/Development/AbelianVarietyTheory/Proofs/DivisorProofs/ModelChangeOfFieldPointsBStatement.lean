import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelChangeOfFieldPointsB
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocGrLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFlagged
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_change_of_field_points_b : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F)
    {X W : Scheme.{0}} {q : X ⟶ Sp (𝓞 F)} {jB : W ⟶ X} {πB : W ⟶ gen Z} {d : ℕ}, IsArithVar q d →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X →
    IsPullback jB (πB ≫ genStr Z ≫ spMap e.toRingHom) q (spMap (algebraMap (𝓞 F) F)) →
    ∀ (M M' : X.Modules) (r : ℕ) (τ : E →+* ℂ) (t : FrAssign Z M r jB) (t' : FrAssign Z M' r jB),
    IsVB M r → IsVB M' r → IsLieFrames Z e jB πB M r τ false t → IsLieFrames Z e jB πB M' r τ false t' →
    IsLieLat Z e jB πB M r τ (ArIn.ind ∅) (fun _ => True) t → GlobalTheory.TwoLat.IsGrLat Z e jB πB M' r τ t' →
    ∃ g : M ⟶ M', GlobalTheory.TwoLat.Matches Z jB πB g t t' := by
  first | exact @GlobalTheory.TwoLat.exists_incl_matches | exact GlobalTheory.TwoLat.exists_incl_matches | (intros; apply GlobalTheory.TwoLat.exists_incl_matches <;> assumption)
