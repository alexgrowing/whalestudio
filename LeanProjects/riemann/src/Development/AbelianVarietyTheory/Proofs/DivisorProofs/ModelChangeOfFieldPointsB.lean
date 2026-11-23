import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocGrLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFlagged
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCoordMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalModelBaseChangeNormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalModelFibreProductNormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalModelGenericFibreIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonAffineFramesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueMorphismOfCompatibleFramesStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwoLat

theorem exists_incl_matches : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
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
  intro E _ _ _ H Dw l Xo c Oz _ β Z F _ _ e X W q jB πB d hq hn pb M M' r τ t t' hM hM' ht ht' hL hG
  choose V f f' hf hf' hV hxV using fun x : X => GlobalTheory.T.exists_common_affine_frames' X M M' r hM hM' x
  choose A hA using fun x : X => GlobalTheory.T.exists_isCoordMat_of_isLieLat_of_isGrLat Z e hq hn pb M M' r τ t t' ht ht' hL hG (V x) (hV x) (f x) (hf x)
    (f' x) (hf' x)
  obtain ⟨g, hg⟩ := GlobalTheory.T.glue_morphism_of_compatible_frames X M M' r X V (fun x => ⟨x, hxV x⟩) f hf (fun x a => ∑ b, A x b a • f' x b)
    (fun i j a => GlobalTheory.T.toroidal_model_fibre_product_normal Z e hq pb M M' r τ t t' ht ht' (V i) (V j) (f i) (hf i) (f' i) (hf' i) (f j) (hf j)
      (f' j) (hf' j) (A i) (A j) (hA i) (hA j) a)
  exact ⟨g, GlobalTheory.T.toroidal_model_generic_fibre_iso Z e M M' r τ t t' ht ht' X V (fun x => ⟨x, hxV x⟩) f hf f' hf' A hA g hg⟩

end GlobalTheory.TwoLat

end
