import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalModelFibreProductNormal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCoordMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toroidal_model_fibre_product_normal : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F)
    {X W : Scheme.{0}} {q : X ⟶ Sp (𝓞 F)} {jB : W ⟶ X} {πB : W ⟶ gen Z} {d : ℕ}, IsArithVar q d →
    IsPullback jB (πB ≫ genStr Z ≫ spMap e.toRingHom) q (spMap (algebraMap (𝓞 F) F)) →
    ∀ (M M' : X.Modules) (r : ℕ) (τ : E →+* ℂ) (t : FrAssign Z M r jB) (t' : FrAssign Z M' r jB),
    IsLieFrames Z e jB πB M r τ false t → IsLieFrames Z e jB πB M' r τ false t' →
    ∀ (U U' : X.Opens) (f : Fin r → Γ(M, U)) (hf : VB.IsFrame f) (f' : Fin r → Γ(M', U)) (hf' : VB.IsFrame f')
    (g : Fin r → Γ(M, U')) (hg : VB.IsFrame g) (g' : Fin r → Γ(M', U')) (hg' : VB.IsFrame g')
    (A : Matrix (Fin r) (Fin r) Γ(X, U)) (A' : Matrix (Fin r) (Fin r) Γ(X, U')),
    GlobalTheory.TwoLat.IsCoordMat Z jB πB t t' hf hf' A → GlobalTheory.TwoLat.IsCoordMat Z jB πB t t' hg hg' A' → ∀ a : Fin r,
    Twist.resM M' (inf_le_right : U ⊓ U' ≤ U') (∑ b, A' b a • g' b) =
      ∑ b, trCo hf g b a • Twist.resM M' (inf_le_left : U ⊓ U' ≤ U) (∑ k, A k b • f' k) := by
  first | exact @GlobalTheory.TwoLat.coordMat_compat | exact GlobalTheory.TwoLat.coordMat_compat | (intros; apply GlobalTheory.TwoLat.coordMat_compat <;> assumption)
