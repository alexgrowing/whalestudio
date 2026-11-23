import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalModelBaseChangeNormal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCoordMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isCoordMat_of_isLieLat_of_isGrLat : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F)
    {X W : Scheme.{0}} {q : X ⟶ Sp (𝓞 F)} {jB : W ⟶ X} {πB : W ⟶ gen Z} {d : ℕ}, IsArithVar q d →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X →
    IsPullback jB (πB ≫ genStr Z ≫ spMap e.toRingHom) q (spMap (algebraMap (𝓞 F) F)) →
    ∀ (M M' : X.Modules) (r : ℕ) (τ : E →+* ℂ) (t : FrAssign Z M r jB) (t' : FrAssign Z M' r jB),
    IsLieFrames Z e jB πB M r τ false t → IsLieFrames Z e jB πB M' r τ false t' →
    IsLieLat Z e jB πB M r τ (ArIn.ind ∅) (fun _ => True) t → GlobalTheory.TwoLat.IsGrLat Z e jB πB M' r τ t' →
    ∀ (V : X.Opens), IsAffineOpen V → ∀ (f : Fin r → Γ(M, V)) (hf : VB.IsFrame f) (f' : Fin r → Γ(M', V))
    (hf' : VB.IsFrame f'), ∃ A : Matrix (Fin r) (Fin r) Γ(X, V), GlobalTheory.TwoLat.IsCoordMat Z jB πB t t' hf hf' A := by
  first | exact @GlobalTheory.TwoLat.CoordReg.exists_isCoordMat | exact GlobalTheory.TwoLat.CoordReg.exists_isCoordMat | (intros; apply GlobalTheory.TwoLat.CoordReg.exists_isCoordMat <;> assumption)
