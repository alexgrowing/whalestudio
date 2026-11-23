import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalModelGenericFibreIso
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCoordMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toroidal_model_generic_fibre_iso : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F)
    {X W : Scheme.{0}} {jB : W ⟶ X} {πB : W ⟶ gen Z},
    ∀ (M M' : X.Modules) (r : ℕ) (τ : E →+* ℂ) (t : FrAssign Z M r jB) (t' : FrAssign Z M' r jB),
    IsLieFrames Z e jB πB M r τ false t → IsLieFrames Z e jB πB M' r τ false t' →
    ∀ (ι : Type) (U : ι → X.Opens), (∀ x : X, ∃ i, x ∈ U i) → ∀ (f : ∀ i, Fin r → Γ(M, U i))
    (hf : ∀ i, VB.IsFrame (f i)) (f' : ∀ i, Fin r → Γ(M', U i)) (hf' : ∀ i, VB.IsFrame (f' i))
    (A : ∀ i, Matrix (Fin r) (Fin r) Γ(X, U i)), (∀ i, GlobalTheory.TwoLat.IsCoordMat Z jB πB t t' (hf i) (hf' i) (A i)) →
    ∀ g : M ⟶ M', (∀ i a, g.app (U i) (f i a) = ∑ b, A i b a • f' i b) → GlobalTheory.TwoLat.Matches Z jB πB g t t' := by
  first | exact @GlobalTheory.TwoLat.matches_of_charts | exact GlobalTheory.TwoLat.matches_of_charts | (intros; apply GlobalTheory.TwoLat.matches_of_charts <;> assumption)
