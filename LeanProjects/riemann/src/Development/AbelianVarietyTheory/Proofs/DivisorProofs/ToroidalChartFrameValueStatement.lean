import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalChartFrameValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUniOne
open NumberField CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.TrueGeo
open GlobalTheory.LieVB (omega)
open GlobalTheory.LocM (tanEv)
open Formalism.MainNotions.DIV.Cons (intO)
open scoped Classical
open GlobalTheory.LieFilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bijective_mulVec_of_isTanMat_of_isEigBasis : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {K : Type} [CommRing K] (φ : c.F →+* K) (x : Sp K ⟶ Z.X)
    {g : ℕ} (ch : VB.Chart (omega Z.t.G) g), ⊤ ≤ x ⁻¹ᵁ ch.U →
    ∀ {r : (E →+* ℂ) → ℕ} (u : ∀ τ, Fin (r τ) → (Sp (DualNumber K) ⟶ Z.t.G.left)), (∀ τ, IsEigBasis Z φ x τ (u τ)) →
    ∀ P : Matrix (Fin g) (Σ τ, Fin (r τ)) K, IsTanMat Z x ch (fun s : Σ τ, Fin (r τ) => u s.1 s.2) P →
    Function.Bijective P.mulVec := by
  first | exact @GlobalTheory.LieFilt.bijective_mulVec_of_eigBases | exact GlobalTheory.LieFilt.bijective_mulVec_of_eigBases | (intros; apply GlobalTheory.LieFilt.bijective_mulVec_of_eigBases <;> assumption)
