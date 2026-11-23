import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalNonarchimedeanPoint
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
theorem _root_.GlobalTheory.T.toroidal_nonarchimedean_point : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (φ : c.F →+* C)
    (xO : Sp ↥(intO C) ⟶ Z.X) (x : Sp C ⟶ Z.X), spMap (intO C).subtype ≫ xO = x →
    ∀ {g : ℕ} (ch : VB.Chart (omega Z.t.G) g), ⊤ ≤ xO ⁻¹ᵁ ch.U →
    ∀ {r : (E →+* ℂ) → ℕ} (u : ∀ τ, Fin (r τ) → (Sp (DualNumber C) ⟶ Z.t.G.left)), (∀ τ, IsEigBasis Z φ x τ (u τ)) →
    (∀ τ w, IsEigTan Z φ x τ w →
      ((∃ a : Fin (r τ) → C, (∀ i, ‖a i‖ ≤ 1) ∧ IsCombAtG Z.t x (u τ) a w) ↔ InGr Z φ x (latDR Z.t x) τ w)) →
    ∀ P : Matrix (Fin g) (Σ τ, Fin (r τ)) C, IsTanMat Z x ch (fun s : Σ τ, Fin (r τ) => u s.1 s.2) P →
    GrCond (fun s : Σ τ, Fin (r τ) => (Fintype.equivFin (E →+* ℂ) s.1 : ℕ)) P := by
  first | exact @GlobalTheory.LieFilt.grCond_tanMat_of_inGr | exact GlobalTheory.LieFilt.grCond_tanMat_of_inGr | (intros; apply GlobalTheory.LieFilt.grCond_tanMat_of_inGr <;> assumption)
