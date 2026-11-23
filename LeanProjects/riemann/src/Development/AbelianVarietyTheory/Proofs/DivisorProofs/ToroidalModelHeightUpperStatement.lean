import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalModelHeightUpper
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
theorem _root_.GlobalTheory.T.toroidal_model_height_upper : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F)
    {X W : Scheme.{0}} {q : X ⟶ Sp (𝓞 F)} {jB : W ⟶ X} {πB : W ⟶ gen Z} (ρ : X ⟶ Z.X), IsPullback jB (πB ≫ genStr Z ≫ spMap e.toRingHom) q (spMap (algebraMap (𝓞 F) F)) → jB ≫ ρ = πB ≫ genι Z →
    ∀ {M M' : X.Modules} {r g : ℕ} (τ : E →+* ℂ) (t : FrAssign Z M r jB) (t' : FrAssign Z M' r jB) (u : M ⟶ M'),
    IsLieFrames Z e jB πB M r τ false t → IsLieFrames Z e jB πB M' r τ false t' → Matches Z jB πB u t t' →
    ∀ (ch : VB.Chart (omega Z.t.G) g) (V : X.Opens), V ≤ ρ ⁻¹ᵁ ch.U → IsAffineOpen V →
    ∀ (f : Fin r → Γ(M, V)) (hf : VB.IsFrame f) (f' : Fin r → Γ(M', V)) (hf' : VB.IsFrame f')
      (A A' : Matrix (Fin g) (Fin r) Γ(W, jB ⁻¹ᵁ V)), GenCoord Z jB πB t ch hf A → GenCoord Z jB πB t' ch hf' A' →
    ∀ b i, A b i = ∑ j, A' b j * jB.app V ((hf'.basis le_rfl).repr (u.app V (f i)) j) := by
  first | exact @GlobalTheory.LieFilt.genCoord_rel | exact GlobalTheory.LieFilt.genCoord_rel | (intros; apply GlobalTheory.LieFilt.genCoord_rel <;> assumption)
