import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalModelHeightSum
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
theorem _root_.GlobalTheory.T.toroidal_model_height_sum : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F)
    {X W : Scheme.{0}} {q : X ⟶ Sp (𝓞 F)} {jB : W ⟶ X} {πB : W ⟶ gen Z} (ρ : X ⟶ Z.X), IsPullback jB (πB ≫ genStr Z ≫ spMap e.toRingHom) q (spMap (algebraMap (𝓞 F) F)) → jB ≫ ρ = πB ≫ genι Z →
    ∀ {L : X.Modules} {g : ℕ} {ℓ : ∀ ch : VB.Chart (omega Z.t.G) g, Fin g → Γ(L, ρ ⁻¹ᵁ ch.U)} (hℓ : ∀ ch, VB.IsFrame (ℓ ch)), IsVB (omega Z.t.G) g →
    ∀ (G : ∀ σ', EigMet Z σ') (hL : VMetric q L g), MetDict Z e ρ hℓ G hL →
    ∀ {M : (E →+* ℂ) → X.Modules} (t : ∀ τ, FrAssign Z (M τ) (Dw.mult τ) jB) (h : ∀ τ, VMetric q (M τ) (Dw.mult τ))
      (T : ∀ τ, M τ ⟶ L), (∀ τ, IsLieFrames Z e jB πB (M τ) _ τ false (t τ)) →
      (∀ τ, IsLieMet Z e q jB πB (M τ) _ τ false rfl G (h τ) (t τ)) → (∀ τ, TanCoord Z jB πB (t τ) ρ hℓ (T τ)) →
    OrthEmb hL h T := by
  first | exact @GlobalTheory.LieFilt.orthEmb_of_tanCoord | exact GlobalTheory.LieFilt.orthEmb_of_tanCoord | (intros; apply GlobalTheory.LieFilt.orthEmb_of_tanCoord <;> assumption)
