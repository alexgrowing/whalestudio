import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualEigenHodgeMetric
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
theorem _root_.GlobalTheory.T.dual_eigen_hodge_metric : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (G : ∀ σ', EigMet Z σ') {g : ℕ} (h : VMetric Z.s (omega Z.t.G) g), IsDualEig G h →
    ∀ (σ' : c.F →+* ℂ) (yc : CxPts (genStr Z) σ') (y : CxPts Z.s (σ'.comp β)), y.1 = yc.1 ≫ genι Z →
    ∀ (ch : VB.Chart (omega Z.t.G) g), y ∈ CxPts.ptsIn Z.s (σ'.comp β) ch.U →
    ∀ (u : EigFrame Z σ' (yc.1 ≫ genι Z)) (P : Matrix (Fin g) (Σ τ, Fin (Dw.mult τ)) ℂ),
      IsTanMat Z (yc.1 ≫ genι Z) ch (fun s : Σ τ, Fin (Dw.mult τ) => u.v s.1 s.2) P → Function.Bijective P.mulVec →
      (∀ τ i j, HermFrame.form (HermFrame.dualGram ((h.met _).G ch y)) (fun b => P b ⟨τ, i⟩) (fun b => P b ⟨τ, j⟩) =
        (G σ').gram yc u τ j i) ∧
      ∀ s s' : Σ τ, Fin (Dw.mult τ), s.1 ≠ s'.1 →
        HermFrame.form (HermFrame.dualGram ((h.met _).G ch y)) (fun b => P b s) (fun b => P b s') = 0 := by
  first | exact @GlobalTheory.DualEigFrame.dualGram_tanMat | exact GlobalTheory.DualEigFrame.dualGram_tanMat | (intros; apply GlobalTheory.DualEigFrame.dualGram_tanMat <;> assumption)
