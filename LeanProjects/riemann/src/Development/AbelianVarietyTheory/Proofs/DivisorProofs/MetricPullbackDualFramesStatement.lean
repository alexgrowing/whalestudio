import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricPullbackDualFrames
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
theorem _root_.GlobalTheory.T.metric_pullback_dual_frames : ∀ {k k' : Type} [CommRing k] [CommRing k'] (φ : k ≃+* k') {X Y Y' : Scheme.{0}} {F : Y'.Modules} {g : ℕ}
    {p' : Y' ⟶ Sp k'} (h : VMetric p' F g) (b : Y ⟶ Y') {p : Y ⟶ Sp k}
    (h₀ : VMetric p ((Scheme.Modules.pullback b).obj F) g), SameMet φ (h.pull b rfl) h₀ →
    ∀ (β : X ⟶ Y) {q : X ⟶ Sp k} (w : β ≫ p = q),
    ∃ (ℓ : ∀ c : VB.Chart F g, Fin g →
        Γ((Scheme.Modules.pullback β).obj (VB.dual ((Scheme.Modules.pullback b).obj F)), (β ≫ b) ⁻¹ᵁ c.U))
      (hℓ : ∀ c, VB.IsFrame (ℓ c)), DualCharts (β ≫ b) ℓ hℓ ∧
      ∀ (σ : k →+* ℂ) (σ' : k' →+* ℂ), σ' = σ.comp φ.symm.toRingHom → ∀ (z : CxPts q σ) (y : CxPts p' σ'),
        y.1 = z.1 ≫ β ≫ b → ∀ c : VB.Chart F g, y ∈ CxPts.ptsIn p' σ' c.U →
        ((h₀.dual.pull β w).met σ).G ⟨(β ≫ b) ⁻¹ᵁ c.U, ℓ c, hℓ c⟩ z = HermFrame.dualGram ((h.met σ').G c y) := by
  first | exact @GlobalTheory.LieFilt.exists_dualCharts_pull_dual_pull | exact GlobalTheory.LieFilt.exists_dualCharts_pull_dual_pull | (intros; apply GlobalTheory.LieFilt.exists_dualCharts_pull_dual_pull <;> assumption)
