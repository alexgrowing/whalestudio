import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FnEquivApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartRegularMinorNormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorBoundsOnChartOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularChartMinorComparisonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftInverseRegularOfRegularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularChartMinorBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularChartMinorEqualityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularChartMinorLimitStatement
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat GlobalTheory.WholeFlag.Glue GlobalTheory.ConstLat.CramerFrame
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory.ConstLat.CramerFrame

theorem frameOn_near : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {C : CxSt F} {g : ℕ} (A : Fin g → Adl C Y) (p : ℕ), p.Prime →
    ∀ (V : Cover Y) (W : Y.X.Opens), genericPoint Y.X ∈ W → ∀ (U : V.X.Opens)
    (H : Matrix (Fin (g + g)) (Fin g) V.G.functionField) (d : Y.X → Fin g → Y.Fnˣ) (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn),
    (∀ y, (T y).BlockTriangular id ∧ ∀ i, T y i i = (d y i : Y.Fn)) → LineBase V d A p → ChartReg V U H T →
    MinorNorm V W U H d T A p → ∀ x ∈ U, ¬ IsUnit (p : V.X.presheaf.stalk x) →
    ∃ (U' : V.X.Opens) (Um : Matrix (Fin (g + g)) (Fin g) V.X.functionField)
      (Lf : Matrix (Fin g) (Fin (g + g)) V.X.functionField) (c : Fin g → V.G.functionFieldˣ),
      U' ≤ U ∧ x ∈ U' ∧ FrameOn V W U' H d T A p Um Lf c := by
  intro F _ _ Y C g A p hp V W hW U H d T hT hLB hCR hMN x hxU hxp
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · refine ⟨U, 0, 0, fun i => i.elim0, le_rfl, hxU, Subsingleton.elim _ _, fun _ _ _ k => k.elim0,
      fun i => i.elim0, fun v hv e y hy z yt h1 h2 h3 => ⟨fun i => i.elim0, 0, fun i => i.elim0, fun i => i.elim0,
      Subsingleton.elim _ _⟩⟩
  obtain ⟨U₁, m, f, hm, hU₁, hx₁, hf, hft⟩ := GlobalTheory.T.chart_regular_minor_norms A p hp V W hW U H d T hT hLB hCR hMN x hxU hxp
  obtain ⟨U', σ, hU', hx', hnz, ha, hb⟩ := GlobalTheory.T.minor_bounds_on_chart_open V W p hp hW hg H d T hT U₁ m f hm hf hft x hx₁ hxp
  have hle : U' ≤ U := hU'.trans hU₁
  have hCR' : ChartReg V U' H T := fun z hz => hCR z (hle hz)
  have hMN' : MinorNorm V W U' H d T A p := fun v hv e y hy z yt h1 h2 h3 =>
    hMN v hv e y hy z yt h1 h2 (h3.trans (fun q hq => hle hq))
  obtain ⟨hdet, hreg⟩ := GlobalTheory.T.triangular_chart_minor_comparison V W p hp hW U' H d T σ hT hCR' hnz ha hb
  obtain ⟨hinv, hlreg⟩ := GlobalTheory.T.left_inverse_regular_of_regular (frameUm V H σ) (σ g) hdet
  refine ⟨U', frameUm V H σ, frameLf V H σ, frameC H σ, hle, hx', hinv, fun y hy hyp k l =>
    ⟨hreg y hy hyp k l, hlreg y (fun r k => hreg y hy hyp r k) l k⟩,
    GlobalTheory.T.triangular_chart_minor_bound V W p hp hW A U' H d T σ hT hCR' hnz ha hb hLB.1, fun v hv e y hy z yt h1 h2 h3 =>
    ⟨GlobalTheory.T.triangular_chart_minor_equality V W p hp hW A U' H d T σ hT hCR' hnz ha hb hLB.1 hMN' v hv e y hy z yt h1 h2 h3,
     GlobalTheory.T.triangular_chart_minor_limit V W p hp hW U' H d T σ hT hCR' hnz ha hb v hv e y hy z yt h1 h2 h3⟩⟩

end GlobalTheory.ConstLat.CramerFrame
