import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartRegularTriangularBase
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_regular_triangular_base : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {C : CxSt F} {g : ℕ} (A : Fin g → Adl C Y) (p : ℕ), p.Prime →
    ∀ (V : Cover Y) (W : Y.X.Opens), genericPoint Y.X ∈ W → ∀ (U : V.X.Opens)
    (H : Matrix (Fin (g + g)) (Fin g) V.G.functionField) (d : Y.X → Fin g → Y.Fnˣ) (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn),
    (∀ y, (T y).BlockTriangular id ∧ ∀ i, T y i i = (d y i : Y.Fn)) → LineBase V d A p → ChartReg V U H T →
    MinorNorm V W U H d T A p → ∀ x ∈ U, ¬ IsUnit (p : V.X.presheaf.stalk x) →
    ∃ (U' : V.X.Opens) (Um : Matrix (Fin (g + g)) (Fin g) V.X.functionField)
      (Lf : Matrix (Fin g) (Fin (g + g)) V.X.functionField) (c : Fin g → V.G.functionFieldˣ),
      U' ≤ U ∧ x ∈ U' ∧ FrameOn V W U' H d T A p Um Lf c := by
  first | exact @GlobalTheory.ConstLat.CramerFrame.frameOn_near | exact GlobalTheory.ConstLat.CramerFrame.frameOn_near | (intros; apply GlobalTheory.ConstLat.CramerFrame.frameOn_near <;> assumption)
