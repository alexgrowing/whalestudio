import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverChartLeftInverseRegular
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_chart_left_inverse_regular : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {C : CxSt F} {g : ℕ} (A : Fin g → Adl C Y) (p : ℕ), p.Prime →
    ∀ (V : Cover Y) (W : Y.X.Opens), genericPoint Y.X ∈ W → ∀ (U : V.X.Opens)
    (H : Matrix (Fin (g + g)) (Fin g) V.G.functionField) (d : Y.X → Fin g → Y.Fnˣ) (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn)
    (Um : Matrix (Fin (g + g)) (Fin g) V.X.functionField) (Lf : Matrix (Fin g) (Fin (g + g)) V.X.functionField)
    (c : Fin g → V.G.functionFieldˣ) (Jx Jix : Matrix (Fin (g + g)) (Fin (g + g)) V.X.functionField),
    FrameOn V W U H d T A p Um Lf c → Jx * Jix = 1 →
    (∀ x ∈ U, ¬ IsUnit (p : V.X.presheaf.stalk x) → ∀ i j, RegAt x (Jx i j) ∧ RegAt x (Jix i j)) →
    AtTest V W p (fun _ e _ z yt => ⊤ ≤ yt ⁻¹ᵁ U → ∀ i j,
      e.w (valAt (z ≫ V.j) ((Um.transpose * Jx * Um) i j)) < 1) →
    ∀ x ∈ U, ¬ IsUnit (p : V.X.presheaf.stalk x) → UnitAt x (compl Um Lf Jix).det := by
  first | exact @GlobalTheory.ConstLat.unitAt_det_compl_of_atTest | exact GlobalTheory.ConstLat.unitAt_det_compl_of_atTest | (intros; apply GlobalTheory.ConstLat.unitAt_det_compl_of_atTest <;> assumption)
