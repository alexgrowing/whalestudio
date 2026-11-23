import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverChartMinorDecomposition
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_chart_minor_decomposition : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {C : CxSt F} {g : ℕ} (A : Fin g → Adl C Y) (p k : ℕ), p.Prime →
    ∀ (V : Cover Y) (W : Y.X.Opens) {ι : Type} (U0 : ι → V.X.Opens)
    (H0 : ι → Matrix (Fin (g + g)) (Fin g) V.G.functionField) (d : Y.X → Fin g → Y.Fnˣ)
    (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn) (J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ) (a : ι) (U : V.X.Opens)
    (Um : Matrix (Fin (g + g)) (Fin g) V.X.functionField) (Lf : Matrix (Fin g) (Fin (g + g)) V.X.functionField)
    (c : Fin g → V.G.functionFieldˣ), U ≤ U0 a → FrameOn V W U (H0 a) d T A p Um Lf c → IsoAgree V W U0 H0 T J p k →
    AtTest V W p (fun _ e _ z yt => ⊤ ≤ yt ⁻¹ᵁ U → ∀ i j,
      e.w (valAt (z ≫ V.j) ((Um.transpose * J.map (Int.castRingHom V.X.functionField) * Um) i j)) ≤
        e.w (p : AlgebraicClosure F) ^ k) := by
  first | exact @GlobalTheory.ConstLat.form_frame_small | exact GlobalTheory.ConstLat.form_frame_small | (intros; apply GlobalTheory.ConstLat.form_frame_small <;> assumption)
