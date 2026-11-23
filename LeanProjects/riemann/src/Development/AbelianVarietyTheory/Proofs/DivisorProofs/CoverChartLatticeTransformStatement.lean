import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverChartLatticeTransform
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_chart_lattice_transform : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {C : CxSt F} {g : ℕ} (A' : Fin g → Adl C Y) (p n k : ℕ), p.Prime →
    n ≠ 0 → ∀ (V : Cover Y) (W : Y.X.Opens) {ι : Type} (U0 : ι → V.X.Opens)
    (H0 : ι → Matrix (Fin (g + g)) (Fin g) V.G.functionField) (d : Y.X → Fin g → Y.Fnˣ)
    (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn) (J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ)
    (P Q : Matrix (Fin (g + g)) (Fin (g + g)) F) (κ : F →+* V.X.functionField),
    (∀ (z : Sp (AlgebraicClosure F) ⟶ V.G) (f : F), valAt (z ≫ V.j) (κ f) = valAt z (V.φ (algebraMap F Y.Fn f))) →
    SecondLat J p n P Q → ∀ (a : ι) (U : V.X.Opens)
    (Um : Matrix (Fin (g + g)) (Fin g) V.X.functionField) (Lf : Matrix (Fin g) (Fin (g + g)) V.X.functionField)
    (c : Fin g → V.G.functionFieldˣ), U ≤ U0 a → ChartReg V (U0 a) (H0 a) T →
    FrameOn V W U (P.map (V.φ.comp (algebraMap F Y.Fn)) * H0 a) d T A' p Um Lf c → IsoAgree V W U0 H0 T J p k →
    AtTest V W p (fun _ e _ z yt => ⊤ ≤ yt ⁻¹ᵁ U → ∀ i j,
      e.w (valAt (z ≫ V.j) ((Um.transpose * ((Q.map κ).transpose * J.map (Int.castRingHom V.X.functionField) * Q.map κ) *
        Um) i j)) ≤ e.w (p : AlgebraicClosure F) ^ k / e.w (n : AlgebraicClosure F) ^ 2) := by
  first | exact @GlobalTheory.ConstLat.IsoSecond.form_frame_second_le | exact GlobalTheory.ConstLat.IsoSecond.form_frame_second_le | (intros; apply GlobalTheory.ConstLat.IsoSecond.form_frame_second_le <;> assumption)
