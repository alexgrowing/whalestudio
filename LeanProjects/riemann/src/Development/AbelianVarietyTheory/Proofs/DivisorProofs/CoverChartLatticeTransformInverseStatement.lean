import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverChartLatticeTransformInverse
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_chart_lattice_transform_inverse : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {C : CxSt F} {g : ℕ} (A A' : Fin g → Adl C Y) (p n k k' : ℕ),
    p.Prime → n ≠ 0 → ∀ (V : Cover Y) (W : Y.X.Opens) {ι : Type} (U0 : ι → V.X.Opens)
    (H0 : ι → Matrix (Fin (g + g)) (Fin g) V.G.functionField) (d : Y.X → Fin g → Y.Fnˣ)
    (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn) (J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ)
    (P Q : Matrix (Fin (g + g)) (Fin (g + g)) F) (κ : F →+* V.X.functionField),
    (∀ (z : Sp (AlgebraicClosure F) ⟶ V.G) (f : F), valAt (z ≫ V.j) (κ f) = valAt z (V.φ (algebraMap F Y.Fn f))) →
    IsUnit J.det → SecondLat J p n P Q → IsoAgree V W U0 H0 T J p k' → LineBase V d A p → LineBase V d A' p →
    ∀ (a b : ι) (Ua Ub : V.X.Opens) (Um' Um : Matrix (Fin (g + g)) (Fin g) V.X.functionField)
      (Lf' Lf : Matrix (Fin g) (Fin (g + g)) V.X.functionField) (c' c : Fin g → V.G.functionFieldˣ),
    Ua ≤ U0 a → Ub ≤ U0 b → ChartReg V (U0 a) (H0 a) T →
    FrameOn V W Ua (P.map (V.φ.comp (algebraMap F Y.Fn)) * H0 a) d T A' p Um' Lf' c' →
    FrameOn V W Ub (H0 b) d T A p Um Lf c →
    (∀ x ∈ Ua, ¬ IsUnit (p : V.X.presheaf.stalk x) →
      UnitAt x (compl Um' Lf' (P.map κ * (J.map (Int.castRingHom V.X.functionField))⁻¹ * (P.map κ).transpose)).det) →
    ∀ (v : HeightOneSpectrum (𝓞 F)), resP v = p → ∀ (e : Ext v) (y : AlgPt Y), below y.1 ∈ W →
      ∀ (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j →
      ⊤ ≤ yt ⁻¹ᵁ Ua → ⊤ ≤ yt ⁻¹ᵁ Ub →
      e.w (p : AlgebraicClosure F) ^ k' / e.w (n : AlgebraicClosure F) ^ 3 ≤ e.w (p : AlgebraicClosure F) ^ k →
      ∀ i : Fin (g + g),
        (∀ j, j < i → e.w (valAt (z ≫ V.j) (((compl Um' Lf' (P.map κ * (J.map (Int.castRingHom V.X.functionField))⁻¹ *
          (P.map κ).transpose))⁻¹ * P.map κ * compl Um Lf (J.map (Int.castRingHom V.X.functionField))⁻¹) i j)) ≤
            e.w (p : AlgebraicClosure F) ^ k) ∧
        e.w (valAt (z ≫ V.j) (((compl Um' Lf' (P.map κ * (J.map (Int.castRingHom V.X.functionField))⁻¹ *
          (P.map κ).transpose))⁻¹ * P.map κ * compl Um Lf (J.map (Int.castRingHom V.X.functionField))⁻¹) i i) -
          valAt z ((Sum.elim c' (fun l => (c' l.rev)⁻¹) (finSumFinEquiv.symm i) /
            Sum.elim c (fun l => (c l.rev)⁻¹) (finSumFinEquiv.symm i) : V.G.functionFieldˣ) : V.G.functionField)) ≤
          e.w (p : AlgebraicClosure F) ^ k := by
  first | exact @GlobalTheory.TestChange.change_tri | exact GlobalTheory.TestChange.change_tri | (intros; apply GlobalTheory.TestChange.change_tri <;> assumption)
