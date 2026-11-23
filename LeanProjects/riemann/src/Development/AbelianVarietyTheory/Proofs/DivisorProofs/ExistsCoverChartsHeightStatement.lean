import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverChartsHeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastNeZeroG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatMatTransposeMulGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthLetters
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat
open scoped Classical
open GlobalTheory.EqHalf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cover_charts_height : Hypotheses2 → HypothesesH → GlobalTheory.Published.RegularAlteration → GlobalTheory.Published.ScholzeWeinsteinB → GlobalTheory.Published.PrismaticDieudonnePerfd →
    ∀ (D : D7) (O : Setup D), O.Core → ∀ (T : Finset ℕ) (R : ℝ), 2 ≤ R → ∀ p : ℕ, p.Prime → p ∈ T → ∀ (c : O.s.Comp)
    (b : Module.Basis (Fin (D.R.f * O.N + D.R.f * O.N)) ℤ O.S.Dw.La) (n : ℕ), 3 ≤ n →
    ∃ (V : Cover (O.Φ.C c).Y) (W : (O.Φ.C c).Y.X.Opens) (Ch : Type) (U : Ch → V.X.Opens)
      (H : Ch → Matrix (Fin (D.R.f * O.N + D.R.f * O.N)) (Fin (D.R.f * O.N)) V.G.functionField)
      (T' : (O.Φ.C c).Y.X → Matrix (Fin (D.R.f * O.N)) (Fin (D.R.f * O.N)) (O.Φ.C c).Y.Fn),
      genericPoint (O.Φ.C c).Y.X ∈ W ∧ (∀ x : V.X, ¬ IsUnit (p : V.X.presheaf.stalk x) → ∃ a, x ∈ U a) ∧
      (∀ y, (T' y).BlockTriangular id ∧ ∀ i, T' y i i = (dgOf O c y i : (O.Φ.C c).Y.Fn)) ∧
      LineBase V (dgOf O c) (wholeA O c T R) p ∧ LineBase V (dgOf O c) (eigA O c T R) p ∧
      (∀ a, ChartReg V (U a) (H a) T') ∧
      AtTest V W p fun v e y z yt => ∀ hp : (resP v).Prime,
        PtData O c b n hp e y (fun a => ⊤ ≤ yt ⁻¹ᵁ U a) (fun a => GlobalTheory.WholeFlag.valMat V (H a) (T' (below y.1)) z) := by
  first | exact @GlobalTheory.EqHalf.Frame.exists_frame | exact GlobalTheory.EqHalf.Frame.exists_frame | (intros; apply GlobalTheory.EqHalf.Frame.exists_frame <;> assumption)
