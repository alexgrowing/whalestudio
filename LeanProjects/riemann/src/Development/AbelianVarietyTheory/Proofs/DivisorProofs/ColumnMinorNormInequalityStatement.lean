import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnMinorNormInequality
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.column_minor_norm_inequality : ∀ {K : Type} [Field K] (w : AbsoluteValue K ℝ), IsNonarchimedean w → ∀ {n g : ℕ} (H : Matrix (Fin n) (Fin g) K),
    (0 < colMinor w H Finset.univ ↔ Function.Injective H.mulVec) ∧
    (Function.Injective H.mulVec → (∀ S, 0 < colMinor w H S) ∧ ∀ (S : Finset (Fin g)) (i : Fin g), i ∉ S →
      (∀ u : Fin g → K, u i = 1 → (∀ l, l ∉ S → l ≠ i → u l = 0) →
        colMinor w H (insert i S) ≤ colMinor w H S * supN w (H.mulVec u)) ∧
      ∃ u : Fin g → K, u i = 1 ∧ (∀ l, l ∉ S → l ≠ i → u l = 0) ∧
        colMinor w H (insert i S) = colMinor w H S * supN w (H.mulVec u)) := by
  first | exact @GlobalTheory.ConstLat.MinorQuot.colMinor_pos_and_quotient | exact GlobalTheory.ConstLat.MinorQuot.colMinor_pos_and_quotient | (intros; apply GlobalTheory.ConstLat.MinorQuot.colMinor_pos_and_quotient <;> assumption)
