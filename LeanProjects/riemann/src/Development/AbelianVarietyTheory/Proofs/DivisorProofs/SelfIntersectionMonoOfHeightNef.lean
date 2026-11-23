import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArithIntersectionNonnegOfSmallSectionDiffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtLinearMapEvalAlgebraMap
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem selfInter_mono : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (A B : HermLB p) (α β : ℝ), Le B A → (∀ x y : ℕ, HtNef ((A.pow x).tens (B.pow y)) D) → A.IsSelfInter α → B.IsSelfInter β → β ≤ α := by
  intro hC k _ Y _ p D hX A B α β hle hnef hα hβ
  obtain ⟨Φ, hΦ⟩ := ((hC.arExists k Y p D hX).2 (Fin 2) ![A, B]).1
  have hpos := GlobalTheory.T.mixedArithIntersection_nonneg_of_small_section_diff hC k Y p D hX A B Φ hΦ hle
  have hmono := GlobalTheory.monotone_form_along_segment D Φ fun x y => hpos x y (hnef x y)
  have hd := ((hC.arIso k Y p D hX).2 (Fin 2) _ Φ hΦ).1
  have h0 : Φ (MvPolynomial.X 0 ^ (D + 1)) = α := HermLB.IsSelfInter.unique hX (hd 0) hα
  have h1 : Φ (MvPolynomial.X 1 ^ (D + 1)) = β := HermLB.IsSelfInter.unique hX (hd 1) hβ
  rw [← h0, ← h1]
  exact hmono

end GlobalTheory.HSNef
