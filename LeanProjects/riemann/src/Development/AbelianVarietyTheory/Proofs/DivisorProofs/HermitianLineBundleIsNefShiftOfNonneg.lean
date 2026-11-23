import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionLowerHeight
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

noncomputable section

namespace GlobalTheory.NefShift

theorem isNef_shift_nonneg : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (M : HermLB p) (t : ℝ), 0 ≤ t → M.IsNef D →
      (M.shift (fun _ => t) fun _ => rfl).IsNef D := by
  intro k _ X _ p D hX M t ht hM
  refine ⟨hM.semiPos.shift _ _, fun Z i _ _ κ _ _ _ hd => hM.vertical Z i κ hd, ?_⟩
  intro Z i _ _ _ hc hd
  obtain ⟨r, hr, h0⟩ := hM.horizontal Z i hc hd
  refine ⟨r, hr, ?_⟩
  rw [GlobalTheory.HtSelfInter.curveDeg_shift hX M t i hc hd hr]
  have : (0 : ℝ) ≤ t * Nat.card (X.residueField (i (genericPoint Z)) →+* ℂ) := by positivity
  linarith

end GlobalTheory.NefShift
