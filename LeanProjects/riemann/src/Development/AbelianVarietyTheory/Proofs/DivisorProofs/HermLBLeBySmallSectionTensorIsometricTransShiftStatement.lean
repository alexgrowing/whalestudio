import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLBLeBySmallSectionTensorIsometricTransShift
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermLBLeBySmallSection_tensor_isometric_trans_shift : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ A B M : HermLB p, (Le B A → Le (M.tens B) (M.tens A)) ∧ (B.Isometric A → Le B A) ∧ (Le B A → Le A M → Le B M) ∧ ∀ t : ℝ, Le B A → Le (B.shift (fun _ => t) fun _ => rfl) (A.shift (fun _ => t) fun _ => rfl) := by
  first | exact @GlobalTheory.HSNef.le_tens_isometric_trans_shift | exact GlobalTheory.HSNef.le_tens_isometric_trans_shift | (intros; apply GlobalTheory.HSNef.le_tens_isometric_trans_shift <;> assumption)
