import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimClosedLeOfTranscendenceBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.BdDim GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dim_closed_le_of_transcendence_bound : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℤ) (S : Set X) (n : ℕ), LocallyOfFiniteType p → IsClosed S → (∀ y ∈ S, TrLe (X.residueField y) n) → topologicalKrullDim S ≤ (n + 1 : ℕ) := by
  first | exact @GlobalTheory.BdDim.topologicalKrullDim_le_of_trLe | exact GlobalTheory.BdDim.topologicalKrullDim_le_of_trLe | (intros; apply GlobalTheory.BdDim.topologicalKrullDim_le_of_trLe <;> assumption)
