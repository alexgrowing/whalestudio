import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsScfEmbeddingDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPRatio
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spherically_complete_embedding' : ∀ (p : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], p.Prime → (p : V) ∈ IsLocalRing.maximalIdeal V → Cardinal.mk V ≤ Cardinal.continuum → ∃ (C : SCF p) (φ : V →+* ↥(intO ↥C.S)), Function.Injective φ ∧ ∀ a b : V, ‖((φ a : ↥(intO ↥C.S)) : ↥C.S)‖ ≤ ‖((φ b : ↥(intO ↥C.S)) : ↥C.S)‖ → b ∣ a := by
  first | exact @GlobalTheory.ShFam.Pad.Pull.exists_scf_embedding_dvd | exact GlobalTheory.ShFam.Pad.Pull.exists_scf_embedding_dvd | (intros; apply GlobalTheory.ShFam.Pad.Pull.exists_scf_embedding_dvd <;> assumption)
