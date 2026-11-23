import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSubfieldOfForallRingEquivFixedOfIsAlgClosedAl
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_subfield_of_forall_ringEquiv_fixed_of_isAlgClosed' : ∀ (K : Type) [Field K] [IsAlgClosed K] (k₀ : Subfield K), IsAlgClosed k₀ → ∀ x : K, (∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → σ x = x) → x ∈ k₀ := by
  first | exact @GlobalTheory.mem_subfield_of_forall_ringEquiv_fixed_of_isAlgClosed | exact GlobalTheory.mem_subfield_of_forall_ringEquiv_fixed_of_isAlgClosed | (intros; apply GlobalTheory.mem_subfield_of_forall_ringEquiv_fixed_of_isAlgClosed <;> assumption)
