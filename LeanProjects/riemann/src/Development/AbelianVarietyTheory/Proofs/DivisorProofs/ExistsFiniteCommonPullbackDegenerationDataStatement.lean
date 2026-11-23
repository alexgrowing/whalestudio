import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCommonPullbackDegenerationData
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_common_pullback_degenerationData : ∀ (K L : Type) [Field K] [CharZero K] [Field L] (β : K →+* L) (E₁ E₂ : DegPre K) (E' : DegPre L), IsPullDeg β E₁ E' → IsPullDeg β E₂ E' → ∃ (K' : Type) (_ : Field K') (io : K →+* K') (E₃ : DegPre K'), io.Finite ∧ Nonempty (IsPullDeg io E₁ E₃) ∧ Nonempty (IsPullDeg io E₂ E₃) := by
  first | exact @GlobalTheory.FieldDesc.exists_finite_common_pull | exact GlobalTheory.FieldDesc.exists_finite_common_pull | (intros; apply GlobalTheory.FieldDesc.exists_finite_common_pull <;> assumption)
