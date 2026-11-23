import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteNormalAdjoinAlgebraic
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationPullbackCompatibleIso
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integrally_closed_extension_of_adjoin : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (s : AlgebraicClosure (FractionRing R)), ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (h : R →+* R₂) (h' : FractionRing R →+* FractionRing R₂) (e : FractionRing R₂ →+* AlgebraicClosure (FractionRing R)), Function.Injective h ∧ h.Finite ∧ IsIntegrallyClosed R₂ ∧ (∀ r, h' (algebraMap R _ r) = algebraMap R₂ _ (h r)) ∧ e.comp h' = algebraMap _ _ ∧ (∃ s₂, e s₂ = s) ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] (g : FractionRing R₂ →+* F), ∃ g' : AlgebraicClosure (FractionRing R) →+* F, g'.comp e = g := by
  first | exact @GlobalTheory.exists_finite_normal_adjoin_algebraic | exact GlobalTheory.exists_finite_normal_adjoin_algebraic | (intros; apply GlobalTheory.exists_finite_normal_adjoin_algebraic <;> assumption)
