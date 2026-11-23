import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsListedFiniteGaloisExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_constants_listed_finite_galois_extension : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (x : Sp Ω ⟶ S) (θ : SecAt G L x), Odd m → N = m ^ (4 * g) → PolFib G L g x → ∃ (Ω' : Type) (_ : Field Ω') (_ : Algebra Ω Ω') (pt : Fin N → (Over.mk (spMap (algebraMap Ω Ω') ≫ x) ⟶ G)) (c : Fin N → Ω'), FiniteDimensional Ω Ω' ∧ IsGalois Ω Ω' ∧ Module.finrank Ω Ω' ∣ N.factorial ∧ ThList G L ρ m (spMap (algebraMap Ω Ω') ≫ x) (SecAt.pull G L θ (algebraMap Ω Ω')) pt c ∧ ∀ τ : Ω' ≃ₐ[Ω] Ω', ∃ σ : Equiv.Perm (Fin N), ∀ a, τ (c a) = c (σ a) := by
  first | exact @GlobalTheory.UMin.GalTh.thList_galois | exact GlobalTheory.UMin.GalTh.thList_galois | (intros; apply GlobalTheory.UMin.GalTh.thList_galois <;> assumption)
