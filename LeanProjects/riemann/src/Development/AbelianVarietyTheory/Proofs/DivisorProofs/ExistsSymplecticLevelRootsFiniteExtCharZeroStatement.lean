import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelRootsFiniteExtCharZero
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplecticLevel_roots_finite_ext_charZero : ∀ (R : Type) [CommRing R] (P : PolAV (Sp R)) (K : Type) [Field K] [CharZero K] (j : R →+* K) (n : ℕ), 0 < n → ∀ (ζ : Kˣ), IsPrimitiveRoot ζ n → ∀ (r : ℕ) (c : Fin r → (𝟙_ (Over (Sp R)) ⟶ P.A)), ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (lev : (Fin P.g ⊕ Fin P.g → ℤ) → (Over.mk (spMap ((algebraMap K L).comp j)) ⟶ P.A)) (d : Fin r → (Over.mk (spMap ((algebraMap K L).comp j)) ⟶ P.A)), (∀ x y, lev (x + y) = lev x * lev y) ∧ (∀ x, lev x ^ n = 1) ∧ (∀ x y, Out.WeilIs P.A P.L n (lev x) (lev y) (unitOn (Units.map (algebraMap K L).toMonoidHom ζ ^ omegaStd x y))) ∧ ∀ i, d i ^ n = toUnit _ ≫ c i := by
  first | exact @GlobalTheory.FieldLevel.exists_level_and_roots | exact GlobalTheory.FieldLevel.exists_level_and_roots | (intros; apply GlobalTheory.FieldLevel.exists_level_and_roots <;> assumption)
