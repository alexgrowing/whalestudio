import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMinimalCompactificationExtensionOfCover
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_minimalCompactification_extension_of_cover : ∀ (o : Type) [CommRing o] (g : ℕ) (Z S' : Scheme.{0}) (z : Z ⟶ Sp o) (π : S' ⟶ Z) [IsProper z] [IsProper π] (OZ : LB Z), OZ.IsLB → GlobalTheory.IsAmpleLB OZ → ∀ (G : Over S') [GrpObj G] [IsCommMonObj G] (N : ℕ), IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → LBIso (OZ.pull π) (lbPow (hodge G g) N) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (b : o →+* R) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (y : Sp (FractionRing R) ⟶ S') (α : pullback G₁.hom (jK R) ⟶ G.left), IsGrpPullback ((Over.pullback (jK R)).obj G₁) G y α → y ≫ π ≫ z = jK R ≫ spMap b → ∃ a : Sp R ⟶ Z, jK R ≫ a = y ≫ π := by
  first | exact @GlobalTheory.TozCore.exists_extension_of_cover_hodge | exact GlobalTheory.TozCore.exists_extension_of_cover_hodge | (intros; apply GlobalTheory.TozCore.exists_extension_of_cover_hodge <;> assumption)
