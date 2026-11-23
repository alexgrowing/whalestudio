import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.refinesPolarisedData_baseChange_symmetric : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : Data R) (R₁ : Type) [CommRing R₁] [IsDomain R₁] (R₂ : Type) [CommRing R₂] [IsDomain R₂] (σ : R₁ →+* R₂) (D₁ : DegPre R₁) (D₂ : DegPre R₂) (β : D₂.P.A.left ⟶ D₁.P.A.left) (v : LB.Iso D₂.P.L (D₁.P.L.pull β)) (xe : D₂.X ≃+ D₁.X) (gam : FractionRing R₁ →+* FractionRing R₂), (∀ r, gam (algebraMap R₁ _ r) = algebraMap R₂ _ (σ r)) → IsGrpPullback D₂.P.A D₁.P.A (spMap σ) β → v.IsGen → (∀ x, (D₂.c x).left ≫ β = spMap σ ≫ (D₁.c (xe x)).left) → GlobalTheory.PsiRing.RigCmp σ D₁ D₂ β v → GlobalTheory.PsiRing.PsiCmp D₁ D₂ β v xe (spMap gam) → ∀ (ρ : R →+* R₁) (e : D₁.X ≃+ Q.X), Function.Injective ρ → Half Q ρ D₁ e (fun _ _ => 1) → Half Q (σ.comp ρ) D₂ (xe.trans e) (fun _ _ => 1) := by
  first | exact @GlobalTheory.HalfBC.half_baseChange | exact GlobalTheory.HalfBC.half_baseChange | (intros; apply GlobalTheory.HalfBC.half_baseChange <;> assumption)
