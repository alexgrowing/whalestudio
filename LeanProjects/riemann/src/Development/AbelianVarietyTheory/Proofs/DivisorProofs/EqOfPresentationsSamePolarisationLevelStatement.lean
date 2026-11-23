import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfPresentationsSamePolarisationLevel
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_presentations_same_polarisation_level : ∀ {o : Type} [CommRing o] {ζ : o} {h n : ℕ} (F' : SFam h n ζ), 3 ≤ n → IsUnit ζ → IsUnit (n : o) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (A : Over (Sp V)) [GrpObj A] [IsCommMonObj A] (t₁ t₂ : Sp V ⟶ F'.X) (a₁ a₂ : A.left ⟶ F'.univ.A.left) (aa₁ aa₂ : (G2 A).left ⟶ (G2 F'.univ.A).left), IsGrpPullback A F'.univ.A t₁ a₁ → IsGrpPullback A F'.univ.A t₂ a₂ → IsSquare a₁ aa₁ → IsSquare a₂ aa₂ → LBIso (F'.univ.P.pull aa₁) (F'.univ.P.pull aa₂) → t₁ ≫ F'.s = t₂ ≫ F'.s → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F], (∀ l, ∃ x : TF (R := V) F ⟶ A, x.left ≫ a₁ = (TF (R := V) F).hom ≫ t₁ ≫ (F'.univ.lev l).left ∧ x.left ≫ a₂ = (TF (R := V) F).hom ≫ t₂ ≫ (F'.univ.lev l).left) → t₁ = t₂ ∧ a₁ = a₂ := by
  first | exact @GlobalTheory.LowSame.eq_of_presentations | exact GlobalTheory.LowSame.eq_of_presentations | (intros; apply GlobalTheory.LowSame.eq_of_presentations <;> assumption)
