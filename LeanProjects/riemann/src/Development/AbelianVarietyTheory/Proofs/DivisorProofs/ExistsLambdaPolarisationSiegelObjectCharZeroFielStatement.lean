import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLambdaPolarisationSiegelObjectCharZeroFiel
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lambdaPolarisation_siegelObject_charZeroField : ∀ (h k : ℕ) (o : Type) [CommRing o] (ζ : o) (S : Scheme.{0}) (s : S ⟶ Sp o) (c : SiegPre h k ζ s), c.Principal →
    ∀ (K : Type) [Field K] [CharZero K] (f : Sp K ⟶ S), ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra K R₁),
      Module.Finite K R₁ ∧ Nontrivial R₁ ∧ ∃ (P : PolAV (Sp R₁)) (α : P.A.left ⟶ c.A.left) (α₂ : (G2 P.A).left ⟶ (G2 c.A).left),
        IsGrpPullback P.A c.A (spMap (algebraMap K R₁) ≫ f) α ∧ IsSquare α α₂ ∧ LBIso (abelian₂ P.A P.L) (c.P.pull α₂) := by
  first | exact @GlobalTheory.SiegelSqrtField.exists_sqrt_field | exact GlobalTheory.SiegelSqrtField.exists_sqrt_field | (intros; apply GlobalTheory.SiegelSqrtField.exists_sqrt_field <;> assumption)
