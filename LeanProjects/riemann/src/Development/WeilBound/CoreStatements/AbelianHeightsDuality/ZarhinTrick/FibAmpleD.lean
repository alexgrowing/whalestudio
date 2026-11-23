import Mathlib
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.IsLBZb

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}}

def fourfoldProductLift {X G : Over S} (c : Fin 4 → (X ⟶ G)) : X ⟶ G4 G := lift (c 0) (lift (c 1) (lift (c 2) (c 3)))

variable {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

def eMap (mu : B ⟶ A) (α : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ) : G4 (A ⊗ B) ⟶ G4 (A ⊗ B) :=
  fourfoldProductLift fun i => lift ((prj _ i ≫ fst A B) * (∏ j, (prj _ j ≫ snd A B ≫ mu) ^ (α i j))⁻¹)
    ((prj _ i ≫ snd A B) ^ (2 * m))

def eMap' (mu : B ⟶ A) (α : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ) : G4 (A ⊗ B) ⟶ G4 (A ⊗ B) :=
  fourfoldProductLift fun i => lift ((prj _ i ≫ fst A B) ^ (2 * m) * ∏ j, (prj _ j ≫ snd A B ≫ mu) ^ (α i j))
    (prj _ i ≫ snd A B)

def lPart (mu : B ⟶ A) {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S) (L : LB ((Over.pullback s).obj A).left) :
    LB ((Over.pullback s).obj (G4 (A ⊗ B))).left :=
  LB.LinComb L (phiL mu s) fun _ => 1

end PositivityTheory.PrwZar
