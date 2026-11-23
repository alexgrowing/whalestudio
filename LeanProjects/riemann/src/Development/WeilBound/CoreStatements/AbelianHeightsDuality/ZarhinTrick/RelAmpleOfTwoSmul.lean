import Mathlib
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibAmpleD
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.RelAmpleOfTwoSmulAlt

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]

theorem relAmple_of_two_smul {G : Over (Sp Ω)} [GrpObj G] (hG : IsAbelianScheme G) {M N : LB G.left}
    (hM : M.IsLB) (hN : N.IsLB) (d : ℕ) (hd : 1 ≤ d) (e : d • cls M hM = d • cls N hN) (h : Out.RelAmple G N) :
    Out.RelAmple G M :=
  Z2.relAmple_of_two_smul hG hM hN d hd e h

end PositivityTheory.PrwZar
