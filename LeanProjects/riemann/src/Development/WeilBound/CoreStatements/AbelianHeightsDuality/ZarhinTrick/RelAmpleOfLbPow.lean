import Mathlib
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibAmpleD
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]

theorem relAmple_of_lbPow {G : Over (Sp Ω)} [GrpObj G] (hG : IsAbelianScheme G) {M : LB G.left} (hM : M.IsLB)
    (n : ℕ) (hn : 1 ≤ n) (h : Out.RelAmple G (lbPow M n)) : Out.RelAmple G M := by
  haveI : IsProper G.hom := hG.proper
  have hP : (lbPow M n).IsLB := GlobalTheory.isLB_lbPow hM n
  exact GlobalTheory.PosDefAmple.relAmple_of_nsmul hM hP hn (cls_lbPow hM n hP).symm h

end PositivityTheory.PrwZar
