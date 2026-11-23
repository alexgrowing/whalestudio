import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiDefs
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.KerMemKL
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.PfiFRangeFiniteClosed
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.SurjOfFiniteDimS
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibLamC
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsogenousRetractPolarisedFiniteExt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteClosedSubschemeRepresentsKernelAmpleStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FlatAndSurjectiveOfSurjectivePointsStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)

namespace PositivityTheory.PrwZar.Z2

open GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Ar.GR

theorem polFibreIsogAny : PositivityTheory.PrwZar.PolFibreIsogAny := by
  intro C _ _ v R _ _ hv A B _ _ P l g hA hB hgA hgB hD hD' hp Ω _ _ s
  have : IsMonHom l := hp.1
  obtain ⟨L, hL, ha, e⟩ := hp.2 Ω s
  have hA' := GlobalTheory.isAbelianScheme_pullback_obj s A hA
  have hB' := GlobalTheory.isAbelianScheme_pullback_obj s B hB
  have hgA' := GlobalTheory.FiniteData.relDim_pullback s A hgA
  have hgB' := GlobalTheory.FiniteData.relDim_pullback s B hgB
  haveI := hA'.comm
  obtain ⟨H, j, -, hH, hK⟩ := GlobalTheory.T.exists_finite_closed_subscheme_represents_kernel_ample GlobalTheory.globalFns_holds Ω ((Over.pullback s).obj A) hA' L hL ha
  have hfin : IsFinite ((Over.pullback s).map l).left :=
    isFinite_of_ker hA' hB' _ H j hH fun T x hx => (hK T x).1 (ker_memKL hD l s L hL e x hx)
  obtain ⟨hfl, hsu⟩ := flat_surj_of_finite hA' hB' g hgA' hgB' _ hfin
  exact ⟨hfin, hfl, hsu⟩

end PositivityTheory.PrwZar.Z2
