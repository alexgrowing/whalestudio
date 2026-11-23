import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationConstantOfPowerEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatSecUnitGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSchemeSpecialFibreNonemptyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowerSectionSpecialFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOfRegularAtCodimOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedSpecialFibreGlobalFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularSectionExtendsOverFibreStatement

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier

namespace GlobalTheory.PropZRow

theorem propZ : PropZ := by
  intro O _ _ _ ϖ hϖ Z f D hD sig hs
  obtain ⟨hI, hN, hP, hF, hC, hL, ht⟩ := hD
  haveI := hI
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace Z := (quasiCompact_iff_compactSpace f).mp inferInstance
  have hD : Hyp f D := ⟨hI, hN, hP, hF, hC, hL, ht⟩
  obtain ⟨τ, hτ, hU, hPow⟩ := GlobalTheory.T.exists_ratSec_unit_generic_fibre O ϖ hϖ Z f D hF hL sig hs
  obtain ⟨hg, hz⟩ := GlobalTheory.T.flat_scheme_special_fibre_nonempty O ϖ hϖ Z f hF (hC.toNonempty)
  obtain ⟨M, n, x₀, hM, hx₀, hreg, hunit⟩ := GlobalTheory.T.exists_power_section_special_fibre Z hN _ hg hz D τ hL hτ hU
  obtain ⟨gen, hgen, heq⟩ := GlobalTheory.T.regular_section_extends_over_fibre O ϖ hϖ Z f D hD hg (GlobalTheory.T.reduced_special_fibre_global_field O Z f hP hC) (GlobalTheory.T.regular_of_regular_at_codim_one Z hN) τ hτ hU M n x₀ hM hx₀ hreg hunit
  exact ⟨M, n, hM, ⟨gen, hgen, hPow M n gen heq⟩, GlobalTheory.T.valuation_constant_of_power_eq O ϖ hϖ Z f D hL sig hs M n gen hM hgen (hPow M n gen heq)⟩

end GlobalTheory.PropZRow
