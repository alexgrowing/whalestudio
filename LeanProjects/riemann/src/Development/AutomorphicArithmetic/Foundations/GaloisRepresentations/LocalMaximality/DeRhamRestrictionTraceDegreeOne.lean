import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceCechCochainFractionEqSumFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTopDegreeCoefficientFormAndEqOnTopFormsStatement
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

theorem UpperTheory.Gal.productCup_of_system.deRham_restriction_trace_degree_one :
    ResidueOfTraceIsFiberSum := by
  intro F L _ _ _ _ _ _ d x hc hred ρ hρ h
  obtain ⟨⟨τ, hτ⟩, -⟩ := GlobalTheory.T.exists_topDegreeCoefficientForm_and_eq_on_top_forms ℂ F L d (xv x) hc
  have hloc : locCoch ℂ L (xv x) (h : L) Finset.univ = (h : L) • vol0 ℂ L (xv x) := if_pos rfl
  have h1 : trF ℂ τ ρ (locCoch ℂ L (xv x) (h : L) Finset.univ) = ρ (Algebra.trace F L (h : L)) := by
    simp only [trF, LinearMap.comp_apply, LinearMap.restrictScalars_apply, hloc, map_smul, hτ.1, smul_eq_mul, mul_one]
  rw [← h1]
  exact GlobalTheory.T.trace_cechCochain_fraction_eq_sum_fibre ℂ F L d (xv x) hc τ hτ ρ hρ inferInstance hred h
