import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakResolutionOfPrincipalisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.GenericOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogResProj

theorem exists_logResolution : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] [CharZero F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) (D : ℕ), IsProjOver p → topologicalKrullDim X = (D : ℕ) → ∀ T : Closeds X, genericPoint X ∉ T → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (π : Y ⟶ X), SmoothOfRelativeDimension D (π ≫ p) ∧ IsProjOver (π ≫ p) ∧ topologicalKrullDim Y = D ∧ π (genericPoint Y) = genericPoint X ∧ π.residueDegree (genericPoint Y) = 1 ∧ FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal (⟨π ⁻¹' (T : Set X), T.isClosed.preimage π.continuous⟩ : Closeds Y)) := by
  intro hP F _ _ X _ p D hp hdim T hT
  obtain ⟨W', s, U, hW', hsm, hpr, hU, hiso⟩ := WeakRes.weak_resolution hP F X p D hp hdim
  have := hW'
  have g₁ := GlobalTheory.Published.generic_of_isIso_restrict s U hU
  let T' : Closeds W' := ⟨s ⁻¹' (T : Set X), T.isClosed.preimage s.continuous⟩
  let I : W'.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal T'
  have hIs : I.support = T' := by
    ext1; exact Scheme.IdealSheafData.coe_support_vanishingIdeal T'
  have hgW : genericPoint W' ∉ (T' : Set W') := by
    show s (genericPoint W') ∉ (T : Set X)
    rw [g₁.1]; exact hT
  have hI : I ≠ ⊥ := by
    intro h
    apply hgW
    have : I.support = ⊤ := by rw [h]; simp
    rw [← hIs, this]; trivial
  obtain ⟨Y, s', hY, hsm', hpr', -, hiso', -, hsnc⟩ := hP F D W' (s ≫ p) hW' hsm hpr I hI
  have := hY
  have hne : ((I.support.compl : W'.Opens) : Set W').Nonempty := ⟨genericPoint W', by
    show genericPoint W' ∉ (I.support : Set W'); rw [hIs]; exact hgW⟩
  have g₂ := GlobalTheory.Published.generic_of_isIso_restrict s' _ hne
  have hpL : LocallyOfFiniteType p := by
    obtain ⟨N, i, hi, rfl⟩ := hp
    have := isProper_str F N
    infer_instance
  have : Smooth (s ≫ p) := by haveI := hsm; exact SmoothOfRelativeDimension.smooth D _
  have : Smooth (s' ≫ s ≫ p) := by haveI := hsm'; exact SmoothOfRelativeDimension.smooth D _
  have hd₁ := GlobalTheory.OpenDim.topologicalKrullDim_eq_of_isIso_restrict F X W' p (s ≫ p) s hpL inferInstance rfl U hU hiso
  have hd₂ := GlobalTheory.OpenDim.topologicalKrullDim_eq_of_isIso_restrict F W' Y (s ≫ p) (s' ≫ s ≫ p) s' inferInstance
    inferInstance rfl _ hne hiso'
  refine ⟨Y, hY, s' ≫ s, by simpa using hsm', by simpa using hpr', by rw [hd₂, hd₁, hdim], ?_, ?_, ?_⟩
  · rw [Scheme.Hom.comp_apply, g₂.1, g₁.1]
  · rw [GlobalTheory.CurveDegreesCompare.residueDegree_comp, g₂.2, g₂.1, g₁.2, mul_one]
  · have hE : (I.comap s').support = ⟨(s' ≫ s) ⁻¹' (T : Set X), T.isClosed.preimage (s' ≫ s).continuous⟩ := by
      ext1
      rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, hIs]
      ext y; simp [T']
    rw [← hE]; exact hsnc

end GlobalTheory.LogResProj
