import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.ClosFacts

theorem range_closι {X : Scheme.{0}} (z : X) : range (closι z) = closure {z} :=
  range_redι (Closeds.closure {z})

theorem isIntegral_clos {X : Scheme.{0}} (z : X) : IsIntegral (clos z) :=
  isIntegral_red (Z := Closeds.closure {z}) isIrreducible_singleton.closure

theorem clos_facts : ∀ (X : Scheme.{0}) (z : X), ∃ _ : IsIntegral (clos z), closι z (genericPoint (clos z)) = z ∧ topologicalKrullDim (clos z) = topologicalKrullDim (closure ({z} : Set X)) ∧ ∀ (Y : Scheme.{0}) [IsIntegral Y] (π : Y ⟶ X), π (genericPoint Y) = z → ∃ g : Y ⟶ clos z, g ≫ closι z = π ∧ g (genericPoint Y) = genericPoint (clos z) ∧ g.residueDegree (genericPoint Y) = π.residueDegree (genericPoint Y) ∧ (IsClosedImmersion π → IsIso g) := by
  intro X z
  have hI := isIntegral_clos z
  have hr := range_closι z
  have hi : closι z (genericPoint (clos z)) = z := by
    have h₁ := (genericPoint_spec (clos z)).image (closι z).continuous
    rw [image_univ, hr, closure_closure] at h₁
    exact h₁.eq isGenericPoint_closure
  refine ⟨hI, hi, (topologicalKrullDim_eq_of_isEmbedding (closι z).isClosedEmbedding.isEmbedding hr), ?_⟩
  intro Y _ π hπ
  have : Surjective (Limits.pullback.snd (closι z) π) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd, hr, ← hπ]
    exact eq_univ_of_forall fun y => ((genericPoint_specializes y).map π.continuous).mem_closure⟩
  have := isIso_of_isClosedImmersion_of_surjective (Limits.pullback.snd (closι z) π)
  obtain ⟨g, rfl⟩ : ∃ g : Y ⟶ clos z, g ≫ closι z = π :=
    ⟨inv (Limits.pullback.snd (closι z) π) ≫ Limits.pullback.fst (closι z) π, by
      rw [Category.assoc, Limits.pullback.condition, IsIso.inv_hom_id_assoc]⟩
  have hg : g (genericPoint Y) = genericPoint (clos z) :=
    (closι z).isClosedEmbedding.injective (hπ.trans hi.symm)
  refine ⟨g, rfl, hg, ?_, fun hc => ?_⟩
  · rw [GlobalTheory.CurveDegreesCompare.residueDegree_comp, GlobalTheory.Published.residueDegree_of_isClosedImmersion (closι z), one_mul]
  · have : IsClosedImmersion g := IsClosedImmersion.of_comp_isClosedImmersion g (closι z)
    have : Surjective g := ⟨by
      rw [← Set.range_eq_univ]
      have h₁ := (genericPoint_spec Y).image g.continuous
      rw [image_univ, g.isClosedEmbedding.isClosed_range.closure_eq, hg] at h₁
      exact h₁.def.symm.trans (genericPoint_spec (clos z)).def⟩
    exact isIso_of_isClosedImmersion_of_surjective g

end GlobalTheory.ClosFacts
