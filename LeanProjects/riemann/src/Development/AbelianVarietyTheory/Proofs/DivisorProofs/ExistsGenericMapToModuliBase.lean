import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfIsReducedOfRangeSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagGenericFibreIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPointResidueNonzero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldMapFiniteOfQuasiFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOnRegularFlagged
open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.MixDens GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Published
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BaseFactor

theorem exists_factor {B W G T M : Scheme.{0}} [IsIntegral B] [IsIntegral M] (j : W ⟶ B) [IsPreimmersion j]
    (π : W ⟶ G) [IsFinite π] (ι : G ⟶ T) [IsPreimmersion ι] (ρ : B ⟶ T) (b : M ⟶ T) [IsClosedImmersion b]
    (w : j ≫ ρ = π ≫ ι) (η : W) (hη : j η = genericPoint B) (y : G) (hy : y ∈ Set.range π)
    (hy' : ∀ z ∈ Set.range π, y ⤳ z) (hb : b (genericPoint M) = ι y) :
    ∃ β : B ⟶ M, β ≫ b = ρ ∧ β (genericPoint B) = genericPoint M ∧ β.residueDegree (genericPoint B) ≠ 0 := by
  have h₁ : π η = y := by
    obtain ⟨x, rfl⟩ := hy
    have hx : η ⤳ x := by
      rw [← j.isEmbedding.isInducing.specializes_iff, hη]
      exact genericPoint_specializes _
    exact ((hx.map π.continuous).antisymm (hy' _ ⟨η, rfl⟩)).eq
  have h₂ : ρ (genericPoint B) = b (genericPoint M) := by
    rw [hb, ← hη, ← h₁, ← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
  have h₃ : Set.range ρ ⊆ Set.range b := by
    rintro _ ⟨x, rfl⟩
    exact ((genericPoint_specializes x).map ρ.continuous).mem_closed b.isClosedEmbedding.isClosed_range
      ⟨_, h₂.symm⟩
  obtain ⟨β, hβ⟩ : ∃ β : B ⟶ M, β ≫ b = ρ := exists_lift_of_isReduced_of_range_subset b ρ h₃
  refine ⟨β, hβ, b.isClosedEmbedding.injective (by rw [← Scheme.Hom.comp_apply, hβ, h₂]), ?_⟩
  have h₄ : (π ≫ ι).residueDegree η ≠ 0 := by
    rw [CurveDegreesCompare.residueDegree_comp]
    exact mul_ne_zero (PullbackFinitePoint.residueDegree_ne_zero_of_surjectiveOnStalks ι _)
      ((PullbackFinitePoint.residueDegree_ne_zero_iff_finite π _).2
        (residueFieldMap_finite_of_locallyQuasiFinite π _))
  rw [← w, ← hβ, CurveDegreesCompare.residueDegree_comp, CurveDegreesCompare.residueDegree_comp, hη] at h₄
  exact right_ne_zero_of_mul (left_ne_zero_of_mul h₄)

theorem exists_factor_component : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (M : DRBase O c) (B Bg : Scheme.{0}) [IsIntegral B] (q : B ⟶ Sp (𝓞 D.what₂.LL)) (jB : Bg ⟶ B) (πB : Bg ⟶ gen O.s.T.Z) (ρ : B ⟶ O.s.T.Z.X), IsPre (genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom) (Set.range (O.Φ.C c).π) (dimGr D.what₂.Tau O.N O.j) (genι O.s.T.Z) q jB πB ρ → ∃ β : B ⟶ M.B, β ≫ M.b = ρ ∧ β ≫ strL M = q ∧ β (genericPoint B) = genericPoint M.B ∧ β.residueDegree (genericPoint B) ≠ 0 := by
  intro D O c M B Bg _ q jB πB ρ h
  obtain ⟨hq, pb, hfin, hr, w⟩ := h
  have : IsPreimmersion (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 D.what₂.LL)) (S := D.what₂.LL)
  have : IsPreimmersion jB := MorphismProperty.of_isPullback pb.flip this
  have : IsPreimmersion (spMap (algebraMap (𝓞 O.κ.c.F) O.κ.c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 O.κ.c.F)) (S := O.κ.c.F)
  have : IsPreimmersion (genι O.s.T.Z) :=
    inferInstanceAs (IsPreimmersion (Limits.pullback.fst O.s.T.Z.s (spMap (algebraMap (𝓞 O.κ.c.F) O.κ.c.F))))
  obtain ⟨η, hη⟩ : genericPoint B ∈ Set.range jB := by
    have hr := Scheme.Pullback.range_fst q (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL))
    obtain ⟨z, hz⟩ : genericPoint B ∈ Set.range (Limits.pullback.fst q
        (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL))) := hr.ge ⟨(⊥ : PrimeSpectrum D.what₂.LL), PrimeSpectrum.ext (by
      rw [FlagGenFib.asIdeal_genericPoint_eq_bot hq]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _))⟩
    exact ⟨pb.isoPullback.inv z, by rw [← Scheme.Hom.comp_apply, pb.isoPullback_inv_fst, hz]⟩
  obtain ⟨β, hβ, h₁, h₂⟩ := exists_factor jB πB (genι O.s.T.Z) ρ M.b w η hη
    ((O.Φ.C c).π (genericPoint (O.Φ.C c).Y.X)) (hr.ge ⟨_, rfl⟩) (fun z hz => by
      obtain ⟨x, rfl⟩ := hr.le hz
      exact (genericPoint_specializes x).map (O.Φ.C c).π.continuous) M.gen
  refine ⟨β, hβ, ?_, h₁, h₂⟩
  have : IsDominant jB := ⟨by
    refine Dense.mono (Set.singleton_subset_iff.2 ⟨η, hη⟩) ?_
    exact dense_iff_closure_eq.2 (genericPoint_spec B)⟩
  refine ext_of_isDominant jB ?_
  have e : spMap (algebraMap (𝓞 O.κ.c.F) O.κ.c.F) ≫ spMap (intEquiv O).toRingHom =
      spMap O.κ.e.toRingHom ≫ spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  have e' : genι O.s.T.Z ≫ O.s.T.Z.s = genStr O.s.T.Z ≫ spMap (algebraMap (𝓞 O.κ.c.F) O.κ.c.F) :=
    Limits.pullback.condition
  rw [pb.w, Category.assoc, Category.assoc, ← e, ← reassoc_of% e', ← reassoc_of% w, ← hβ]
  simp only [Category.assoc]

end GlobalTheory.BaseFactor

end
