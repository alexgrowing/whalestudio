import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
import Formalism.LocalToGlobal.IndefiniteReal.MultLemmas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumOfMemMultSpan
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KStableOfIsGKSub
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.KTypeProj

theorem typeSpan_proj_mem {M ι : Type} [AddCommGroup M] [Module ℂ M] (b : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (G : Submodule ℂ M)
    (ρ : ι → M →ₗ[ℂ] M) (inv : ι → ι) (hpos : ∀ x ∈ G, x ≠ 0 → 0 < (b x x).re)
    (hherm : ∀ x ∈ G, ∀ y ∈ G, star (b x y) = b y x)
    (_hρG : ∀ i, ∀ x ∈ G, ρ i x ∈ G) (hadj : ∀ i, ∀ x ∈ G, ∀ y ∈ G, b (ρ i x) y = b x (ρ (inv i) y))
    (hproj : ∀ F : Submodule ℂ M, F ≤ G → FiniteDimensional ℂ F →
      ∃ π : M →ₗ[ℂ] M, (∀ x, π x ∈ F) ∧ ∀ x, ∀ f ∈ F, b (π x) f = b x f)
    (Y₀ : Submodule ℂ M) (e : M →ₗ[ℂ] M) (he : ∀ x, e x ∈ typeSpan ρ Y₀ G)
    (he' : ∀ x, ∀ f ∈ typeSpan ρ Y₀ G, b (e x) f = b x f)
    (Y : Submodule ℂ M) (hYf : FiniteDimensional ℂ Y) (hYG : Y ≤ G) (hYρ : ∀ i, ∀ y ∈ Y, ρ i y ∈ Y) :
    ∀ x ∈ Y, e x ∈ Y := by
  intro x hx
  have hzero : ∀ d ∈ G, b d d = 0 → d = 0 := by
    intro d hd h
    by_contra hne
    have := hpos d hd hne
    rw [h] at this
    simp at this
  obtain ⟨π, hπY, hπ⟩ := hproj Y hYG hYf
  have hcomm : ∀ i, ∀ z ∈ G, π (ρ i z) = ρ i (π z) := by
    intro i z hz
    have hdY : π (ρ i z) - ρ i (π z) ∈ Y := Y.sub_mem (hπY _) (hYρ i _ (hπY z))
    have hpair : ∀ y ∈ Y, b (π (ρ i z) - ρ i (π z)) y = 0 := by
      intro y hy
      have h1 : b (π (ρ i z)) y = b (ρ i z) y := hπ _ y hy
      have h2 : b (ρ i z) y = b z (ρ (inv i) y) := hadj i z hz y (hYG hy)
      have h3 : b z (ρ (inv i) y) = b (π z) (ρ (inv i) y) := (hπ z _ (hYρ (inv i) y hy)).symm
      have h4 : b (ρ i (π z)) y = b (π z) (ρ (inv i) y) := hadj i (π z) (hYG (hπY z)) y (hYG hy)
      rw [map_sub, LinearMap.sub_apply, h1, h2, h3, h4, sub_self]
    exact sub_eq_zero.mp (hzero _ (hYG hdY) (hpair _ hdY))
  have hSG : typeSpan ρ Y₀ G ≤ G := typeSpan_le ρ Y₀ G
  have hY1f : FiniteDimensional ℂ (typeSpan ρ Y₀ G ⊓ Y : Submodule ℂ M) :=
    Submodule.finiteDimensional_of_le inf_le_right
  obtain ⟨π₁, hπ₁Y, hπ₁⟩ := hproj (typeSpan ρ Y₀ G ⊓ Y) (inf_le_left.trans hSG) hY1f
  have hpS : π₁ x ∈ typeSpan ρ Y₀ G := (hπ₁Y x).1
  have hpY : π₁ x ∈ Y := (hπ₁Y x).2
  have hxp : x - π₁ x ∈ Y := Y.sub_mem hx hpY
  have hle : typeSpan ρ Y₀ G ≤ LinearMap.ker (b (x - π₁ x)) := by
    refine iSup₂_le fun T hT => ?_
    rintro _ ⟨w, hw, rfl⟩
    rw [LinearMap.mem_ker]
    have hTw : T w ∈ G := hT.1 ⟨w, hw, rfl⟩
    have hπT : π (T w) ∈ typeSpan ρ Y₀ G ⊓ Y := by
      refine ⟨?_, hπY _⟩
      have hm := map_le_typeSpan ρ (Y₀ := Y₀) (G := G) (π ∘ₗ T) ?_ ?_
      · exact hm ⟨w, hw, rfl⟩
      · rintro _ ⟨v, -, rfl⟩; exact hYG (hπY _)
      · intro i v hv
        simp only [LinearMap.comp_apply]
        rw [hT.2 i v hv, hcomm i _ (hT.1 ⟨v, hv, rfl⟩)]
    have e1 : b (x - π₁ x) (π (T w)) = 0 := by
      rw [map_sub, LinearMap.sub_apply, hπ₁ x _ hπT, sub_self]
    have e2 : b (T w - π (T w)) (x - π₁ x) = 0 := by
      rw [map_sub b (T w) (π (T w)), LinearMap.sub_apply, hπ (T w) _ hxp, sub_self]
    have e3 : b (x - π₁ x) (T w - π (T w)) = 0 := by
      rw [← hherm _ (G.sub_mem hTw (hYG (hπY _))) _ (hYG hxp), e2, star_zero]
    have hsplit : T w = π (T w) + (T w - π (T w)) := by abel
    rw [hsplit, map_add, e1, e3, add_zero]
  have hd : e x - π₁ x ∈ typeSpan ρ Y₀ G := Submodule.sub_mem _ (he x) hpS
  have hdd : b (e x - π₁ x) (e x - π₁ x) = 0 := by
    have h1 := he' x _ hd
    have h2 := LinearMap.mem_ker.mp (hle hd)
    rw [map_sub b x (π₁ x), LinearMap.sub_apply] at h2
    rw [map_sub b (e x) (π₁ x), LinearMap.sub_apply]
    rw [h1, sub_eq_zero.mp h2, sub_self]
  have h0 := hzero _ (hSG hd) hdd
  rw [sub_eq_zero.mp h0]
  exact hpY

end GlobalTheory.KTypeProj

end
