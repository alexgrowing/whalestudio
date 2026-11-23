import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GeoModel.OpenLocus

theorem exists_dense_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel ℤ x) (f : M.X ⟶ Y.X) (y₀ : Sp Ω ⟶ Xo.XF c), M.ξ ≫ f = y₀ ≫ Y.j → ∃ U : (pullback (f ≫ Y.s) (spMap (algebraMap (𝓞 c.F) c.F))).Opens, Dense (U : Set ((pullback (f ≫ Y.s) (spMap (algebraMap (𝓞 c.F) c.F)) : Scheme.{0}))) ∧ pullback.fst (f ≫ Y.s) (spMap (algebraMap (𝓞 c.F) c.F)) ⁻¹' (f ⁻¹' abLocus Y.t.G) = U := by
  intro E _ _ _ H D l Xo c Y Ω _ κ _ x M f y₀ hξ
  set π := spMap (algebraMap (𝓞 c.F) c.F) with hπ
  haveI : IsOpenImmersion Y.jQ := Y.jQ_open
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := {}
  haveI hpre : IsPreimmersion π :=
    IsPreimmersion.of_isLocalization (R := 𝓞 c.F) (S := c.F) (nonZeroDivisors (𝓞 c.F))
  haveI hfst : IsPreimmersion (pullback.fst (f ≫ Y.s) π) := inferInstance
  have hcond : (pullback.fst (f ≫ Y.s) π ≫ f) ≫ Y.s = pullback.snd (f ≫ Y.s) π ≫ π := by
    rw [Category.assoc, pullback.condition]
  set g := pullback.lift (pullback.fst (f ≫ Y.s) π ≫ f) (pullback.snd (f ≫ Y.s) π) hcond with hg
  have hgf : g ≫ pullback.fst Y.s π = pullback.fst (f ≫ Y.s) π ≫ f := pullback.lift_fst _ _ _
  have hpt : ∀ p, f (pullback.fst (f ≫ Y.s) π p) = pullback.fst Y.s π (g p) := by
    intro p
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hgf]
  have hopen : IsOpen (g ⁻¹' Set.range Y.jQ) :=
    (IsOpenImmersion.isOpen_range Y.jQ).preimage g.continuous
  refine ⟨⟨g ⁻¹' Set.range Y.jQ, hopen⟩, ?_, ?_⟩
  · have hc2 : M.ξ ≫ f ≫ Y.s = (y₀ ≫ Y.jQ ≫ pullback.snd Y.s π) ≫ π := by
      rw [← Category.assoc, hξ]
      simp only [Model.j, Category.assoc, pullback.condition]
      rfl
    set ξ' := pullback.lift M.ξ (y₀ ≫ Y.jQ ≫ pullback.snd Y.s π) hc2 with hξ'
    have hξg : ξ' ≫ g = y₀ ≫ Y.jQ := by
      apply pullback.hom_ext
      · rw [Category.assoc, hgf, ← Category.assoc, pullback.lift_fst, hξ]
        simp only [Model.j, Category.assoc]
        rfl
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.assoc]
    set p0 := ξ' (IsLocalRing.closedPoint Ω) with hp0
    have hp0U : p0 ∈ g ⁻¹' Set.range Y.jQ := by
      refine ⟨y₀ (IsLocalRing.closedPoint Ω), ?_⟩
      have h := congrArg (fun (k : Spec (CommRingCat.of Ω) ⟶ pullback Y.s π) => k (IsLocalRing.closedPoint Ω)) hξg
      change g (ξ' (IsLocalRing.closedPoint Ω)) = Y.jQ (y₀ (IsLocalRing.closedPoint Ω)) at h
      exact h.symm
    have hp0M : pullback.fst (f ≫ Y.s) π p0 = genPt M.ξ := by
      have h := congrArg (fun (k : Spec (CommRingCat.of Ω) ⟶ M.X) => k (IsLocalRing.closedPoint Ω))
        (pullback.lift_fst M.ξ (y₀ ≫ Y.jQ ≫ pullback.snd Y.s π) hc2)
      change pullback.fst (f ≫ Y.s) π (ξ' (IsLocalRing.closedPoint Ω)) = M.ξ (IsLocalRing.closedPoint Ω) at h
      exact h
    have hemb := Scheme.Hom.isEmbedding (pullback.fst (f ≫ Y.s) π)
    intro p
    have hsp : p0 ⤳ p := by
      rw [← hemb.isInducing.specializes_iff, hp0M]
      exact M.all _
    exact closure_mono (Set.singleton_subset_iff.2 hp0U) (specializes_iff_mem_closure.1 hsp)
  · ext p
    simp only [Set.mem_preimage, TopologicalSpace.Opens.coe_mk]
    rw [hpt, ← Set.mem_preimage (f := pullback.fst Y.s π), Y.ab_gen]

end GlobalTheory.CompanionTheory.Ar.GeoModel.OpenLocus
