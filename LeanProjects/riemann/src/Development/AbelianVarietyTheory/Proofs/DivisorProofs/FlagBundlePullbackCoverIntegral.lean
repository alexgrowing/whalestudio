import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularCoverOfAlterationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleSmoothRelativeDimensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProjectionSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleTotalSpaceIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProjectiveOverBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullDimSmoothSurjectiveTotalStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundleCover

theorem pullback_regCover_isArithVar : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (D : ℕ), IsArithVar q 1 → IsArithVar p D → ∀ (π : Y ⟶ B), π ≫ q = p → ∀ (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ), (∀ a, VB.IsVB (E a) (r a)) → ∀ (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → ∀ C : RegCover q, IsIntegral (Limits.pullback π C.ρ) ∧ IsArithVar (Limits.pullback.fst π C.ρ ≫ p) D ∧ π (genericPoint Y) = genericPoint B := by
  intro k _ B Y _ _ q p D hq hp π hπ ι _ E r hE fl hfl C
  have hreg := C.reg
  haveI : IsLocallyNoetherian B := hq.isLocallyNoetherian
  haveI : IsLocallyNoetherian C.Y := hreg.toIsArithVar.isLocallyNoetherian
  haveI : IsNoetherianRing k := hq.isNoetherianRing
  have hs : Function.Surjective π := GlobalTheory.T.flag_bundle_projection_surjective B Y π ι E r fl hE hfl
  haveI hsm : SmoothOfRelativeDimension (∑ a, r a * (r a - 1) / 2) π := GlobalTheory.T.flag_bundle_smooth_relative_dimension B Y π ι E r fl hE hfl
  have hE' : ∀ a, VB.IsVB ((Scheme.Modules.pullback C.ρ).obj (E a)) (r a) := fun a => (hE a).pullback C.ρ
  have hfl' := GlobalTheory.T.flag_bundle_base_change B Y C.Y π ι E r fl hfl C.ρ
  haveI hsm' : SmoothOfRelativeDimension (∑ a, r a * (r a - 1) / 2) (Limits.pullback.snd π C.ρ) :=
    GlobalTheory.T.flag_bundle_smooth_relative_dimension _ _ _ ι _ r _ hE' hfl'
  have hs' : Function.Surjective (Limits.pullback.snd π C.ρ) := GlobalTheory.T.flag_bundle_projection_surjective _ _ _ ι _ r _ hE' hfl'
  haveI : IrreducibleSpace (Limits.pullback π C.ρ : Scheme.{0}) := GlobalTheory.T.flag_bundle_total_space_irreducible _ _ _ ι _ r _ hE' hfl'
  haveI : Smooth (Limits.pullback.snd π C.ρ) := SmoothOfRelativeDimension.smooth (∑ a, r a * (r a - 1) / 2) _
  haveI : IsReduced (Limits.pullback π C.ρ) := GlobalTheory.isReduced_of_smooth_of_isReduced (Limits.pullback.snd π C.ρ)
  haveI hint : IsIntegral (Limits.pullback π C.ρ) := isIntegral_of_irreducibleSpace_of_isReduced _
  have e : Limits.pullback.fst π C.ρ ≫ p = Limits.pullback.snd π C.ρ ≫ C.ρ ≫ q := by
    rw [← hπ, ← Category.assoc, Limits.pullback.condition, Category.assoc]
  refine ⟨hint, ⟨hp.isDomain, hp.finite, hint, ?_, ?_, ?_⟩, ?_⟩
  · rw [e]
    exact GlobalTheory.T.flag_bundle_projective_over_base k C.Y _ (C.ρ ≫ q) _ ι _ r _ hreg.isProjOver hE' hfl'
  · rw [e, Category.assoc]
    haveI := hreg.flat
    infer_instance
  · have h1 := GlobalTheory.T.krull_dim_smooth_surjective_total B Y π (∑ a, r a * (r a - 1) / 2) 1 hs hq.dim_eq
    have h2 := GlobalTheory.T.krull_dim_smooth_surjective_total C.Y _ (Limits.pullback.snd π C.ρ) (∑ a, r a * (r a - 1) / 2) 1 hs' hreg.dim_eq
    rw [h2, ← h1]
    exact hp.dim_eq
  · have hg : IsGenericPoint (π (genericPoint Y)) (⊤ : Set B) := by
      have h1 := genericPoint_spec Y
      show closure {π (genericPoint Y)} = ⊤
      refine eq_top_iff.2 fun b _ => ?_
      obtain ⟨y, rfl⟩ := hs b
      have hy : y ∈ closure {genericPoint Y} := by rw [h1.def]; trivial
      exact map_mem_closure π.continuous hy (by intro z hz; rw [Set.mem_singleton_iff.1 hz]; rfl)
    exact hg.eq (genericPoint_spec B)

end GlobalTheory.FlagBundleCover

end
