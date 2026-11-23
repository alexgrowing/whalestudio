import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeAndRelDimOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveCrystallineBaseChangeNilpotentThickeninStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPeriodEqPeriodOverThickeningStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentOfNilpotentDividedPowersIdealStatement

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem isSeparated_left_of_isAbelianScheme {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A]
    (h : IsAbelianScheme A) : A.left.IsSeparated := by
  have h1 : IsProper A.hom := h.proper
  have h2 : IsSeparated A.hom := inferInstance
  rw [Scheme.isSeparated_iff, ← terminal.comp_from A.hom]
  infer_instance

theorem pTaylor : PTaylor := by
  intro I _ _ g B _ _ 𝒜 _ hA hg y₀ A₀ _ φ₀ hφ₀ L₀ u₀ F σ e h0 hy hE hτ P₀ hP₀ D _ _ π κ hκ hπ N t ht htN
    j hj A' _ φ' _ m' i h hi k x d hd c per hper
  obtain ⟨hA₀, hg₀⟩ := GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback _ 𝒜 A₀ φ₀ g hφ₀ hA hg
  have hspan := (GlobalTheory.T.primitiveCrystalline_baseChange_nilpotent_thickening A₀ g hA₀ hg₀ D π κ hκ hπ k).2
  have hmem : (liftMor κ h).pull (m'.pull c) ∈ Submodule.span D (Set.range k.pull) := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨n, f, v, hv⟩ := Submodule.mem_span_set'.1 hmem
  choose a ha using fun r : Fin n ↦ (v r).2
  have hsum : (liftMor κ h).pull (m'.pull c) = ∑ r, f r • k.pull (a r) := by
    rw [← hv]; exact Finset.sum_congr rfl fun r _ ↦ by rw [ha]
  let πa : D →ₐ[ℂ] ℂ := { π with commutes' := hπ }
  have M := (m'.comp (liftMor κ h)).isMor
  have nn : IsMor (dp0 B) (𝒜.hom ≫ 𝟙 _) κ (A₀.hom ≫ spMap π) (j : B →+* D) φ₀ := by
    rw [RingHom.id_comp, hi] at M
    exact M
  have hpull : nn.pull1 c.1 = ∑ r ∈ Finset.univ, f r • k.isMor.pull1 (a r).1 := by
    have e1 := IsMor.pullback1_comp m'.isMor (liftMor κ h).isMor nn (fun _ ↦ rfl) hi c.1
    have e2 := congrArg (Submodule.subtype _) hsum
    rw [map_sum] at e2
    exact e1.symm.trans e2
  have key := GlobalTheory.T.taylor_period_eq_period_over_thickening_alt (F := F) (F₀ := fibFam u₀) e (fibUnif u₀)
    (isSeparated_left_of_isAbelianScheme 𝒜 hA) (isSeparated_left_of_isAbelianScheme A₀ hA₀) h0
    (fun _ ↦ trivial) (fun l _ ↦ (hτ l).symm) φ₀ (fun p ↦ (hE p.2).symm) πa (GlobalTheory.T.isNilpotent_of_nilpotentDividedPowers_ideal κ hκ) κ
    (fun _ hd ↦ hd) N t ht htN (j : B →+* D) hj (A₀.hom ≫ spMap π)
    (by rw [Category.comp_id]; rfl) nn _ k.isMor rfl c.1 per hper Finset.univ f (fun r ↦ (a r).1)
    (fun r l ↦ P₀ l (a r)) _ (fun _ _ ↦ rfl) (fun r ↦ hP₀ (a r)) hpull x
  rw [crysToDR_apply, hsum, map_sum, ← key]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [map_smul, hd (a r), smul_eq_mul]

end GlobalTheory.AnPer
