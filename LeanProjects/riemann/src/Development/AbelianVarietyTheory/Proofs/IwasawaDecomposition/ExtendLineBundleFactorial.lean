import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsLineBundleExtension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlueLineBundlesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LbIsoOfDisjointCoverStatement

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.ExtendLineBundleComponents

theorem exists_integral_components (X : Scheme.{0}) [IsLocallyNoetherian X] [CompactSpace X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) :
    ∃ (A : Type) (V : A → X.Opens), (∀ a b x, x ∈ V a → x ∈ V b → a = b) ∧ (∀ x, ∃ a, x ∈ V a) ∧
      ∀ a, IsIntegral (V a).toScheme ∧ CompactSpace (V a).toScheme := by
  have : IsNoetherian X := {}
  have hfin := (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X))
  have heq : ∀ (x : X) (Z W : Set X), Z ∈ irreducibleComponents X → W ∈ irreducibleComponents X →
      x ∈ Z → x ∈ W → Z = W := by
    intro x Z W hZ hW hxZ hxW
    have := hX x
    exact GlobalTheory.IsNormalScheme.eq_of_mem_irreducibleComponents_of_isDomain hZ hW hxZ hxW
  have hopen : ∀ Z ∈ irreducibleComponents X, IsOpen Z := fun Z hZ => by
    have e : Zᶜ = ⋃ W ∈ irreducibleComponents X \ {Z}, W := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_iUnion, exists_prop]
      constructor
      · intro hx
        refine ⟨_, ⟨irreducibleComponent_mem_irreducibleComponents x, fun h ↦ hx ?_⟩,
          mem_irreducibleComponent⟩
        exact (show irreducibleComponent x = Z from h) ▸ mem_irreducibleComponent
      · rintro ⟨W, ⟨hW, hne⟩, hxW⟩ hxZ
        exact hne (heq x W Z hW hZ hxW hxZ)
    rw [← isClosed_compl_iff, e]
    exact hfin.sdiff.isClosed_biUnion fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1
  have : IsReduced X := isReduced_of_isReduced_stalk _
  let V : irreducibleComponents X → X.Opens := fun Z => ⟨Z.1, hopen Z.1 Z.2⟩
  refine ⟨irreducibleComponents X, V, fun a b x ha hb => Subtype.ext (heq x a b a.2 b.2 ha hb),
    fun x => ⟨⟨_, irreducibleComponent_mem_irreducibleComponents x⟩, mem_irreducibleComponent⟩,
    fun a => ?_⟩
  have : IrreducibleSpace (V a).toScheme := Subtype.irreducibleSpace a.2.1
  refine ⟨isIntegral_of_irreducibleSpace_of_isReduced _, ?_⟩
  exact isCompact_iff_compactSpace.mp (isClosed_of_mem_irreducibleComponents a.1 a.2).isCompact

theorem uniqueFactorizationMonoid_stalk_toScheme (X : Scheme.{0}) (U : X.Opens)
    (hX : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) (y : U.toScheme) :
    UniqueFactorizationMonoid (U.toScheme.presheaf.stalk y) :=
  MulEquiv.uniqueFactorizationMonoid
    (asIso (U.ι.stalkMap y)).commRingCatIsoToRingEquiv.toMulEquiv (hX _)

end GlobalTheory.ExtendLineBundleComponents

open GlobalTheory.ExtendLineBundleComponents GlobalTheory.GenSpread in

theorem GlobalTheory.exists_lineBundle_extension_of_isDomain : ∀ (X Y : Scheme.{0}) [IsLocallyNoetherian X]
    [CompactSpace X] (j : Y ⟶ X), IsOpenImmersion j → (∀ x : X, IsDomain (X.presheaf.stalk x)) →
    (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) → ∀ L : LB Y, L.IsLB →
    ∃ L' : LB X, L'.IsLB ∧ LBIso (L'.pull j) L := by
  intro X Y _ _ j hj hdom hufm L hL
  obtain ⟨A, V, hd, hc, hV⟩ := exists_integral_components X hdom
  have key : ∀ a, ∃ M : LB (V a).toScheme, M.IsLB ∧
      LBIso (M.pull (j ∣_ V a)) (L.pull (j ⁻¹ᵁ V a).ι) := by
    intro a
    have := (hV a).1
    have := (hV a).2
    obtain ⟨M, hM, φ, hφ⟩ := GlobalTheory.exists_lineBundle_extension (V a).toScheme (j ⁻¹ᵁ V a).toScheme
      (j ∣_ V a) inferInstance (uniqueFactorizationMonoid_stalk_toScheme X (V a) hufm)
      (L.pull (j ⁻¹ᵁ V a).ι) (pull_isLB hL _)
    exact ⟨M, hM, φ, hφ⟩
  choose M hM hML using key
  obtain ⟨N, hN, hNM⟩ := GlobalTheory.T.exists_lineBundle_glue_disjoint_cover X A V hd hc M hM
  refine ⟨N, hN, GlobalTheory.T.lbIso_of_lbIso_on_disjoint_cover Y A (fun a => j ⁻¹ᵁ V a) (fun a b y ha hb => hd a b _ ha hb)
    (fun y => hc (j y)) _ _ (pull_isLB hN j) hL fun a => ?_⟩
  have e1 : LBIso ((N.pull j).pull (j ⁻¹ᵁ V a).ι) ((N.pull (V a).ι).pull (j ∣_ V a)) :=
    LBIso.trans (pull_isLB (pull_isLB hN j) _) (pull_isLB hN _) (pull_isLB (pull_isLB hN _) _)
      (lbIso_pull_pull hN _ rfl).symm (lbIso_pull_pull hN _ (morphismRestrict_ι j (V a)).symm)
  have e2 : LBIso ((N.pull (V a).ι).pull (j ∣_ V a)) ((M a).pull (j ∣_ V a)) :=
    lbIso_pullback (hNM a) _
  exact LBIso.trans (pull_isLB (pull_isLB hN j) _) (pull_isLB (pull_isLB hN _) _) (pull_isLB hL _) e1
    (LBIso.trans (pull_isLB (pull_isLB hN _) _) (pull_isLB (hM a) _) (pull_isLB hL _) e2 (hML a))
