import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreIsAbelianSchemeRelDimOfFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianCechH1TrivialBundleRankBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechFirstCohomologyDimensionBoundCocyclesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleCoboundaryOfCoveringSubfamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageQuotientFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePullbackAffineFunctionEqQuotientConstStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.FibreH1

theorem resG_appLE {Y : Scheme.{0}} {K : Type} [CommRing K] (s : Y ⟶ Sp K) {V V' : Y.Opens} (h : V' ≤ V)
    (x : Γ(Sp K, ⊤)) : resG Y h ((s.appLE ⊤ V le_top).hom x) = (s.appLE ⊤ V' le_top).hom x := by
  exact congrArg (fun φ : Γ(Sp K, ⊤) ⟶ Γ(Y, V') => φ.hom x)
    (Scheme.Hom.appLE_map s (U := ⊤) le_top (homOfLE h).op)

theorem fieldDep : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (J : Type) (W : J → A.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = ⊤ → ∀ (e : Fin (g + 1) → ∀ i i' : J, Γ(A.left, W i ⊓ W i')), (∀ b i i' i'', resG A.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (e b i i') + resG A.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (e b i' i'') = resG A.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (e b i i'')) → ∃ c : Fin (g + 1) → K, c ≠ 0 ∧ ∃ h : ∀ i, Γ(A.left, W i), ∀ i i', ∑ b, (A.hom.appLE ⊤ (W i ⊓ W i') le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c b)) * e b i i' = resG A.left inf_le_left (h i) - resG A.left inf_le_right (h i') := by
  intro K _ A _ g hA hsm J W hW hcov e he
  haveI := hA.proper
  haveI : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun i => (W i : Set A.left))
    (fun i => (W i).isOpen) (by
      intro x _
      have hx : x ∈ (⨆ i, W i) := by rw [hcov]; trivial
      rw [TopologicalSpace.Opens.mem_iSup] at hx
      exact Set.mem_iUnion.2 hx)
  let σ : Fin t.card → J := fun k => (t.equivFin.symm k).1
  have hσ : ⨆ k, W (σ k) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨t.equivFin ⟨i, hi⟩, by simpa [σ] using hx⟩
  obtain ⟨hfin, hrk⟩ := GlobalTheory.T.abelian_cech_h1_trivial_bundle_rank_bound K A g hA hsm (Fin t.card) (fun k => W (σ k)) (fun k => hW _) hσ
  obtain ⟨c, hc, h', hh'⟩ := GlobalTheory.T.cech_first_cohomology_dimension_bound_cocycles K A.left A.hom g (Fin t.card) (fun k => W (σ k)) hfin hrk
    (fun b k k' => e b (σ k) (σ k')) (fun b k k' k'' => he b _ _ _)
  refine ⟨c, hc, ?_⟩
  exact GlobalTheory.T.cechCocycle_coboundary_of_coveringSubfamily A.left J W (Fin t.card) σ hσ
    (fun i i' => ∑ b, (A.hom.appLE ⊤ (W i ⊓ W i') le_top).hom
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c b)) * e b i i') (by
      intro i i' i''
      simp only [map_sum, map_mul, resG_appLE]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← mul_add, he b]) h' hh'

theorem fibre_dim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (J : Type) (W : J → t.G.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → ∀ (e : Fin (n + 1) → ∀ i i' : J, Γ(A.left, ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i')), (∀ b, (∀ i i' i'', resG A.left (inf_le_left : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'' ≤ ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (e b i i') + resG A.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'' ≤ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'') (e b i' i'') = resG A.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'' ≤ ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i'') (e b i i''))) → ∃ r : Fin (n + 1) → Γ(X, U.1), (∃ b, r b ∉ m) ∧ ∃ h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i), ∀ i i', ∑ b, (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom ((t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b)) * e b i i' = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i') := by
  intro E _ _ _ H X t hprop hamp U n v hv huniq J W hWa hcov hWU m hm A _ ι hpb e he
  letI : Field (Γ(X, U.1) ⧸ m) := Ideal.Quotient.field m
  obtain ⟨hA, hsm⟩ := GlobalTheory.T.closedFibre_isAbelianScheme_relDim_of_frame E H X t hprop U n v hv huniq m hm A ι hpb
  have hsq := hpb.1
  have hw : ι ≫ t.G.hom = A.hom ≫ spMap (Ideal.Quotient.mk m) ≫ chart U := hsq.w
  have htop : ⨆ i, ι ⁻¹ᵁ W i = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : t.G.hom.base (ι.base x) ∈ (U.1 : Set X) := by
      change (ι ≫ t.G.hom).base x ∈ _
      rw [hw, ← U.2.range_fromSpec]
      exact ⟨_, rfl⟩
    have hx' : ι.base x ∈ (⨆ i, W i) := by rw [hcov]; exact hx
    rw [TopologicalSpace.Opens.mem_iSup] at hx' ⊢
    exact hx'
  have haff : ∀ i, IsAffineOpen (ι ⁻¹ᵁ W i) := fun i =>
    GlobalTheory.T.isAffineOpen_preimage_quotientFibre X t.G.left t.G.hom U m A.left A.hom ι hsq (W i) (hWa i) (hWU i)
  obtain ⟨c, hc, h, hh⟩ := fieldDep (Γ(X, U.1) ⧸ m) A n hA hsm J (fun i => ι ⁻¹ᵁ W i) haff htop e he
  choose r hr using fun b => Ideal.Quotient.mk_surjective (c b)
  refine ⟨r, ?_, h, fun i i' => ?_⟩
  · obtain ⟨b, hb⟩ := Function.ne_iff.1 hc
    refine ⟨b, fun hmem => hb ?_⟩
    rw [← hr b]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hmem
  · rw [← hh i i']
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [GlobalTheory.T.fibre_pullback_affineFunction_eq_quotientConst X t.G.left t.G.hom U m A.left A.hom ι hw (W i ⊓ W i') (inf_le_left.trans (hWU i))
      (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx), hr b]

end GlobalTheory.FibreH1
