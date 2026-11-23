import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ExistsChow

set_option autoImplicit false
set_option maxSynthPendingDepth 1

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
  TopologicalSpace

namespace GlobalTheory.CompanionTheory.GE.ChowOpen

lemma isClosedImmersion_restrict_iSup {T Z : Scheme.{0}} (f : T ⟶ Z) {ι : Type} (V : ι → Z.Opens)
    (h : ∀ i, IsClosedImmersion (f ∣_ V i)) : IsClosedImmersion (f ∣_ (⨆ i, V i)) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun i => (⨆ i, V i).ι ⁻¹ᵁ V i) ?_ ?_
  · refine top_le_iff.1 fun x _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 x.2
    exact Opens.mem_iSup.2 ⟨i, hi⟩
  · intro i
    have hV : (⨆ i, V i).ι ''ᵁ ((⨆ i, V i).ι ⁻¹ᵁ V i) = V i := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact inf_eq_right.2 (le_iSup V i)
    have e := morphismRestrictRestrict f (⨆ i, V i) ((⨆ i, V i).ι ⁻¹ᵁ V i)
    have h' : IsClosedImmersion (f ∣_ ((⨆ i, V i).ι ''ᵁ ((⨆ i, V i).ι ⁻¹ᵁ V i))) := by
      rw [hV]; exact h i
    exact (MorphismProperty.arrow_mk_iso_iff (@IsClosedImmersion) e).2 h'

theorem exists_image_open {T Z : Scheme.{0}} (f : T ⟶ Z) [QuasiCompact f] (S : Z.Opens)
    [IsClosedImmersion (f ∣_ S)] (hS : f ⁻¹ᵁ S = ⊤) :
    ∃ (O : f.image.Opens) (φ : O.toScheme ⟶ T), IsIso φ ∧ φ ≫ f = O.ι ≫ f.imageι := by
  have hι : IsIso (f ⁻¹ᵁ S).ι := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    exact ⟨inferInstance, ⟨by rw [← Set.range_eq_univ, Scheme.Opens.range_ι, hS]; rfl⟩⟩
  refine ⟨f.imageι ⁻¹ᵁ S, SchemeImage.imageRestrictLift f S ≫ (f ⁻¹ᵁ S).ι, inferInstance, ?_⟩
  rw [Category.assoc, ← morphismRestrict_ι, SchemeImage.imageRestrictLift_fac_assoc,
    morphismRestrict_ι]

theorem exists_chow_open_projective {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    (s : X ⟶ Spec (.of A)) [IsSeparated s] [LocallyOfFiniteType s] [QuasiCompact s]
    [IrreducibleSpace X] :
    ∃ (N : ℕ) (Y : Scheme.{0}) (i : Y ⟶ projectiveSpace A N) (O : Y.Opens)
      (ψ : (O : Scheme.{0}) ⟶ X) (W : X.Opens), IsClosedImmersion i ∧ IsProper ψ ∧
      O.ι ≫ i ≫ ProjSpace.toSpecBase A N = ψ ≫ s ∧ (W : Set X).Nonempty ∧ IsIso (ψ ∣_ W) := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have : IsNoetherian X := ⟨⟩
  have hex : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V := fun x => by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨V, hV, hxV⟩
  choose V hVaff hxV using hex
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (V x : Set X))
    (fun x => (V x).2) (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)
  have htne : t.Nonempty := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    obtain ⟨y, hy, -⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨y, hy⟩
  obtain ⟨k, hk⟩ : ∃ k, t.card = k + 1 := ⟨t.card - 1, by have := htne.card_pos; omega⟩
  let e : Fin (k + 1) ≃ t := (Fintype.equivFinOfCardEq (by simpa using hk)).symm
  let U : Fin (k + 1) → X.Opens := fun j => V (e j)
  have hUaff : ∀ j, IsAffineOpen (U j) := fun j => hVaff _
  have hU : iSup U = ⊤ := by
    refine top_le_iff.1 fun x _ => ?_
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact Opens.mem_iSup.2 ⟨e.symm ⟨y, hy⟩, by simpa [U] using hxy⟩
  have hc := fun j => ProjSpace.exists_closedImmersion_stdOpen (A := A) s (hUaff j)
  choose n c hccl hcc using hc
  have : ∀ j, IsClosedImmersion (c j) := hccl
  have hη : genericPoint X ∈ ChowGraph.W U := by
    rw [ChowGraph.W, ← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
    intro j
    exact ((genericPoint_spec X).mem_open_set_iff (U j).2).2
      ⟨e j, Set.mem_univ _, hxV _⟩
  have : NoetherianSpace (ChowGraph.W U).toScheme :=
    NoetherianSpace.set ((ChowGraph.W U : X.Opens) : Set X)
  have : QuasiCompact (ChowGraph.g s n U c hcc) := ⟨fun _ _ _ => NoetherianSpace.isCompact _⟩
  have hqc : QuasiCompact (ChowGraph.q s n U c hcc) := by
    unfold ChowGraph.q; infer_instance
  have hcl : IsClosedImmersion
      (ChowGraph.q s n U c hcc ∣_ (⨆ i, ChowGraph.V (A := A) n i)) :=
    isClosedImmersion_restrict_iSup _ _ fun i =>
      ChowGraph.isClosedImmersion_q_restrict s n U c hcc i
  have hS : ChowGraph.q s n U c hcc ⁻¹ᵁ (⨆ i, ChowGraph.V (A := A) n i) = ⊤ := by
    refine top_le_iff.1 fun y _ => ?_
    have hy : ChowGraph.π s n U c hcc y ∈ (⊤ : X.Opens) := trivial
    rw [← hU] at hy
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hy
    exact Opens.mem_iSup.2 ⟨i, ChowGraph.q_mem_V s n U c hcc i y hi⟩
  obtain ⟨O, φ, hφ, hφq⟩ := exists_image_open (ChowGraph.q s n U c hcc) _ hS
  have hπ : IsProper (ChowGraph.π s n U c hcc) := by
    unfold ChowGraph.π; infer_instance
  refine ⟨ProjSpace.multiProjDim k n, (ChowGraph.q s n U c hcc).image,
    (ChowGraph.q s n U c hcc).imageι ≫ ProjSpace.multiProjEmb A k n, O,
    φ ≫ ChowGraph.π s n U c hcc, ChowGraph.W U, inferInstance, inferInstance, ?_, ⟨_, hη⟩, ?_⟩
  · rw [Category.assoc, ProjSpace.multiProjEmb_toSpecBase, ← Category.assoc, ← hφq]
    simp only [ChowGraph.q, ChowGraph.π, Category.assoc, pullback.condition]
  · rw [morphismRestrict_comp]
    have := ChowGraph.isIso_π_restrict s n U c hcc
    have h1 : IsIso (φ ∣_ (ChowGraph.π s n U c hcc ⁻¹ᵁ ChowGraph.W U)) :=
      IsZariskiLocalAtTarget.restrict (P := MorphismProperty.isomorphisms Scheme) hφ _
    exact IsIso.comp_isIso' h1 this

theorem exists_chow_open {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))]
    [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] [IsIntegral X] :
    ∃ (N : ℕ) (Y : Scheme.{0}) (i : Y ⟶ projectiveSpace A N) (O : Y.Opens)
      (ψ : (O : Scheme.{0}) ⟶ X) (W : X.Opens), IsClosedImmersion i ∧ IsProper ψ ∧
      O.ι ≫ i ≫ ProjSpace.toSpecBase A N = ψ ≫ (X ↘ Spec (.of A)) ∧ (W : Set X).Nonempty ∧
      IsIso (ψ ∣_ W) :=
  exists_chow_open_projective (X ↘ Spec (.of A))

end GlobalTheory.CompanionTheory.GE.ChowOpen
