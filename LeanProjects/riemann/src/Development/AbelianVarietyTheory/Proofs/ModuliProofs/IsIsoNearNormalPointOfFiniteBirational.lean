import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace GlobalTheory.FiniteBirationalNear

theorem exists_common_smul_mem {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (S : Submonoid A) {N : Submodule A M} (hN : N.FG) (N' : Submodule A M)
    (h : ∀ m ∈ N, ∃ s ∈ S, s • m ∈ N') : ∃ s ∈ S, ∀ m ∈ N, s • m ∈ N' := by
  classical
  obtain ⟨T, rfl⟩ := hN
  choose! s hs hs' using h
  refine ⟨∏ t ∈ T, s t, prod_mem fun t ht => hs t (Submodule.subset_span ht), ?_⟩
  have : Submodule.span A (T : Set M) ≤ N'.comap ((∏ t ∈ T, s t) • LinearMap.id) := by
    refine Submodule.span_le.2 fun t ht => ?_
    change (∏ t ∈ T, s t) • t ∈ N'
    rw [← Finset.prod_erase_mul T s ht, mul_smul]
    exact N'.smul_mem _ (hs' t (Submodule.subset_span ht))
  exact fun m hm => this hm

theorem exists_away_isDomain {A O : Type*} [CommRing A] [IsNoetherianRing A] [CommRing O]
    [Algebra A O] (S : Submonoid A) [IsLocalization S O] [IsDomain O] :
    ∃ s ∈ S, ∀ (P : Type) [CommRing P] [Algebra A P] [IsLocalization.Away s P], IsDomain P := by
  obtain ⟨s, hs, h⟩ := exists_common_smul_mem S
    (IsNoetherian.noetherian (RingHom.ker (algebraMap A O))) ⊥ fun m hm => by
      obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff S O m).1 hm
      exact ⟨c, c.2, hc⟩
  refine ⟨s, hs, fun P _ _ _ => ?_⟩
  have hu : IsUnit (algebraMap A O s) := IsLocalization.map_units O ⟨s, hs⟩
  refine Function.Injective.isDomain (IsLocalization.Away.lift (S := P) s hu) ?_
  rw [IsLocalization.Away.lift, IsLocalization.lift_injective_iff]
  intro x y
  constructor
  · intro e
    have := congrArg (IsLocalization.Away.lift (S := P) s hu) e
    simpa using this
  · intro e
    have h1 : x - y ∈ RingHom.ker (algebraMap A O) := by
      rw [RingHom.mem_ker, map_sub, e, sub_self]
    have h2 : s * (x - y) = 0 := h _ h1
    rw [← sub_eq_zero, ← map_sub]
    exact (IsLocalization.map_eq_zero_iff (.powers s) P _).2 ⟨⟨s, Submonoid.mem_powers s⟩, h2⟩

theorem exists_mul_mem_range {A O K B : Type*} [CommRing A] [IsDomain A] [CommRing O]
    [Algebra A O] (S : Submonoid A) [IsLocalization S O] [IsDomain O] [IsIntegrallyClosed O]
    [Field K] [Algebra A K] [IsFractionRing A K] [CommRing B] [Algebra A B] [Module.Finite A B]
    (ψ : B →ₐ[A] K) (hψ : Function.Injective ψ) :
    ∃ r ∈ S, ∀ b : B, ∃ a : A, algebraMap A B a = algebraMap A B r * b := by
  have hu (s : S) : IsUnit (algebraMap A K s) := by
    refine IsUnit.mk0 _ fun h0 => ?_
    have h1 : (s : A) = 0 := IsFractionRing.injective A K (by rw [h0, map_zero])
    have h2 := IsLocalization.map_units O s
    rw [h1, map_zero] at h2
    exact not_isUnit_zero h2
  let : Algebra O K := (IsLocalization.lift (S := O) hu).toAlgebra
  have : IsScalarTower A O K := IsScalarTower.of_algebraMap_eq fun a =>
    (IsLocalization.lift_eq hu a).symm
  have : IsFractionRing O K := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization S O K
  obtain ⟨r, hr, h⟩ := exists_common_smul_mem S (Module.Finite.fg_top (R := A) (M := B))
    (LinearMap.range (Algebra.linearMap A B)) fun b _ => by
      have hb : IsIntegral O (ψ b) := ((Algebra.IsIntegral.isIntegral (R := A) b).map ψ).tower_top
      obtain ⟨o, ho⟩ := IsIntegrallyClosed.isIntegral_iff.mp hb
      obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj S o
      refine ⟨s, s.2, a, hψ ?_⟩
      have e' := congrArg (algebraMap O K) e
      rw [map_mul, ho, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at e'
      rw [Algebra.linearMap_apply, ψ.commutes, map_smul, Algebra.smul_def, mul_comm, e']
  refine ⟨r, hr, fun b => ?_⟩
  obtain ⟨a, ha⟩ := h b trivial
  exact ⟨a, by rw [← Algebra.smul_def]; exact ha⟩

theorem exists_isIntegral_nhds {M : Scheme.{0}} [IsLocallyNoetherian M] (x : M)
    [IsDomain (M.presheaf.stalk x)] : ∃ V : M.Opens, x ∈ V ∧ IsIntegral V := by
  obtain ⟨_, ⟨U, hU : IsAffineOpen U, rfl⟩, hxU, -⟩ :=
    M.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : IsNoetherianRing Γ(M, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  letI := M.presheaf.algebra_section_stalk (U := U) ⟨x, hxU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  obtain ⟨s, hs, h⟩ := exists_away_isDomain (O := M.presheaf.stalk x)
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  have := hU.isLocalization_basicOpen s
  have : IsDomain Γ(M, M.basicOpen s) := h _
  refine ⟨M.basicOpen s, (M.mem_basicOpen s x hxU).2
    (IsLocalization.map_units (M.presheaf.stalk x) ⟨s, hs⟩), ?_⟩
  exact IsIntegral.of_isIso (hU.basicOpen s).isoSpec.inv

theorem exists_isIso_of_isIntegral {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [IsIntegral X]
    [IsIntegral Y] [IsDominant f] [IsIso (f.stalkMap (genericPoint X))] (y : Y)
    [IsIntegrallyClosed (Y.presheaf.stalk y)] : ∃ V : Y.Opens, y ∈ V ∧ IsIso (f ∣_ V) := by
  obtain ⟨_, ⟨U, hU : IsAffineOpen U, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have : Nonempty U := ⟨⟨y, hxU⟩⟩
  letI := (f.app U).hom.toAlgebra
  have : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := f.finite_app U hU
  have hη := apply_genericPoint_of_isDominant f
  have hyU : f (genericPoint X) ∈ U := by
    rw [hη]
    exact ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  letI := Y.presheaf.algebra_section_stalk (U := U) ⟨_, hyU⟩
  have hfr := isFractionRing_stalk_of_eq_genericPoint hU _ hyU hη
  have hgerm (a : Γ(Y, U)) : f.stalkMap (genericPoint X) (Y.presheaf.germ U _ hyU a) =
      X.presheaf.germ (f ⁻¹ᵁ U) (genericPoint X) hyU (f.app U a) :=
    f.germ_stalkMap_apply U _ hyU a
  have hbij : Function.Bijective (f.stalkMap (genericPoint X)) :=
    ConcreteCategory.bijective_of_isIso _
  have hinj : Function.Injective (f.app U) := by
    intro a a' h'
    apply germ_injective_of_isIntegral Y _ hyU
    apply hbij.1
    rw [hgerm, hgerm, h']
  let φ : Γ(X, f ⁻¹ᵁ U) ⟶ Y.presheaf.stalk (f (genericPoint X)) :=
    X.presheaf.germ (f ⁻¹ᵁ U) (genericPoint X) hyU ≫ inv (f.stalkMap (genericPoint X))
  have hφ (c : Γ(X, f ⁻¹ᵁ U)) : f.stalkMap (genericPoint X) (φ c) =
      X.presheaf.germ (f ⁻¹ᵁ U) (genericPoint X) hyU c := by
    rw [← CommRingCat.comp_apply, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  let ψ : Γ(X, f ⁻¹ᵁ U) →ₐ[Γ(Y, U)] Y.presheaf.stalk (f (genericPoint X)) :=
    { φ.hom with
      commutes' := fun a ↦ hbij.1 ((hφ _).trans (hgerm a).symm) }
  have hψ : Function.Injective ψ := fun b b' e => by
    apply germ_injective_of_isIntegral X (genericPoint X) hyU
    rw [← hφ b, ← hφ b']
    exact congr(f.stalkMap (genericPoint X) $e)
  letI : Field (Y.presheaf.stalk (f (genericPoint X))) := IsFractionRing.toField Γ(Y, U)
  letI := Y.presheaf.algebra_section_stalk (U := U) ⟨y, hxU⟩
  have := hU.isLocalization_stalk ⟨y, hxU⟩
  obtain ⟨r, hr, h⟩ := exists_mul_mem_range (O := Y.presheaf.stalk y)
    (hU.primeIdealOf ⟨y, hxU⟩).asIdeal.primeCompl ψ hψ
  refine ⟨Y.basicOpen r, (Y.mem_basicOpen r y hxU).2
    (IsLocalization.map_units (Y.presheaf.stalk y) ⟨r, hr⟩), ?_⟩
  rw [isIso_morphismRestrict_iff_isIso_app _ (hU.basicOpen r),
    hU.app_basicOpen_eq_away_map f (hU.preimage f) r]
  refine IsIso.comp_isIso' ?_ inferInstance
  rw [ConcreteCategory.isIso_iff_bijective]
  have := hU.isLocalization_basicOpen r
  have := (hU.preimage f).isLocalization_basicOpen (f.app U r)
  constructor
  · exact (IsLocalization.Away.map_injective_iff _ _ _).2 fun a ha =>
      ⟨0, by rw [hinj (ha.trans (map_zero _).symm), mul_zero]⟩
  · refine (IsLocalization.Away.map_surjective_iff _ _ _ _).2 fun b => ?_
    obtain ⟨a, ha⟩ := h b
    exact ⟨a, 1, by rw [pow_one]; exact ha⟩

theorem main : ∀ (U M : Scheme.{0}) [IsLocallyNoetherian M] (u : U ⟶ M) (W : M.Opens), IsFinite u → IsReduced U → IsIso (u ∣_ W) → Dense (W : Set M) → Dense ((u ⁻¹ᵁ W : U.Opens) : Set U) → ∀ x : M, IsDomain (M.presheaf.stalk x) → IsIntegrallyClosed (M.presheaf.stalk x) → ∃ V : M.Opens, x ∈ V ∧ IsIso (u ∣_ V) := by
  intro U M _ u W _ _ hW hd hd' x _ _
  obtain ⟨V, hxV, hV⟩ := exists_isIntegral_nhds x
  let f := u ∣_ V
  let W' : V.toScheme.Opens := V.ι ⁻¹ᵁ W
  have : IsFinite f := MorphismProperty.of_isPullback (P := @IsFinite)
    (isPullback_morphismRestrict u V).flip ‹_›
  have hW' : IsIso (f ∣_ W') := by
    have h1 : IsIso (u ∣_ W ∣_ (W.ι ⁻¹ᵁ V)) := inferInstance
    have h2 := ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict u W (W.ι ⁻¹ᵁ V))).1 h1
    have e : W.ι ''ᵁ (W.ι ⁻¹ᵁ V) = V.ι ''ᵁ W' := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.image_preimage_eq_opensRange_inf,
        Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι, inf_comm]
    exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict u V W')).2
      (((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff (morphismRestrictEq u e)).1 h2)
  have hne : Nonempty W' := by
    obtain ⟨z, hz, hz'⟩ := hd.inter_open_nonempty V V.isOpen ⟨x, hxV⟩
    exact ⟨⟨⟨z, hz⟩, hz'⟩⟩
  have : IsIntegral W' := isIntegral_of_isOpenImmersion W'.ι
  have : IsIntegral (f ⁻¹ᵁ W') := IsIntegral.of_isIso (inv (f ∣_ W'))
  have hd₂ : Dense ((f ⁻¹ᵁ W' : (u ⁻¹ᵁ V).toScheme.Opens) : Set (u ⁻¹ᵁ V).toScheme) := by
    have e : f ⁻¹ᵁ W' = (u ⁻¹ᵁ V).ι ⁻¹ᵁ u ⁻¹ᵁ W := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, morphismRestrict_ι]
    rw [e]
    exact hd'.preimage (u ⁻¹ᵁ V).ι.isOpenEmbedding.isOpenMap
  have : IrreducibleSpace (u ⁻¹ᵁ V).toScheme := by
    rw [irreducibleSpace_def, Set.top_eq_univ, ← hd₂.closure_eq]
    refine IsIrreducible.closure ?_
    exact isIrreducible_iff_irreducibleSpace.2 (inferInstanceAs (IrreducibleSpace (f ⁻¹ᵁ W').toScheme))
  have : IsIntegral (u ⁻¹ᵁ V).toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  obtain ⟨_, _⟩ := birational_of_isIso_morphismRestrict f W' hne
  have : IsIntegrallyClosed (V.toScheme.presheaf.stalk (⟨x, hxV⟩ : V)) :=
    IsIntegrallyClosed.of_equiv (R := M.presheaf.stalk x)
      (V.stalkIso ⟨x, hxV⟩).symm.commRingCatIsoToRingEquiv
  obtain ⟨V', hx', hV'⟩ := exists_isIso_of_isIntegral f ⟨x, hxV⟩
  refine ⟨V.ι ''ᵁ V', ⟨⟨x, hxV⟩, hx', rfl⟩, ?_⟩
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict u V V')).1 hV'

end GlobalTheory.FiniteBirationalNear
