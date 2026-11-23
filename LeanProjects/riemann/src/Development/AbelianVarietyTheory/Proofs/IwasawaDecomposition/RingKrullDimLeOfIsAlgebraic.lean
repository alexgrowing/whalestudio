import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIsoMorphismRestrictOfLocalDominantSections
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.AlgStep

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.ModelDom

theorem ringKrullDim_le_of_isAlgebraic (A B : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing B]
    [IsDomain B] [Algebra A B] [FaithfulSMul A B] [Algebra.FiniteType A B] [Algebra.IsAlgebraic A B] :
    ringKrullDim B ≤ ringKrullDim A := by
  classical
  have step : ∀ (R S : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing S] [IsDomain S] (f : R →+* S),
      Function.Injective f → ∀ x : S, Function.Surjective (Polynomial.eval₂RingHom f x) →
      (∃ g : Polynomial R, g ≠ 0 ∧ Polynomial.eval₂ f x g = 0) → ringKrullDim S ≤ ringKrullDim R := by
    intro R S _ _ _ _ _ f hf x hgen halg
    rw [ringKrullDim_le_iff_height_le]
    intro q hq
    have h := ReciprocityTheory.CA.height_le_height_comap_of_eval₂_surjective f hf x hgen halg q
    have h2 : ((q.comap f).height : WithBot ℕ∞) ≤ ringKrullDim R :=
      Ideal.height_le_ringKrullDim_of_ne_top (Ideal.IsPrime.ne_top inferInstance)
    exact (WithBot.coe_le_coe.2 h).trans h2
  have key : ∀ s : Finset B, ringKrullDim (Algebra.adjoin A (s : Set B)) ≤ ringKrullDim A := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine step A _ (algebraMap A _) (FaithfulSMul.algebraMap_injective _ _) 0 ?_
        ⟨Polynomial.X, Polynomial.X_ne_zero, by simp⟩
      rintro ⟨y, hy⟩
      rw [Finset.coe_empty, Algebra.adjoin_empty, Algebra.mem_bot] at hy
      obtain ⟨a, rfl⟩ := hy
      exact ⟨Polynomial.C a, Subtype.ext (by simp)⟩
    | insert x s _ ih =>
      have hle : Algebra.adjoin A (s : Set B) ≤ Algebra.adjoin A ((insert x s : Finset B) : Set B) :=
        Algebra.adjoin_mono (by simp)
      have : Algebra.FiniteType A (Algebra.adjoin A (s : Set B)) :=
        Algebra.FiniteType.adjoin_of_finite s.finite_toSet
      have : IsNoetherianRing (Algebra.adjoin A (s : Set B)) := Algebra.FiniteType.isNoetherianRing A _
      have hx : x ∈ Algebra.adjoin A ((insert x s : Finset B) : Set B) := Algebra.subset_adjoin (by simp)
      refine le_trans (step _ _ (Subalgebra.inclusion hle).toRingHom (Subalgebra.inclusion_injective hle) ⟨x, hx⟩
        ?_ ?_) ih
      · rintro ⟨y, hy⟩
        induction hy using Algebra.adjoin_induction with
        | mem y hy =>
          rw [Finset.coe_insert] at hy
          rcases hy with rfl | hy
          · exact ⟨Polynomial.X, by simp⟩
          · exact ⟨Polynomial.C ⟨y, Algebra.subset_adjoin hy⟩, Subtype.ext (by simp)⟩
        | algebraMap a => exact ⟨Polynomial.C (algebraMap A _ a), Subtype.ext (by simp)⟩
        | add y z _ _ hy hz =>
          obtain ⟨p, hp⟩ := hy
          obtain ⟨q, hq⟩ := hz
          exact ⟨p + q, by rw [map_add, hp, hq]; rfl⟩
        | mul y z _ _ hy hz =>
          obtain ⟨p, hp⟩ := hy
          obtain ⟨q, hq⟩ := hz
          exact ⟨p * q, by rw [map_mul, hp, hq]; rfl⟩
      · obtain ⟨g, hg, h0⟩ := Algebra.IsAlgebraic.isAlgebraic (R := A) x
        refine ⟨g.map (algebraMap A _), (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective _ _)).2 hg, ?_⟩
        apply Subtype.ext
        rw [Polynomial.eval₂_map]
        have := Polynomial.hom_eval₂ g
          ((Subalgebra.inclusion hle).toRingHom.comp (algebraMap A (Algebra.adjoin A (s : Set B))))
          (Algebra.adjoin A ((insert x s : Finset B) : Set B)).val.toRingHom ⟨x, hx⟩
        exact this.trans h0
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := A) (A := B)
  have := key s
  rw [hs] at this
  exact (ringKrullDim_eq_of_ringEquiv Subalgebra.topEquiv.toRingEquiv).ge.trans this

theorem dim_le_of_birational {N M : Scheme.{0}} [IsIntegral N] [IsIntegral M] [IsLocallyNoetherian M] (π : N ⟶ M)
    [LocallyOfFiniteType π] [IsDominant π] [IsIso (π.stalkMap (genericPoint N))] :
    topologicalKrullDim N ≤ topologicalKrullDim M := by
  have hd : ∀ {Z : Scheme.{0}} (U : Z.Opens), IsAffineOpen U →
      topologicalKrullDim (U : Set Z) = ringKrullDim Γ(Z, U) := fun {Z} U hU => by
    rw [topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
    exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(Z, U))
  refine topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_
  obtain ⟨U, hU, hxU, -⟩ := Opens.isBasis_iff_nbhd.1 M.isBasis_affineOpens (Opens.mem_top (π x))
  obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.1 N.isBasis_affineOpens (show x ∈ π ⁻¹ᵁ U from hxU)
  refine ⟨V, V.isOpen, hxV, ?_⟩
  refine le_trans ?_ (topologicalKrullDim_subspace_le M (U : Set M))
  rw [hd U hU, hd V hV]
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  have : Nonempty V := ⟨⟨_, hxV⟩⟩
  have : IsNoetherianRing Γ(M, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  letI := (π.appLE U V hVU).hom.toAlgebra
  have : Algebra.FiniteType Γ(M, U) Γ(N, V) := π.finiteType_appLE hU hV hVU
  have hη := apply_genericPoint_of_isDominant π
  have hηV : genericPoint N ∈ V :=
    ((genericPoint_spec N).mem_open_set_iff V.isOpen).mpr ⟨x, trivial, hxV⟩
  have hyU : π (genericPoint N) ∈ U := hVU hηV
  letI := M.presheaf.algebra_section_stalk (U := U) ⟨_, hyU⟩
  have hfr := isFractionRing_stalk_of_eq_genericPoint hU _ hyU hη
  have hgerm (a : Γ(M, U)) : π.stalkMap (genericPoint N) (M.presheaf.germ U _ hyU a) =
      N.presheaf.germ V (genericPoint N) hηV (π.appLE U V hVU a) := by
    rw [π.germ_stalkMap_apply U _ hyU a, Scheme.Hom.appLE, CommRingCat.comp_apply,
      TopCat.Presheaf.germ_res_apply]
  have hbij : Function.Bijective (π.stalkMap (genericPoint N)) := ConcreteCategory.bijective_of_isIso _
  have hinj : Function.Injective (algebraMap Γ(M, U) Γ(N, V)) := fun a a' h => by
    have h' : π.appLE U V hVU a = π.appLE U V hVU a' := h
    apply germ_injective_of_isIntegral M _ hyU
    apply hbij.1
    rw [hgerm, hgerm, h']
  have : FaithfulSMul Γ(M, U) Γ(N, V) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  let φ : Γ(N, V) ⟶ M.presheaf.stalk (π (genericPoint N)) :=
    N.presheaf.germ V (genericPoint N) hηV ≫ inv (π.stalkMap (genericPoint N))
  have hφ (c : Γ(N, V)) : π.stalkMap (genericPoint N) (φ c) = N.presheaf.germ V (genericPoint N) hηV c := by
    rw [← CommRingCat.comp_apply, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  let ψ : Γ(N, V) →ₐ[Γ(M, U)] M.presheaf.stalk (π (genericPoint N)) :=
    { φ.hom with
      commutes' := fun a ↦ hbij.1 ((hφ _).trans (hgerm a).symm) }
  have hψ : Function.Injective ψ := fun a b h => by
    apply germ_injective_of_isIntegral N _ hηV
    rw [← hφ, ← hφ]
    exact congrArg _ h
  have : Algebra.IsAlgebraic Γ(M, U) (M.presheaf.stalk (π (genericPoint N))) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors Γ(M, U))
  have : Algebra.IsAlgebraic Γ(M, U) Γ(N, V) := Algebra.IsAlgebraic.of_injective ψ hψ
  exact ringKrullDim_le_of_isAlgebraic _ _

theorem exists_isIso_restrict {Y N M : Scheme.{0}} [IsIntegral Y] [IsIntegral N] [IsIntegral M] (jN : Y ⟶ N)
    [IsDominant jN] (π : N ⟶ M) [IsSeparated π] [LocallyOfFiniteType π] (j : Y ⟶ M) [Flat j] [SurjectiveOnStalks j]
    (h : jN ≫ π = j) : ∃ U : M.Opens, (U : Set M).Nonempty ∧ IsIso (π ∣_ U) := by
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks j (genericPoint Y)
  let φ : Spec (M.presheaf.stalk (j (genericPoint Y))) ⟶ N :=
    Spec.map (inv (j.stalkMap (genericPoint Y))) ≫ Y.fromSpecStalk (genericPoint Y) ≫ jN
  have hφ : φ ≫ π = M.fromSpecStalk (j (genericPoint Y)) ≫ 𝟙 M := by
    simp only [φ, Category.assoc, h, Category.comp_id]
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id,
      Category.id_comp]
  obtain ⟨U, hU, g, hg₁, hg₂⟩ := spread_out_of_isGermInjective' (𝟙 M) π φ hφ
  rw [Category.comp_id] at hg₂
  have : IsDominant (Y.fromSpecStalk (genericPoint Y)) :=
    ⟨((dense_iff_closure_eq.2 (genericPoint_spec Y)).mono
      (Set.singleton_subset_iff.2 ⟨_, Scheme.fromSpecStalk_closedPoint⟩))⟩
  have : IsDominant φ := inferInstance
  have : IsDominant g := by
    rw [hg₁] at this
    exact IsDominant.of_comp (U.fromSpecStalkOfMem _ hU) g
  exact ⟨U, ⟨_, hU⟩, GlobalTheory.ZH.isIso_morphismRestrict_of_local_dominant_sections π U fun y hy =>
    ⟨U, U.ι, inferInstance, g, ⟨⟨y, hy⟩, rfl⟩, by simp, ‹_›, hg₂⟩⟩

theorem exists_normal_dominating (F : Type) [Field F] [NumberField F] (Y : Var F) (M M' : TrueGeo.Model Y) :
    ∃ (N : TrueGeo.Model Y) (π : N.X ⟶ M.X) (π' : N.X ⟶ M'.X), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N.X ∧
      π ≫ M.p = N.p ∧ π' ≫ M'.p = N.p ∧ N.j ≫ π = M.j ∧ N.j ≫ π' = M'.j ∧
      (∃ U : M.X.Opens, (U : Set M.X).Nonempty ∧ IsIso (π ∣_ U)) ∧
      ∃ U : M'.X.Opens, (U : Set M'.X).Nonempty ∧ IsIso (π' ∣_ U) := by
  have H₀ := M.pb
  have := M.ar.isIntegral
  have := M'.ar.isIntegral
  have := M.ar.isLocallyNoetherian
  have : IsProper M.p := CommonModel.isProper_of_isProjOver M.ar.isProjOver
  have : IsProper M'.p := CommonModel.isProper_of_isProjOver M'.ar.isProjOver
  let r := pullback.fst M.p M'.p
  let h : Y.X ⟶ pullback M.p M'.p := pullback.lift M.j M'.j (M.pb.w.trans M'.pb.w.symm)
  have hr : h ≫ r = M.j := pullback.lift_fst _ _ _
  have hr' : h ≫ pullback.snd M.p M'.p = M'.j := pullback.lift_snd _ _ _
  have hW : IsProjOver (r ≫ M.p) := GlobalTheory.ProjSpace.isProjOver_pullback M.ar.isProjOver M'.ar.isProjOver
  have w : h ≫ r ≫ M.p = Y.str ≫ spMap (algebraMap (𝓞 F) F) := by rw [← Category.assoc, hr, H₀.w]
  have hb := IsPullback.of_hasPullback (r ≫ M.p) (spMap (algebraMap (𝓞 F) F))
  let f' : Y.X ⟶ pullback (r ≫ M.p) (spMap (algebraMap (𝓞 F) F)) := pullback.lift h Y.str w
  let ρ : pullback (r ≫ M.p) (spMap (algebraMap (𝓞 F) F)) ⟶ Y.X :=
    H₀.lift (pullback.fst _ _ ≫ r) (pullback.snd _ _) (by rw [Category.assoc]; exact hb.w)
  have hρ : ρ ≫ Y.str = pullback.snd _ _ := H₀.lift_snd _ _ _
  have hfρ : f' ≫ ρ = 𝟙 Y.X := by
    apply H₀.hom_ext
    · rw [Category.assoc, H₀.lift_fst, pullback.lift_fst_assoc, hr, Category.id_comp]
    · rw [Category.assoc, hρ, pullback.lift_snd, Category.id_comp]
  have : IsSeparated (ρ ≫ Y.str) := by rw [hρ]; infer_instance
  have : IsSeparated ρ := IsSeparated.of_comp ρ Y.str
  have : IsClosedImmersion (f' ≫ ρ) := by rw [hfρ]; infer_instance
  have : IsClosedImmersion f' := IsClosedImmersion.of_comp f' ρ
  have hh : h = f' ≫ 𝟙 _ ≫ pullback.fst _ _ := by rw [Category.id_comp, pullback.lift_fst]
  have : IsAffineHom (pullback.fst (r ≫ M.p) (spMap (algebraMap (𝓞 F) F))) :=
    MorphismProperty.of_isPullback hb.flip (isAffineHom_of_isAffine _)
  have : IsAffineHom h := by rw [hh]; infer_instance
  have hpb := GlobalTheory.isPullback_toNormalization_of_isLocalization (nonZeroDivisors (𝓞 F)) hb f' (𝟙 _) h hh
  rw [Category.id_comp] at hpb
  have hfin : IsFinite h.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_of_over_fractionRing (o := .of (𝓞 F)) h (r ≫ M.p) F Y.str w
  have : GlobalTheory.IsNormalScheme Y.X := Y.isNormalScheme
  have : GlobalTheory.IsNormalScheme h.normalization := GlobalTheory.IsNormalScheme.normalization_of_isIntegral h
  have hint : IsIntegral h.normalization := inferInstance
  have : Flat (spMap (algebraMap (𝓞 F) F)) := flat_specMap_localization (nonZeroDivisors (𝓞 F)) F
  have : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (R := 𝓞 F) (S := F) (nonZeroDivisors (𝓞 F))
  have : Flat M.j := MorphismProperty.of_isPullback M.pb.flip ‹_›
  have : Flat M'.j := MorphismProperty.of_isPullback M'.pb.flip ‹_›
  have : IsPreimmersion M.j := MorphismProperty.of_isPullback M.pb.flip ‹_›
  have : IsPreimmersion M'.j := MorphismProperty.of_isPullback M'.pb.flip ‹_›
  have e₁ : h.toNormalization ≫ h.fromNormalization ≫ r = M.j := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hr]
  have e₂ : h.toNormalization ≫ h.fromNormalization ≫ pullback.snd M.p M'.p = M'.j := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hr']
  have hU := exists_isIso_restrict h.toNormalization (h.fromNormalization ≫ r) M.j e₁
  have hU' := exists_isIso_restrict h.toNormalization (h.fromNormalization ≫ pullback.snd M.p M'.p) M'.j e₂
  have hdim : topologicalKrullDim h.normalization = (Y.dim + 1 : ℕ) := by
    obtain ⟨U, hne, _⟩ := hU
    obtain ⟨_, _⟩ := birational_of_isIso_morphismRestrict (h.fromNormalization ≫ r) U hne.to_subtype
    have := surjective_of_isDominant_of_isClosed_range (h.fromNormalization ≫ r)
      (h.fromNormalization ≫ r).isClosedMap.isClosed_range
    rw [← M.ar.dim_eq]
    exact (dim_le_of_birational (h.fromNormalization ≫ r)).antisymm
      (PosBaseChange.dim_le_of_isClosedMap (h.fromNormalization ≫ r).isClosedMap
        (h.fromNormalization ≫ r).surjective)
  have hfl : Flat (h.fromNormalization ≫ r ≫ M.p) := GlobalTheory.flat_fromNormalization_comp h F (r ≫ M.p) Y.str w
  have hfZ : Flat (spMap (Int.castRingHom (𝓞 F))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat ℤ (𝓞 F))
  have hpb' := hpb.paste_vert hb
  rw [pullback.lift_snd] at hpb'
  refine ⟨⟨h.normalization, h.fromNormalization ≫ r ≫ M.p,
    ⟨M.ar.isDomain, M.ar.finite, hint, GlobalTheory.isProjOver_comp_of_finite _ _ _ _ _ hfin hW, inferInstance, hdim⟩,
    h.toNormalization, hpb'⟩, h.fromNormalization ≫ r, h.fromNormalization ≫ pullback.snd M.p M'.p,
    GlobalTheory.IsNormalScheme.pred _, Category.assoc _ _ _, ?_, e₁, e₂, hU, hU'⟩
  change (h.fromNormalization ≫ pullback.snd M.p M'.p) ≫ M'.p = h.fromNormalization ≫ r ≫ M.p
  rw [Category.assoc, ← pullback.condition]

end GlobalTheory.ModelDom
