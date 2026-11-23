import Mathlib

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace GlobalTheory

theorem isPullback_equalizer_diagonal {X S T : Scheme.{u}} (f : X ⟶ S) {a b : T ⟶ X}
    (hab : a ≫ f = b ≫ f) :
    IsPullback (equalizer.ι a b ≫ a) (equalizer.ι a b) (pullback.diagonal f)
      (pullback.lift a b hab) := by
  refine ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _ (fun s ↦ equalizer.lift s.snd ?_) ?_ ?_ ?_⟩⟩
  · apply pullback.hom_ext
    · simp [pullback.lift_fst]
    · simpa [pullback.lift_snd] using equalizer.condition a b
  · have h1 := s.condition =≫ pullback.fst _ _
    have h2 := s.condition =≫ pullback.snd _ _
    simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
      pullback.lift_fst, pullback.lift_snd] at h1 h2
    rw [← h1, h2]
  · intro s
    have h1 := s.condition =≫ pullback.fst _ _
    simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id,
      pullback.lift_fst] at h1
    simp [h1]
  · intro s
    simp
  · intro s m _ h
    rw [← cancel_mono (equalizer.ι a b), h]
    simp

theorem isOpenImmersion_equalizer_ι_of_unramified {X S T : Scheme.{u}} (f : X ⟶ S)
    [FormallyUnramified f] [LocallyOfFiniteType f] {a b : T ⟶ X} (hab : a ≫ f = b ≫ f) :
    IsOpenImmersion (equalizer.ι a b) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (isPullback_equalizer_diagonal f hab) inferInstance

theorem isClosedImmersion_equalizer_ι_of_isSeparated {X S T : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] {a b : T ⟶ X} (hab : a ≫ f = b ≫ f) :
    IsClosedImmersion (equalizer.ι a b) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (isPullback_equalizer_diagonal f hab) inferInstance

set_option backward.isDefEq.respectTransparency false in

theorem isOpenImmersion_equalizer_ι_left_of_unramified {S : Scheme.{u}} {T X : Over S}
    [FormallyUnramified X.hom] [LocallyOfFiniteType X.hom] (a b : T ⟶ X) :
    IsOpenImmersion (equalizer.ι a b).left := by
  refine MorphismProperty.of_isPullback
    ((Limits.isPullback_equalizer_prod a b).map (Over.forget _)).flip ?_
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsOpenImmersion _
    (Over.prodLeftIsoPullback X X).hom]
  convert! (inferInstance : IsOpenImmersion (pullback.diagonal X.hom))
  ext1 <;> simp [← Over.comp_left]

theorem range_subset_range_equalizer_ι {X T Z : Scheme.{u}} {a b : T ⟶ X} (j : Z ⟶ T)
    (hj : j ≫ a = j ≫ b) : Set.range j ⊆ Set.range (equalizer.ι a b) := by
  rintro _ ⟨z, rfl⟩
  exact ⟨equalizer.lift j hj z, by rw [← Scheme.Hom.comp_apply, equalizer.lift_ι]⟩

theorem eq_of_range_equalizer_ι_eq_univ {X S T : Scheme.{u}} (f : X ⟶ S)
    [FormallyUnramified f] [LocallyOfFiniteType f] {a b : T ⟶ X} (hab : a ≫ f = b ≫ f)
    (h : Set.range (equalizer.ι a b) = Set.univ) : a = b := by
  have := isOpenImmersion_equalizer_ι_of_unramified f hab
  have : IsIso (equalizer.ι a b) :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _ (Opens.ext h)
  rw [← cancel_epi (equalizer.ι a b), equalizer.condition]

theorem eq_of_surjective_of_unramified {X S T Z : Scheme.{u}} (f : X ⟶ S)
    [FormallyUnramified f] [LocallyOfFiniteType f] {a b : T ⟶ X} (hab : a ≫ f = b ≫ f)
    (j : Z ⟶ T) [Surjective j] (hj : j ≫ a = j ≫ b) : a = b :=
  eq_of_range_equalizer_ι_eq_univ f hab (Set.eq_univ_of_univ_subset
    (j.surjective.range_eq ▸ range_subset_range_equalizer_ι j hj))

theorem eq_of_preconnected_of_unramified {X S T Z : Scheme.{u}} (f : X ⟶ S)
    [FormallyUnramified f] [LocallyOfFiniteType f] [IsSeparated f] [PreconnectedSpace T]
    {a b : T ⟶ X} (hab : a ≫ f = b ≫ f)
    (j : Z ⟶ T) [Nonempty Z] (hj : j ≫ a = j ≫ b) : a = b := by
  have := isOpenImmersion_equalizer_ι_of_unramified f hab
  have := isClosedImmersion_equalizer_ι_of_isSeparated f hab
  refine eq_of_range_equalizer_ι_eq_univ f hab (IsClopen.eq_univ
    ⟨(equalizer.ι a b).isClosedEmbedding.isClosed_range,
      (equalizer.ι a b).isOpenEmbedding.isOpen_range⟩ ?_)
  exact (Set.range_nonempty j).mono (range_subset_range_equalizer_ι j hj)

theorem eq_of_connected_of_unramified_of_point {X S T : Scheme.{u}} (f : X ⟶ S)
    [FormallyUnramified f] [LocallyOfFiniteType f] [IsSeparated f] [ConnectedSpace T]
    {a b : T ⟶ X} (hab : a ≫ f = b ≫ f)
    {k : Type u} [Field k] (j : Spec (.of k) ⟶ T) (hj : j ≫ a = j ≫ b) : a = b :=
  eq_of_preconnected_of_unramified f hab j hj

theorem eq_of_isLocalRing_of_unramified {X S Z : Scheme.{u}} (f : X ⟶ S)
    [FormallyUnramified f] [LocallyOfFiniteType f] {R : CommRingCat.{u}} [IsLocalRing R]
    {a b : Spec R ⟶ X} (hab : a ≫ f = b ≫ f)
    (j : Z ⟶ Spec R) (hz : IsLocalRing.closedPoint R ∈ Set.range j) (hj : j ≫ a = j ≫ b) :
    a = b := by
  have := isOpenImmersion_equalizer_ι_of_unramified f hab
  refine eq_of_range_equalizer_ι_eq_univ f hab ?_
  have h := (IsLocalRing.closed_point_mem_iff (R := R)
    (U := (equalizer.ι a b).opensRange)).mp (range_subset_range_equalizer_ι j hj hz)
  exact congr(SetLike.coe $h)

theorem isOpenImmersion_of_section_of_unramified {X S : Scheme.{u}} (f : X ⟶ S)
    [FormallyUnramified f] [LocallyOfFiniteType f] (s : S ⟶ X) (hs : s ≫ f = 𝟙 S) :
    IsOpenImmersion s := by
  have hab : (𝟙 X) ≫ f = (f ≫ s) ≫ f := by simp [hs]
  have := isOpenImmersion_equalizer_ι_of_unramified f hab
  have h1 : s ≫ 𝟙 X = s ≫ f ≫ s := by simp [reassoc_of% hs]
  have h2 := equalizer.condition (𝟙 X) (f ≫ s)
  have : IsIso (equalizer.lift s h1) := ⟨equalizer.ι _ _ ≫ f, by simp [hs], by
    rw [← cancel_mono (equalizer.ι _ _)]
    simpa using h2.symm⟩
  rw [← equalizer.lift_ι s h1]
  infer_instance

theorem isClosedImmersion_of_section_of_isSeparated {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] (s : S ⟶ X) (hs : s ≫ f = 𝟙 S) : IsClosedImmersion s :=
  have : IsClosedImmersion (s ≫ f) := hs ▸ inferInstance
  .of_comp s f

theorem isOpenImmersion_and_isClosedImmersion_of_section_of_etale {X S : Scheme.{u}} (f : X ⟶ S)
    [Etale f] [IsSeparated f] (s : S ⟶ X) (hs : s ≫ f = 𝟙 S) :
    IsOpenImmersion s ∧ IsClosedImmersion s :=
  ⟨isOpenImmersion_of_section_of_unramified f s hs,
    isClosedImmersion_of_section_of_isSeparated f s hs⟩

theorem surjective_of_isNilpotent_ker {T₀ T : Scheme.{u}} (i : T₀ ⟶ T) [IsClosedImmersion i]
    (hi : IsNilpotent i.ker) : Surjective i := by
  have : IsDominant i := by
    obtain ⟨n, hn⟩ := hi
    rw [isDominant_iff, denseRange_iff_closure_range, ← i.support_ker,
      ← i.ker.support_pow (n + 1) (by simp), pow_succ, hn]
    simp
  exact surjective_of_isDominant_of_isClosed_range _ i.isClosedEmbedding.isClosed_range

set_option backward.isDefEq.respectTransparency false in

theorem exists_local_lift_of_smooth {X S T₀ T : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    (i : T₀ ⟶ T) [IsClosedImmersion i] (hi : IsNilpotent i.ker)
    (g : T₀ ⟶ X) (h : T ⟶ S) (w : g ≫ f = i ≫ h) (t : T) :
    ∃ (W : T.Opens) (_ : t ∈ W) (l : W.toScheme ⟶ X), l ≫ f = W.ι ≫ h ∧
      (i ∣_ W) ≫ l = (i ⁻¹ᵁ W).ι ≫ g := by
  obtain ⟨t, rfl⟩ := (surjective_of_isNilpotent_ker i hi).surj t
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f (g t))) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU : V ≤ f ⁻¹ᵁ U⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).isOpen
  obtain ⟨O, hO, hO'⟩ := i.isClosedEmbedding.isInducing.isOpen_iff.mp (g ⁻¹ᵁ V).isOpen
  have htO : i t ∈ O := by
    have : t ∈ i ⁻¹' O := hO' ▸ hxV
    exact this
  have hth : h (i t) ∈ U := by
    rw [← Scheme.Hom.comp_apply, ← w, Scheme.Hom.comp_apply]; exact hxU
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWO⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open
    (show i t ∈ O ∩ (h ⁻¹ᵁ U : Set T) from ⟨htO, hth⟩) (hO.inter (h ⁻¹ᵁ U).isOpen)
  have hWU : W ≤ h ⁻¹ᵁ U := fun x hx ↦ (hWO hx).2
  have hWV : i ⁻¹ᵁ W ≤ g ⁻¹ᵁ V := fun x hx ↦ by
    have : x ∈ i ⁻¹' O := (hWO hx).1
    rwa [hO'] at this
  have hsm := f.smooth_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom, (h.appLE U W hWU).hom,
    ((h.appLE U W hWU) ≫ i.app W).hom]
  let ψ₀ : Γ(X, V) →ₐ[Γ(S, U)] Γ(T₀, i ⁻¹ᵁ W) := ⟨(g.appLE _ _ hWV).hom, fun r ↦ by
    simp [RingHom.algebraMap_toAlgebra, ← CategoryTheory.comp_apply, -CommRingCat.hom_comp,
      Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, w, -Scheme.Hom.comp_appLE]⟩
  let π : Γ(T, W) →ₐ[Γ(S, U)] Γ(T₀, i ⁻¹ᵁ W) := ⟨(i.app W).hom, fun r ↦ rfl⟩
  have hπ : Function.Surjective π := i.app_surjective W hW
  have hπ' : IsNilpotent (RingHom.ker (π : Γ(T, W) →+* Γ(T₀, i ⁻¹ᵁ W))) := by
    obtain ⟨n, hn⟩ := hi
    exact ⟨n, by simpa using! congr(($hn).ideal ⟨W, hW⟩)⟩
  let ψ := Algebra.FormallySmooth.liftOfSurjective ψ₀ π hπ hπ'
  have hψ : π.comp ψ = ψ₀ := Algebra.FormallySmooth.comp_liftOfSurjective ψ₀ π hπ hπ'
  have e₁ : f.appLE U V hVU ≫ CommRingCat.ofHom ψ.toRingHom = h.appLE U W hWU :=
    CommRingCat.hom_ext ψ.comp_algebraMap
  have e₂ : CommRingCat.ofHom ψ.toRingHom ≫ i.app W = g.appLE _ _ hWV :=
    CommRingCat.hom_ext congr(($hψ).toRingHom)
  refine ⟨W, hxW, Scheme.Opens.toSpecΓ W ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hV.fromSpec, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, ← hU.SpecMap_appLE_fromSpec f hV hVU,
      ← Spec.map_comp_assoc, e₁, hU.SpecMap_appLE_fromSpec h hW hWU, hW.toSpecΓ_fromSpec_assoc]
  · rw [← Scheme.Opens.toSpecΓ_naturality_assoc, ← Spec.map_comp_assoc, e₂,
      hV.SpecMap_appLE_fromSpec g (hW.preimage i) hWV, IsAffineOpen.toSpecΓ_fromSpec_assoc]

theorem existsUnique_lift_of_etale {X S T₀ T : Scheme.{u}} (f : X ⟶ S) [Etale f]
    (i : T₀ ⟶ T) [IsClosedImmersion i] (hi : IsNilpotent i.ker)
    (g : T₀ ⟶ X) (h : T ⟶ S) (w : g ≫ f = i ≫ h) :
    ∃! l : T ⟶ X, i ≫ l = g ∧ l ≫ f = h := by
  have := surjective_of_isNilpotent_ker i hi
  refine existsUnique_of_exists_of_unique ?_ fun l₁ l₂ h₁ h₂ ↦
    eq_of_surjective_of_unramified f (h₁.2.trans h₂.2.symm) i (h₁.1.trans h₂.1.symm)
  choose W hW l hl hl' using exists_local_lift_of_smooth f i hi g h w
  have key : ∀ (t : T) {Z : Scheme.{u}} (a : Z ⟶ W t) (b : Z ⟶ T₀), a ≫ (W t).ι = b ≫ i →
      a ≫ l t = b ≫ g := fun t Z a b e ↦ by
    obtain ⟨c, hc₁, hc₂⟩ := (isPullback_morphismRestrict i (W t)).exists_lift a b e
    rw [← hc₁, ← hc₂, Category.assoc, hl', Category.assoc]
  have hcov : IsOpenCover W := by
    rw [IsOpenCover, eq_top_iff]
    exact fun t _ ↦ Opens.mem_iSup.mpr ⟨t, hW t⟩
  let 𝒰 := T.openCoverOfIsOpenCover W hcov
  have hcomp : ∀ s t : T, pullback.fst (W s).ι (W t).ι ≫ l s = pullback.snd _ _ ≫ l t := by
    intro s t
    refine eq_of_surjective_of_unramified f ?_
      (pullback.fst (pullback.fst (W s).ι (W t).ι ≫ (W s).ι) i) ?_
    · simp [hl, pullback.condition_assoc]
    · rw [← Category.assoc, ← Category.assoc, key s _ (pullback.snd _ _),
        key t _ (pullback.snd _ _)]
      · rw [Category.assoc, ← pullback.condition (f := (W s).ι)]
        exact pullback.condition
      · rw [Category.assoc]
        exact pullback.condition
  have hL : ∀ t : T, (W t).ι ≫ 𝒰.glueMorphisms l hcomp = l t :=
    fun t ↦ 𝒰.ι_glueMorphisms l hcomp t
  refine ⟨𝒰.glueMorphisms l hcomp, ?_, ?_⟩
  · refine Scheme.hom_ext_of_forall _ _ fun x ↦ ⟨i ⁻¹ᵁ W (i x), hW _, ?_⟩
    rw [← morphismRestrict_ι_assoc, hL, hl']
  · refine Scheme.hom_ext_of_forall _ _ fun x ↦ ⟨W x, hW _, ?_⟩
    rw [reassoc_of% hL, hl]

theorem over_eq_of_preconnected_of_unramified {S Z : Scheme.{u}} {T X : Over S}
    [FormallyUnramified X.hom] [LocallyOfFiniteType X.hom] [IsSeparated X.hom]
    [PreconnectedSpace T.left] {a b : T ⟶ X}
    (j : Z ⟶ T.left) [Nonempty Z] (hj : j ≫ a.left = j ≫ b.left) : a = b :=
  Over.OverMorphism.ext
    (eq_of_preconnected_of_unramified X.hom ((Over.w a).trans (Over.w b).symm) j hj)

theorem isNilpotent_ker_specMap {R R₀ : CommRingCat.{u}} (π : R ⟶ R₀)
    (hπ : IsNilpotent (RingHom.ker π.hom)) : IsNilpotent (Spec.map π).ker := by
  obtain ⟨n, hn⟩ := hπ
  refine ⟨n, Scheme.IdealSheafData.ext_of_isAffine ?_⟩
  have e : RingHom.ker (Spec.map π).appTop.hom =
      (RingHom.ker π.hom).map (Scheme.ΓSpecIso R).inv.hom := by
    have h₁ : (Spec.map π).appTop = (Scheme.ΓSpecIso R).hom ≫ π ≫ (Scheme.ΓSpecIso R₀).inv := by
      simp [← Scheme.ΓSpecIso_naturality_assoc]
    rw [h₁]
    have := Ideal.map_symm (I := RingHom.ker π.hom) (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
    refine Eq.trans ?_ this.symm
    ext x
    simp only [RingHom.mem_ker, CommRingCat.hom_comp, RingHom.comp_apply, Ideal.mem_comap]
    exact map_eq_zero_iff _ (Scheme.ΓSpecIso R₀).symm.commRingCatIsoToRingEquiv.injective
  have e' : (Spec.map π).ker.ideal ⟨⊤, isAffineOpen_top _⟩ =
      (RingHom.ker π.hom).map (Scheme.ΓSpecIso R).inv.hom := by
    rw [← e, Scheme.Hom.ker_apply]; rfl
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, e', ← Ideal.map_pow, hn]
  simp

theorem existsUnique_lift_of_etale_of_surjective {X S : Scheme.{u}} (f : X ⟶ S) [Etale f]
    {R R₀ : CommRingCat.{u}} (π : R ⟶ R₀) (hπ : Function.Surjective π)
    (hπ' : IsNilpotent (RingHom.ker π.hom))
    (g : Spec R₀ ⟶ X) (h : Spec R ⟶ S) (w : g ≫ f = Spec.map π ≫ h) :
    ∃! l : Spec R ⟶ X, Spec.map π ≫ l = g ∧ l ≫ f = h :=
  have := IsClosedImmersion.spec_of_surjective π hπ
  existsUnique_lift_of_etale f _ (isNilpotent_ker_specMap π hπ') g h w

open Polynomial in

theorem exists_algHom_lift_of_henselian {B A : Type*} {R K : Type u} [CommRing B] [CommRing A]
    [CommRing R] [Field K] [Algebra B A] [Algebra B R] [Algebra B K] [Algebra.Etale B A]
    [HenselianLocalRing R] (π : R →ₐ[B] K) (hπ : Function.Surjective π) (φ : A →ₐ[B] K) :
    ∃ ψ : A →ₐ[B] R, π.comp ψ = φ := by
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨r, hr, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := B) (RingHom.ker φ)
  obtain ⟨P⟩ := hstd.nonempty_standardEtalePresentation
  let φ' : Localization.Away r →ₐ[B] K :=
    IsLocalization.Away.liftAlgHom r (f := φ) (Ne.isUnit hr)
  have hφ' : φ'.comp (IsScalarTower.toAlgHom B A _) = φ := by
    ext a; simp [φ']
  have hx : P.HasMap (φ' P.x) := P.hasMap.map φ'
  have hc : (π : R →+* K).comp (algebraMap B R) = algebraMap B K := π.comp_algebraMap
  have H := ((HenselianLocalRing.TFAE R).out 0 2).mp ‹HenselianLocalRing R›
  obtain ⟨a, ha, ha'⟩ := H (π : R →+* K) hπ (P.f.map (algebraMap B R)) (P.monic_f.map _) (φ' P.x)
    (by rw [eval₂_map, hc]; exact hx.1)
    (by rw [derivative_map, eval₂_map, hc]; exact hx.isUnit_derivative_f.ne_zero)
  replace ha' : π a = φ' P.x := ha'
  have hloc : IsLocalHom (π : R →+* K) := .of_surjective _ hπ
  have hA : P.HasMap a := by
    refine ⟨by rwa [aeval_def, ← Polynomial.eval_map], ?_⟩
    refine IsUnit.of_map (π : R →+* K) _ ?_
    rw [RingHom.coe_coe, ← aeval_algHom_apply, ha']
    exact hx.2
  refine ⟨((P.lift a hA).comp P.equivRing.toAlgHom).comp (IsScalarTower.toAlgHom B A _), ?_⟩
  rw [← hφ', ← AlgHom.comp_assoc]
  congr 1
  exact P.hom_ext (by simp [ha'])

theorem exists_specMap_fromSpec_eq {X : Scheme.{u}} {R : CommRingCat.{u}} (g : Spec R ⟶ X)
    {V : X.Opens} (hV : IsAffineOpen V) (hg : Set.range g ⊆ V) :
    ∃ φ : Γ(X, V) ⟶ R, Spec.map φ ≫ hV.fromSpec = g := by
  have hg' : Set.range g ⊆ Set.range hV.fromSpec := by rwa [hV.range_fromSpec]
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift hV.fromSpec g hg')
  exact ⟨φ, by rw [hφ, IsOpenImmersion.lift_fac]⟩

theorem existsUnique_lift_of_etale_of_henselian {X S : Scheme.{u}} (f : X ⟶ S) [Etale f]
    {R K : Type u} [CommRing R] [HenselianLocalRing R] [Field K] (π : R →+* K)
    (hπ : Function.Surjective π) (g : Spec (.of K) ⟶ X) (h : Spec (.of R) ⟶ S)
    (w : g ≫ f = Spec.map (CommRingCat.ofHom π) ≫ h) :
    ∃! l : Spec (.of R) ⟶ X, Spec.map (CommRingCat.ofHom π) ≫ l = g ∧ l ≫ f = h := by
  have hloc : IsLocalHom π := .of_surjective _ hπ
  have hcl : Spec.map (CommRingCat.ofHom π) (IsLocalRing.closedPoint K) =
      IsLocalRing.closedPoint R := IsLocalRing.comap_closedPoint π
  refine existsUnique_of_exists_of_unique ?_ fun l₁ l₂ h₁ h₂ ↦
    eq_of_isLocalRing_of_unramified f (h₁.2.trans h₂.2.symm) _ ⟨_, hcl⟩ (h₁.1.trans h₂.1.symm)
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (f (g (IsLocalRing.closedPoint K)))) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU : V ≤ f ⁻¹ᵁ U⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).isOpen
  replace hU : IsAffineOpen U := hU
  replace hV : IsAffineOpen V := hV
  have hgV : g ⁻¹ᵁ V = ⊤ := (IsLocalRing.closed_point_mem_iff (R := K)).mp hxV
  have hhU : h ⁻¹ᵁ U = ⊤ := (IsLocalRing.closed_point_mem_iff (R := R)).mp (by
    have : h (Spec.map (CommRingCat.ofHom π) (IsLocalRing.closedPoint K)) ∈ U := by
      have e : f (g (IsLocalRing.closedPoint K)) =
          h (Spec.map (CommRingCat.ofHom π) (IsLocalRing.closedPoint K)) :=
        congr($w (IsLocalRing.closedPoint K))
      exact e ▸ hxU
    rw [hcl] at this
    exact this)
  obtain ⟨φ, rfl⟩ := exists_specMap_fromSpec_eq g hV (by
    rintro _ ⟨x, rfl⟩; exact (hgV.ge (Set.mem_univ x) :))
  obtain ⟨α, rfl⟩ := exists_specMap_fromSpec_eq h hU (by
    rintro _ ⟨x, rfl⟩; exact (hhU.ge (Set.mem_univ x) :))
  rw [Category.assoc, ← hU.SpecMap_appLE_fromSpec f hV hVU, ← Spec.map_comp_assoc,
    ← Spec.map_comp_assoc, cancel_mono, Spec.map_inj] at w
  have het := f.etale_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom]
  letI : Algebra Γ(S, U) R := α.hom.toAlgebra
  letI : Algebra Γ(S, U) K := (π.comp α.hom).toAlgebra
  obtain ⟨ψ, hψ⟩ := exists_algHom_lift_of_henselian (B := Γ(S, U)) (A := Γ(X, V))
    ⟨π, fun _ ↦ rfl⟩ hπ ⟨φ.hom, fun r ↦ congr($w r)⟩
  have e₁ : f.appLE U V hVU ≫ CommRingCat.ofHom ψ.toRingHom = α :=
    CommRingCat.hom_ext ψ.comp_algebraMap
  have e₂ : CommRingCat.ofHom ψ.toRingHom ≫ CommRingCat.ofHom π = φ :=
    CommRingCat.hom_ext congr(($hψ).toRingHom)
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hV.fromSpec, ?_, ?_⟩
  · rw [← Spec.map_comp_assoc, e₂]
  · rw [Category.assoc, ← hU.SpecMap_appLE_fromSpec f hV hVU, ← Spec.map_comp_assoc, e₁]

def restrictPoints {X S T₀ T : Scheme.{u}} (f : X ⟶ S) (h : T ⟶ S) (i : T₀ ⟶ T) :
    {l : T ⟶ X // l ≫ f = h} → {g : T₀ ⟶ X // g ≫ f = i ≫ h} :=
  fun l ↦ ⟨i ≫ l.1, by rw [Category.assoc, l.2]⟩

@[simp]
theorem restrictPoints_val {X S T₀ T : Scheme.{u}} (f : X ⟶ S) (h : T ⟶ S) (i : T₀ ⟶ T)
    (l : {l : T ⟶ X // l ≫ f = h}) : (restrictPoints f h i l).1 = i ≫ l.1 := rfl

theorem bijective_restrictPoints_of_existsUnique {X S T₀ T : Scheme.{u}} (f : X ⟶ S) (h : T ⟶ S)
    (i : T₀ ⟶ T)
    (H : ∀ g : T₀ ⟶ X, g ≫ f = i ≫ h → ∃! l : T ⟶ X, i ≫ l = g ∧ l ≫ f = h) :
    Function.Bijective (restrictPoints f h i) := by
  rw [Function.bijective_iff_existsUnique]
  rintro ⟨g, hg⟩
  obtain ⟨l, ⟨h₁, h₂⟩, h₃⟩ := H g hg
  exact ⟨⟨l, h₂⟩, Subtype.ext h₁, fun y hy ↦ Subtype.ext (h₃ _ ⟨congr(($hy).1), y.2⟩)⟩

theorem bijective_restrictPoints_of_etale {X S T₀ T : Scheme.{u}} (f : X ⟶ S) [Etale f]
    (h : T ⟶ S) (i : T₀ ⟶ T) [IsClosedImmersion i] (hi : IsNilpotent i.ker) :
    Function.Bijective (restrictPoints f h i) :=
  bijective_restrictPoints_of_existsUnique f h i fun g w ↦ existsUnique_lift_of_etale f i hi g h w

theorem bijective_restrictPoints_of_etale_of_henselian {X S : Scheme.{u}} (f : X ⟶ S) [Etale f]
    (R : Type u) [CommRing R] [HenselianLocalRing R] (h : Spec (.of R) ⟶ S) :
    Function.Bijective (restrictPoints f h
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) :=
  bijective_restrictPoints_of_existsUnique f h _ fun g w ↦
    existsUnique_lift_of_etale_of_henselian f _ IsLocalRing.residue_surjective g h w

theorem unramified_etale_sections :
    (∀ {X S T : Scheme.{u}} (f : X ⟶ S) [FormallyUnramified f] [LocallyOfFiniteType f]
      [IsSeparated f] (a b : T ⟶ X), a ≫ f = b ≫ f →
        IsOpenImmersion (equalizer.ι a b) ∧ IsClosedImmersion (equalizer.ι a b)) ∧
    (∀ {X S T : Scheme.{u}} (f : X ⟶ S) [FormallyUnramified f] [LocallyOfFiniteType f]
      [IsSeparated f] [ConnectedSpace T] (a b : T ⟶ X), a ≫ f = b ≫ f →
        ∀ (k : Type u) [Field k] (j : Spec (.of k) ⟶ T), j ≫ a = j ≫ b → a = b) ∧
    (∀ {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] [IsSeparated f] (s : S ⟶ X), s ≫ f = 𝟙 S →
        IsOpenImmersion s ∧ IsClosedImmersion s) ∧
    (∀ {X S T₀ T : Scheme.{u}} (f : X ⟶ S) [Etale f] (i : T₀ ⟶ T) [IsClosedImmersion i],
      IsNilpotent i.ker → ∀ (g : T₀ ⟶ X) (h : T ⟶ S), g ≫ f = i ≫ h →
        ∃! l : T ⟶ X, i ≫ l = g ∧ l ≫ f = h) ∧
    (∀ (R : Type u) [CommRing R] [HenselianLocalRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
      [Etale f], Function.Bijective (restrictPoints f (𝟙 _)
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))) :=
  ⟨fun f _ _ _ _ _ hab ↦ ⟨isOpenImmersion_equalizer_ι_of_unramified f hab,
      isClosedImmersion_equalizer_ι_of_isSeparated f hab⟩,
    fun f _ _ _ _ _ _ hab _ _ j hj ↦ eq_of_connected_of_unramified_of_point f hab j hj,
    fun f _ _ s hs ↦ isOpenImmersion_and_isClosedImmersion_of_section_of_etale f s hs,
    fun f _ i _ hi g h w ↦ existsUnique_lift_of_etale f i hi g h w,
    fun R _ _ _ f _ ↦ bijective_restrictPoints_of_etale_of_henselian f R _⟩

end GlobalTheory
