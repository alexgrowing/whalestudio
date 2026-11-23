import Mathlib

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace GlobalTheory.Retract

section Algebra

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  (s : A →ₐ[R] B) (p : B →ₐ[R] A) (h : p.comp s = AlgHom.id R A)

include h

theorem algHom_surjective : Function.Surjective p :=
  fun a ↦ ⟨s a, congr($h a)⟩

theorem flat_algebra [Module.Flat R B] : Module.Flat R A :=
  Module.Flat.of_retract s.toLinearMap p.toLinearMap (LinearMap.ext fun a ↦ congr($h a))

theorem finite_algebra [Module.Finite R B] : Module.Finite R A :=
  Module.Finite.of_surjective p.toLinearMap (algHom_surjective s p h)

theorem finiteType_algebra [Algebra.FiniteType R B] : Algebra.FiniteType R A :=
  Algebra.FiniteType.of_surjective p (algHom_surjective s p h)

theorem fg_ker [Algebra.FiniteType R B] : (RingHom.ker p.toRingHom).FG := by
  classical
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (R := R) (A := B)
  refine ⟨t.image fun b ↦ b - s (p b), le_antisymm ?_ ?_⟩
  · rw [Ideal.span_le]
    intro x hx
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hx
    have : p (s (p b)) = p b := congr($h (p b))
    simp [RingHom.mem_ker, this]
  · set I : Ideal B := Ideal.span (↑(t.image fun b ↦ b - s (p b)) : Set B)
    have key : Ideal.Quotient.mkₐ R I = (Ideal.Quotient.mkₐ R I).comp (s.comp p) := by
      refine AlgHom.ext_of_adjoin_eq_top ht fun b hb ↦ ?_
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
      rw [Ideal.Quotient.eq]
      exact Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hb))
    intro b hb
    have hb' : p b = 0 := hb
    have := congr($key b)
    simp only [AlgHom.comp_apply, hb', map_zero, Ideal.Quotient.mkₐ_eq_mk] at this
    exact Ideal.Quotient.eq_zero_iff_mem.mp this

theorem finitePresentation_algebra [Algebra.FinitePresentation R B] :
    Algebra.FinitePresentation R A :=
  Algebra.FinitePresentation.of_surjective (algHom_surjective s p h) (fg_ker s p h)

theorem formallySmooth_algebra [Algebra.FormallySmooth R B] : Algebra.FormallySmooth R A := by
  refine Algebra.FormallySmooth.of_split p
    ((Ideal.Quotient.mkₐ R (RingHom.ker p.toRingHom ^ 2)).comp s) ?_
  ext a
  exact congr($h a)

theorem formallyUnramified_algebra [Algebra.FormallyUnramified R B] :
    Algebra.FormallyUnramified R A :=
  Algebra.FormallyUnramified.of_surjective p (algHom_surjective s p h)

theorem formallyEtale_algebra [Algebra.FormallyEtale R B] : Algebra.FormallyEtale R A :=
  Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr
    ⟨formallyUnramified_algebra s p h, formallySmooth_algebra s p h⟩

theorem smooth_algebra [Algebra.Smooth R B] : Algebra.Smooth R A :=
  ⟨formallySmooth_algebra s p h, finitePresentation_algebra s p h⟩

theorem etale_algebra [Algebra.Etale R B] : Algebra.Etale R A :=
  ⟨formallyEtale_algebra s p h, finitePresentation_algebra s p h⟩

theorem quasiFinite_algebra [Algebra.QuasiFinite R B] : Algebra.QuasiFinite R A :=
  Algebra.QuasiFinite.of_surjective_algHom p (algHom_surjective s p h)

end Algebra

section Local

variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {i : X ⟶ Y} {r : Y ⟶ X}

theorem section_comp (hir : i ≫ r = 𝟙 X) (hr : r ≫ f = g) : i ≫ g = f := by
  rw [← hr, reassoc_of% hir]

theorem apply_apply (hir : i ≫ r = 𝟙 X) (x : X) : r (i x) = x := by
  rw [← Scheme.Hom.comp_apply, hir]; rfl

theorem exists_affine_le (hir : i ≫ r = 𝟙 X) (x : X) (O : X.Opens) (hx : x ∈ O) :
    ∃ (U : X.Opens) (V : Y.Opens), IsAffineOpen U ∧ IsAffineOpen V ∧ x ∈ U ∧ U ≤ O ∧
      U ≤ i ⁻¹ᵁ V ∧ V ≤ r ⁻¹ᵁ U := by
  obtain ⟨U₀, hU₀, hxU₀, hU₀O⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
  have hix : i x ∈ r ⁻¹ᵁ U₀ := by
    change r (i x) ∈ U₀
    rwa [apply_apply hir]
  obtain ⟨V₀, hV₀, hxV₀, hV₀U₀⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens hix
  obtain ⟨a, ha, hxa⟩ := IsAffineOpen.exists_basicOpen_le hU₀ (V := i ⁻¹ᵁ V₀) ⟨x, hxV₀⟩ hxU₀
  have hV : Y.basicOpen (r.appLE U₀ V₀ hV₀U₀ a) = V₀ ⊓ r ⁻¹ᵁ X.basicOpen a := by
    simp [Scheme.Hom.appLE, ← Scheme.preimage_basicOpen]
  refine ⟨X.basicOpen a, Y.basicOpen (r.appLE U₀ V₀ hV₀U₀ a), IsAffineOpen.basicOpen hU₀ a,
    IsAffineOpen.basicOpen hV₀ _, hxa, (X.basicOpen_le a).trans hU₀O, ?_, ?_⟩
  · rw [hV]
    intro z hz
    refine ⟨ha hz, ?_⟩
    change r (i z) ∈ X.basicOpen a
    rwa [apply_apply hir]
  · rw [hV]
    exact inf_le_right

theorem exists_affine (hir : i ≫ r = 𝟙 X) (hr : r ≫ f = g) (x : X) :
    ∃ (U : X.Opens) (V : Y.Opens) (W : S.Opens),
      IsAffineOpen U ∧ IsAffineOpen V ∧ IsAffineOpen W ∧ x ∈ U ∧
      U ≤ i ⁻¹ᵁ V ∧ V ≤ r ⁻¹ᵁ U ∧ U ≤ f ⁻¹ᵁ W ∧ V ≤ g ⁻¹ᵁ W := by
  obtain ⟨W, hW, hxW, -⟩ := Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens (Opens.mem_top (f x))
  obtain ⟨U, V, hU, hV, hxU, hUW, hUV, hVU⟩ := exists_affine_le hir x (f ⁻¹ᵁ W) hxW
  refine ⟨U, V, W, hU, hV, hW, hxU, hUV, hVU, hUW, ?_⟩
  subst hr
  intro y hy
  exact hUW (hVU hy)

theorem appLE_comp_appLE (hir : i ≫ r = 𝟙 X) {U : X.Opens} {V : Y.Opens}
    (hUV : U ≤ i ⁻¹ᵁ V) (hVU : V ≤ r ⁻¹ᵁ U) :
    r.appLE U V hVU ≫ i.appLE V U hUV = 𝟙 Γ(X, U) := by
  rw [Scheme.Hom.appLE_comp_appLE]
  generalize_proofs e
  revert e
  rw [hir]
  intro e
  exact (Category.id_comp _).trans (X.presheaf.map_id _)

theorem base_appLE_comp_retraction (hr : r ≫ f = g) {U : X.Opens} {V : Y.Opens} {W : S.Opens}
    (hVU : V ≤ r ⁻¹ᵁ U) (hUW : U ≤ f ⁻¹ᵁ W) (hVW : V ≤ g ⁻¹ᵁ W) :
    f.appLE W U hUW ≫ r.appLE U V hVU = g.appLE W V hVW := by
  subst hr
  rw [Scheme.Hom.appLE_comp_appLE]

theorem base_appLE_comp_section (hi : i ≫ g = f) {U : X.Opens} {V : Y.Opens} {W : S.Opens}
    (hUV : U ≤ i ⁻¹ᵁ V) (hUW : U ≤ f ⁻¹ᵁ W) (hVW : V ≤ g ⁻¹ᵁ W) :
    g.appLE W V hVW ≫ i.appLE V U hUV = f.appLE W U hUW := by
  subst hi
  rw [Scheme.Hom.appLE_comp_appLE]

theorem exists_algHom_retract (hir : i ≫ r = 𝟙 X) (hr : r ≫ f = g)
    {U : X.Opens} {V : Y.Opens} {W : S.Opens}
    (hUV : U ≤ i ⁻¹ᵁ V) (hVU : V ≤ r ⁻¹ᵁ U) (hUW : U ≤ f ⁻¹ᵁ W) (hVW : V ≤ g ⁻¹ᵁ W) :
    letI := (f.appLE W U hUW).hom.toAlgebra
    letI := (g.appLE W V hVW).hom.toAlgebra
    ∃ (s : Γ(X, U) →ₐ[Γ(S, W)] Γ(Y, V)) (p : Γ(Y, V) →ₐ[Γ(S, W)] Γ(X, U)),
      s.toRingHom = (r.appLE U V hVU).hom ∧ p.toRingHom = (i.appLE V U hUV).hom ∧
        p.comp s = AlgHom.id _ _ := by
  letI := (f.appLE W U hUW).hom.toAlgebra
  letI := (g.appLE W V hVW).hom.toAlgebra
  refine ⟨⟨(r.appLE U V hVU).hom, fun a ↦ ?_⟩, ⟨(i.appLE V U hUV).hom, fun a ↦ ?_⟩, rfl, rfl, ?_⟩
  · exact congr($(base_appLE_comp_retraction hr hVU hUW hVW).hom a)
  · exact congr($(base_appLE_comp_section (section_comp hir hr) hUV hUW hVW).hom a)
  · ext a
    exact congr($(appLE_comp_appLE hir hUV hVU).hom a)

theorem exists_baseChange (hir : i ≫ r = 𝟙 X) (hr : r ≫ f = g) {T X' Y' : Scheme.{u}} {y : T ⟶ S}
    {a : X' ⟶ X} {f' : X' ⟶ T} (hX : IsPullback a f' f y)
    {b : Y' ⟶ Y} {g' : Y' ⟶ T} (hY : IsPullback b g' g y) :
    ∃ (i' : X' ⟶ Y') (r' : Y' ⟶ X'), i' ≫ r' = 𝟙 X' ∧ r' ≫ f' = g' ∧
      i' ≫ b = a ≫ i ∧ r' ≫ a = b ≫ r := by
  refine ⟨hY.lift (a ≫ i) f' (by rw [Category.assoc, section_comp hir hr, hX.w]),
    hX.lift (b ≫ r) g' (by rw [Category.assoc, hr, hY.w]), ?_, by simp, by simp, by simp⟩
  apply hX.hom_ext <;> simp [hir]

end Local

section RingHomProperty

variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {i : X ⟶ Y} {r : Y ⟶ X}

theorem of_hasRingHomProperty (P : MorphismProperty Scheme.{u})
    {Q : ∀ {R A : Type u} [CommRing R] [CommRing A], (R →+* A) → Prop} [HasRingHomProperty P Q]
    (hQ : ∀ {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
      (s : A →ₐ[R] B) (p : B →ₐ[R] A), p.comp s = AlgHom.id R A →
        Q (algebraMap R B) → Q (algebraMap R A))
    (hir : i ≫ r = 𝟙 X) (hr : r ≫ f = g) (hg : P g) : P f := by
  wlog hS : IsAffine S generalizing X Y S
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := P) S.affineCover]
    intro j
    obtain ⟨i', r', h₁, h₂, -, -⟩ := exists_baseChange hir hr
      (IsPullback.of_hasPullback f (S.affineCover.f j))
      (IsPullback.of_hasPullback g (S.affineCover.f j))
    exact this h₁ h₂ (IsZariskiLocalAtTarget.of_isPullback (.of_hasPullback _ _) hg) inferInstance
  choose U V hU hV hxU _ hUV hVU using fun x ↦ exists_affine_le hir x ⊤ trivial
  refine HasRingHomProperty.of_iSup_eq_top (fun x ↦ ⟨U x, hU x⟩) ?_ fun x ↦ ?_
  · exact eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxU x⟩
  · obtain ⟨s, p, -, -, h⟩ := exists_algHom_retract hir hr (W := ⊤) (hUV x) (hVU x) le_top le_top
    letI := (f.appLE ⊤ (U x) le_top).hom.toAlgebra
    letI := (g.appLE ⊤ (V x) le_top).hom.toAlgebra
    exact hQ s p h (HasRingHomProperty.appLE P g hg ⟨⊤, isAffineOpen_top S⟩ ⟨V x, hV x⟩ le_top)

variable (hir : i ≫ r = 𝟙 X) (hr : r ≫ f = g)
include hir hr

theorem locallyOfFiniteType [hg : LocallyOfFiniteType g] : LocallyOfFiniteType f :=
  of_hasRingHomProperty @LocallyOfFiniteType (fun s p h H ↦ by
    rw [RingHom.finiteType_algebraMap] at H ⊢
    exact finiteType_algebra s p h) hir hr hg

theorem locallyOfFinitePresentation [hg : LocallyOfFinitePresentation g] :
    LocallyOfFinitePresentation f :=
  of_hasRingHomProperty @LocallyOfFinitePresentation (fun s p h H ↦ by
    rw [RingHom.finitePresentation_algebraMap] at H ⊢
    exact finitePresentation_algebra s p h) hir hr hg

theorem flat [hg : Flat g] : Flat f :=
  of_hasRingHomProperty @Flat (fun s p h H ↦ by
    rw [RingHom.flat_algebraMap_iff] at H ⊢
    exact flat_algebra s p h) hir hr hg

theorem smooth [hg : Smooth g] : Smooth f :=
  of_hasRingHomProperty @Smooth (fun s p h H ↦ by
    rw [RingHom.smooth_algebraMap] at H ⊢
    exact smooth_algebra s p h) hir hr hg

theorem etale [hg : Etale g] : Etale f :=
  of_hasRingHomProperty @Etale (fun s p h H ↦ by
    rw [RingHom.etale_algebraMap] at H ⊢
    exact etale_algebra s p h) hir hr hg

theorem formallyUnramified [hg : FormallyUnramified g] : FormallyUnramified f :=
  of_hasRingHomProperty @FormallyUnramified (fun s p h H ↦ by
    rw [RingHom.formallyUnramified_algebraMap] at H ⊢
    exact formallyUnramified_algebra s p h) hir hr hg

theorem locallyQuasiFinite [hg : LocallyQuasiFinite g] : LocallyQuasiFinite f :=
  of_hasRingHomProperty @LocallyQuasiFinite (fun s p h H ↦ by
    rw [RingHom.quasiFinite_algebraMap] at H ⊢
    exact quasiFinite_algebra s p h) hir hr hg

end RingHomProperty

section Absolute

variable {X Y : Scheme.{u}} {i : X ⟶ Y} {r : Y ⟶ X} (hir : i ≫ r = 𝟙 X)
include hir

theorem surjective_retraction : Surjective r :=
  ⟨fun x ↦ ⟨i x, apply_apply hir x⟩⟩

theorem surjective_of_isPullback {T Z : Scheme.{u}} {t : T ⟶ X} {a : Z ⟶ Y} {r' : Z ⟶ T}
    (h : IsPullback a r' r t) : Surjective r' :=
  MorphismProperty.of_isPullback (P := @Surjective) h (surjective_retraction hir)

theorem mono_section : Mono i :=
  (SplitMono.mk r hir).mono

theorem connectedSpace [ConnectedSpace Y] : ConnectedSpace X :=
  (surjective_retraction hir).surj.connectedSpace r.continuous

theorem irreducibleSpace [IrreducibleSpace Y] : IrreducibleSpace X :=
  (surjective_retraction hir).surj.irreducibleSpace r.continuous

theorem isReduced [IsReduced Y] : IsReduced X := by
  refine ⟨fun U ↦ ?_⟩
  have hUV : U ≤ i ⁻¹ᵁ r ⁻¹ᵁ U := fun x hx ↦ by
    change r (i x) ∈ U
    rwa [apply_apply hir]
  refine isReduced_of_injective (r.appLE U (r ⁻¹ᵁ U) le_rfl).hom
    (Function.LeftInverse.injective (g := (i.appLE (r ⁻¹ᵁ U) U hUV).hom) fun a ↦ ?_)
  exact congr($(appLE_comp_appLE hir hUV le_rfl).hom a)

theorem isIntegral [IsIntegral Y] : IsIntegral X :=
  (isIntegral_iff_irreducibleSpace_and_isReduced X).mpr ⟨irreducibleSpace hir, isReduced hir⟩

end Absolute

section Global

variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {i : X ⟶ Y} {r : Y ⟶ X}
  (hir : i ≫ r = 𝟙 X) (hr : r ≫ f = g)
include hir hr

theorem isClosedImmersion_section [IsSeparated g] : IsClosedImmersion i := by
  subst hr
  have : IsSeparated r := IsSeparated.of_comp r f
  have : IsClosedImmersion (i ≫ r) := by rw [hir]; infer_instance
  exact IsClosedImmersion.of_comp i r

theorem surjective [Surjective g] : Surjective f := by
  subst hr
  exact Surjective.of_comp r f

theorem quasiCompact [QuasiCompact g] : QuasiCompact f := by
  subst hr
  refine ⟨fun U hU hU' ↦ ?_⟩
  have := (QuasiCompact.isCompact_preimage (f := r ≫ f) U hU hU').image r.continuous
  rwa [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp,
    Set.image_preimage_eq _ (surjective_retraction hir).surj] at this

theorem quasiSeparated [QuasiSeparated g] : QuasiSeparated f := by
  have := mono_section hir
  rw [← section_comp hir hr]
  infer_instance

theorem isSeparated [IsSeparated g] : IsSeparated f := by
  have := mono_section hir
  rw [← section_comp hir hr]
  infer_instance

theorem universallyClosed [UniversallyClosed g] : UniversallyClosed f := by
  subst hr
  have := surjective_retraction hir
  exact UniversallyClosed.of_comp_surjective r f

theorem isProper [IsProper g] : IsProper f := by
  have := isClosedImmersion_section hir hr
  rw [← section_comp hir hr]
  infer_instance

theorem isAffineHom [IsAffineHom g] : IsAffineHom f := by
  have := isClosedImmersion_section hir hr
  rw [← section_comp hir hr]
  infer_instance

theorem isFinite [IsFinite g] : IsFinite f := by
  have := isClosedImmersion_section hir hr
  rw [← section_comp hir hr]
  infer_instance

theorem geometrically (P : ObjectProperty Scheme.{u})
    (hP : ∀ {A B : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ A), a ≫ b = 𝟙 A → P B → P A)
    (hg : AlgebraicGeometry.geometrically P g) : AlgebraicGeometry.geometrically P f := by
  intro K _ y Z fst snd h
  obtain ⟨i', r', h₁, -, -, -⟩ := exists_baseChange hir hr h (IsPullback.of_hasPullback g y)
  exact hP i' r' h₁ (pullback_of_geometrically hg K y)

theorem geometricallyConnected [hg : GeometricallyConnected g] : GeometricallyConnected f :=
  ⟨geometrically hir hr _ (fun _ _ h _ ↦ connectedSpace h) hg.1⟩

theorem geometricallyIrreducible [hg : GeometricallyIrreducible g] : GeometricallyIrreducible f :=
  ⟨geometrically hir hr _ (fun _ _ h _ ↦ irreducibleSpace h) hg.1⟩

theorem geometricallyReduced [hg : GeometricallyReduced g] : GeometricallyReduced f :=
  ⟨geometrically hir hr _ (fun _ _ h _ ↦ isReduced h) hg.1⟩

theorem geometricallyIntegral [hg : GeometricallyIntegral g] : GeometricallyIntegral f :=
  ⟨geometrically hir hr _ (fun _ _ h _ ↦ isIntegral h) hg.1⟩

theorem properties :
    (LocallyOfFiniteType g → LocallyOfFiniteType f) ∧
    (LocallyOfFinitePresentation g → LocallyOfFinitePresentation f) ∧
    (Flat g → Flat f) ∧ (Smooth g → Smooth f) ∧ (Etale g → Etale f) ∧
    (QuasiCompact g → QuasiCompact f) ∧ (IsSeparated g → IsSeparated f) ∧
    (UniversallyClosed g → UniversallyClosed f) ∧ (IsProper g → IsProper f) ∧
    (IsFinite g → IsFinite f) ∧ (GeometricallyConnected g → GeometricallyConnected f) ∧
    Surjective r ∧ (IsSeparated g → IsClosedImmersion i) :=
  ⟨fun _ ↦ locallyOfFiniteType hir hr, fun _ ↦ locallyOfFinitePresentation hir hr,
    fun _ ↦ flat hir hr, fun _ ↦ smooth hir hr, fun _ ↦ etale hir hr,
    fun _ ↦ quasiCompact hir hr, fun _ ↦ isSeparated hir hr, fun _ ↦ universallyClosed hir hr,
    fun _ ↦ isProper hir hr, fun _ ↦ isFinite hir hr, fun _ ↦ geometricallyConnected hir hr,
    surjective_retraction hir, fun _ ↦ isClosedImmersion_section hir hr⟩

end Global

section Over

variable {S : Scheme.{u}} {X Y : Over S}

theorem over_left_comp (h : CategoryTheory.Retract X Y) : h.i.left ≫ h.r.left = 𝟙 X.left := by
  rw [← Over.comp_left, h.retract, Over.id_left]

theorem over_properties (h : CategoryTheory.Retract X Y) :
    (LocallyOfFiniteType Y.hom → LocallyOfFiniteType X.hom) ∧
    (LocallyOfFinitePresentation Y.hom → LocallyOfFinitePresentation X.hom) ∧
    (Flat Y.hom → Flat X.hom) ∧ (Smooth Y.hom → Smooth X.hom) ∧ (Etale Y.hom → Etale X.hom) ∧
    (QuasiCompact Y.hom → QuasiCompact X.hom) ∧ (IsSeparated Y.hom → IsSeparated X.hom) ∧
    (UniversallyClosed Y.hom → UniversallyClosed X.hom) ∧ (IsProper Y.hom → IsProper X.hom) ∧
    (IsFinite Y.hom → IsFinite X.hom) ∧
    (GeometricallyConnected Y.hom → GeometricallyConnected X.hom) ∧
    Surjective h.r.left ∧ (IsSeparated Y.hom → IsClosedImmersion h.i.left) :=
  properties (over_left_comp h) (Over.w h.r)

end Over

end GlobalTheory.Retract
