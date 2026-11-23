import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqZeroOfForallPowDvdGerm

universe u v

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.PrimeSection

theorem res_appLE {X Y : Scheme.{u}} (j : Y ⟶ X) {U : X.Opens} {W W' : Y.Opens}
    (h : W ≤ j ⁻¹ᵁ U) (h' : W' ≤ W) (s : Γ(X, U)) :
    Y.presheaf.map (homOfLE h').op (j.appLE U W h s) = j.appLE U W' (h'.trans h) s := by
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]

theorem appLE_res {X Y : Scheme.{u}} (j : Y ⟶ X) {U U' : X.Opens} {W : Y.Opens}
    (h : W ≤ j ⁻¹ᵁ U') (h' : U' ≤ U) (s : Γ(X, U)) :
    j.appLE U' W h (X.presheaf.map (homOfLE h').op s) =
      j.appLE U W (h.trans (j.preimage_mono h')) s := by
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE]

theorem appLE_appLE {X Y Z : Scheme.{u}} (i : Z ⟶ Y) (j : Y ⟶ X) {k : Z ⟶ X} (hk : i ≫ j = k)
    {U : X.Opens} {W : Y.Opens} {A : Z.Opens} (h : W ≤ j ⁻¹ᵁ U) (h' : A ≤ i ⁻¹ᵁ W)
    (h'' : A ≤ k ⁻¹ᵁ U) (s : Γ(X, U)) :
    i.appLE W A h' (j.appLE U W h s) = k.appLE U A h'' s := by
  subst hk
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_comp_appLE]

theorem appLE_bijective {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] {U : X.Opens}
    (hU : U ≤ j.opensRange) {W : Y.Opens} (h : W = j ⁻¹ᵁ U) :
    Function.Bijective (j.appLE U W h.le) := by
  subst h
  rw [Scheme.Hom.appLE_eq_app]
  have := j.isIso_app U hU
  exact ConcreteCategory.bijective_of_isIso _

theorem eq_preimage_inf {X Y : Scheme.{u}} {j : Y ⟶ X} [IsOpenImmersion j] {D U : X.Opens}
    (hj : j.opensRange = D) {W : Y.Opens} (h : W = j ⁻¹ᵁ U) : W = j ⁻¹ᵁ (U ⊓ D) := by
  subst h hj
  exact le_antisymm (fun y hy ↦ ⟨hy, y, rfl⟩) fun y hy ↦ hy.1

theorem appLE_injective {X Y : Scheme.{u}} [IsIntegral X] (j : Y ⟶ X) [IsOpenImmersion j]
    [Nonempty Y] {U : X.Opens} {W : Y.Opens} (h : W = j ⁻¹ᵁ U) :
    Function.Injective (j.appLE U W h.le) := by
  intro s s' H
  obtain ⟨y⟩ := ‹Nonempty Y›
  refine res_inf_injective (D := j.opensRange) (genericPoint_mem ⟨y, rfl⟩) U
    ((appLE_bijective j inf_le_right (eq_preimage_inf rfl h)).1 ?_)
  rw [appLE_res, appLE_res]
  exact H

section Immersion

variable {X : Scheme.{u}} {t : Γ(X, ⊤)} {η : X}
  (hη : ∀ x : X, x ∉ X.basicOpen t ↔ η ⤳ x)
  (hp : ∀ U : X.Opens, IsAffineOpen U → η ∈ U →
    Prime (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t))
  [IsIntegral X] [IsLocallyNoetherian X]
  {Y : Scheme.{u}} {j : Y ⟶ X} [IsOpenImmersion j] (hj : j.opensRange = X.basicOpen t)
  {ι : Type v} {U : ι → X.Opens} {g : ∀ a b, Γ(X, U a ⊓ U b)}
  {W : ι → Y.Opens} (hW : ∀ a, W a = j ⁻¹ᵁ U a)

omit [IsIntegral X] [IsLocallyNoetherian X] in
include hj in

theorem exists_transport (r : ∀ a, Γ(Y, W a))
    (hr : ∀ a b, Y.presheaf.map (homOfLE inf_le_left).op (r a) =
      j.appLE (U a ⊓ U b) (W a ⊓ W b) (inf_le_inf (hW a).le (hW b).le) (g a b) *
        Y.presheaf.map (homOfLE inf_le_right).op (r b))
    (τ : Γ(Y, ⊤)ˣ) (hτ : (τ : Γ(Y, ⊤)) = j.appTop t) :
    ∃ (r' : ∀ a, Γ(X, U a ⊓ X.basicOpen t)) (τ' : Γ(X, X.basicOpen t)ˣ),
      (τ' : Γ(X, X.basicOpen t)) = X.presheaf.map (homOfLE le_top).op t ∧
      (∀ a b, X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_left)).op (r' a) =
        X.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ⊓ X.basicOpen t ≤ U a ⊓ U b)).op
          (g a b) * X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_right)).op (r' b)) ∧
      (∀ a, r' a = 0 → r a = 0) ∧ (∀ a, IsUnit (r a) → IsUnit (r' a)) ∧
      ∀ (n : ℤ) (a : ι) (s : Γ(X, U a)), X.presheaf.map (homOfLE inf_le_left).op s =
        X.presheaf.map (homOfLE inf_le_right).op (↑(τ' ^ n) : Γ(X, X.basicOpen t)) * r' a ↔
        j.appLE (U a) (W a) (hW a).le s =
          Y.presheaf.map (homOfLE le_top).op (↑(τ ^ n) : Γ(Y, ⊤)) * r a := by
  have hb := fun a ↦ appLE_bijective j (inf_le_right.trans hj.ge) (eq_preimage_inf hj (hW a))
  choose r' hr' using fun a ↦ (hb a).2 (r a)
  obtain ⟨τ', hτ'⟩ := exists_unit_eq_res t
  have htop : (⊤ : Y.Opens) ≤ j ⁻¹ᵁ X.basicOpen t := fun y _ ↦ hj.le ⟨y, rfl⟩
  have hττ : Units.map (j.appLE _ ⊤ htop).hom.toMonoidHom τ' = τ := by
    ext
    rw [Units.coe_map, hτ, hτ']
    exact (appLE_res j _ _ _).trans (congrArg (fun φ : Γ(X, ⊤) ⟶ Γ(Y, ⊤) ↦ φ t) j.appLE_eq_app)
  refine ⟨r', τ', hτ', fun a b ↦ ?_, fun a h ↦ by rw [← hr', h, map_zero], fun a h ↦ ?_,
    fun n a s ↦ ?_⟩
  · have hab : W a ⊓ W b = j ⁻¹ᵁ (U a ⊓ U b) := by rw [hW, hW]; rfl
    refine (appLE_bijective j (inf_le_right.trans hj.ge) (eq_preimage_inf hj hab)).1 ?_
    have := hr a b
    rw [← hr' a, ← hr' b, res_appLE, res_appLE] at this
    rw [map_mul, appLE_res, appLE_res, appLE_res]
    exact this
  · rw [← hr' a] at h
    exact (isUnit_map_iff (RingEquiv.ofBijective _ (hb a)) _).1 h
  · rw [← (hb a).1.eq_iff, map_mul, appLE_res, appLE_res, hr', ← hττ, ← map_zpow, Units.coe_map]
    exact iff_of_eq (congrArg (_ = · * _) (res_appLE j htop le_top _).symm)

include hη hp hj in

theorem existsUnique_zpow_mul_appLE (hU : ∀ x : X, ∃ a, x ∈ U a) (hg : ∀ a b, IsUnit (g a b))
    (τ : Γ(Y, ⊤)ˣ) (hτ : (τ : Γ(Y, ⊤)) = j.appTop t) {r : ∀ a, Γ(Y, W a)}
    (hr : ∀ a b, Y.presheaf.map (homOfLE inf_le_left).op (r a) =
      j.appLE (U a ⊓ U b) (W a ⊓ W b) (inf_le_inf (hW a).le (hW b).le) (g a b) *
        Y.presheaf.map (homOfLE inf_le_right).op (r b))
    (hr0 : ∃ a, r a ≠ 0) :
    ∃! n : ℤ, ∃ s : ∀ a, Γ(X, U a),
      (∀ a b, X.presheaf.map (homOfLE inf_le_left).op (s a) =
        g a b * X.presheaf.map (homOfLE inf_le_right).op (s b)) ∧
      (∀ a, j.appLE (U a) (W a) (hW a).le (s a) =
        Y.presheaf.map (homOfLE le_top).op (↑(τ ^ n) : Γ(Y, ⊤)) * r a) ∧
      ∃ a, ∃ x, x ∉ X.basicOpen t ∧ x ∈ X.basicOpen (s a) := by
  obtain ⟨r', τ', hτ', hr', h0, -, H⟩ := exists_transport hj hW r hr τ hτ
  simpa only [H] using existsUnique_zpow_mul hη hp hU hg τ' hτ' hr'
    (hr0.imp fun a ha h ↦ ha (h0 a h))

include hη hp hj in

theorem exists_isUnit_appLE_eq (hU : ∀ x : X, ∃ a, x ∈ U a) (hg : ∀ a b, IsUnit (g a b))
    {r : ∀ a, Γ(Y, W a)}
    (hr : ∀ a b, Y.presheaf.map (homOfLE inf_le_left).op (r a) =
      j.appLE (U a ⊓ U b) (W a ⊓ W b) (inf_le_inf (hW a).le (hW b).le) (g a b) *
        Y.presheaf.map (homOfLE inf_le_right).op (r b))
    (hru : ∀ a, IsUnit (r a)) {T T' : Scheme.{u}} [IsIntegral T] [Nonempty T'] (e : T ⟶ X)
    (k : T' ⟶ T) [IsOpenImmersion k] (e' : T' ⟶ Y) (he : e' ≫ j = k ≫ e)
    {y : T} (hy : e y ∉ X.basicOpen t) {a₀ : ι} {A : T.Opens} (hyA : y ∈ A)
    (hA : A ≤ e ⁻¹ᵁ U a₀) {A' : T'.Opens} (hA' : A' = k ⁻¹ᵁ A) (hA'' : A' ≤ e' ⁻¹ᵁ W a₀)
    {u : Γ(T, A)} (hu : IsUnit u) (hur : k.appLE A A' hA'.le u = e'.appLE (W a₀) A' hA'' (r a₀)) :
    ∃ s : ∀ a, Γ(X, U a), (∀ a, IsUnit (s a)) ∧
      (∀ a b, X.presheaf.map (homOfLE inf_le_left).op (s a) =
        g a b * X.presheaf.map (homOfLE inf_le_right).op (s b)) ∧
      ∀ a, j.appLE (U a) (W a) (hW a).le (s a) = r a := by
  obtain ⟨τ, hτ⟩ : IsUnit (j.appTop t) := by
    obtain ⟨τ', hτ'⟩ := exists_unit_eq_res t
    have htop : (⊤ : Y.Opens) ≤ j ⁻¹ᵁ X.basicOpen t := fun y _ ↦ hj.le ⟨y, rfl⟩
    have := τ'.isUnit.map (j.appLE _ ⊤ htop).hom
    rw [hτ', appLE_res] at this
    rwa [← show j.appLE ⊤ ⊤ _ = j.appTop from j.appLE_eq_app]
  obtain ⟨r', τ', hτ', hr', -, hu', H⟩ := exists_transport hj hW r hr τ hτ
  obtain ⟨n, s, hsu, hc, hs⟩ :=
    exists_zpow_mul_isUnit hη hp hU hg τ' hτ' hr' fun a ↦ hu' a (hru a)
  simp only [H] at hs
  have hnat : ∀ z : Γ(X, U a₀), k.appLE A A' hA'.le (e.appLE _ A hA z) =
      e'.appLE (W a₀) A' hA'' (j.appLE _ _ (hW a₀).le z) := fun z ↦ by
    have h : A' ≤ (k ≫ e) ⁻¹ᵁ U a₀ := hA'.le.trans (k.preimage_mono hA)
    rw [appLE_appLE k e rfl _ _ h, appLE_appLE e' j he _ _ h]
  let φ : Γ(Y, ⊤) →+* Γ(T', A') :=
    (e'.appLE (W a₀) A' hA'').hom.comp (Y.presheaf.map (homOfLE le_top).op).hom
  obtain rfl : n = 0 := by
    refine zpow_eq_zero (k.appLE A A' hA'.le).hom (appLE_injective k hA')
      ((hsu a₀).map (e.appLE _ A hA).hom) hu
      (p := e.appLE _ A hA (X.presheaf.map (homOfLE (le_top : U a₀ ≤ ⊤)).op t)) (fun H ↦ hy ?_)
      (Units.map φ.toMonoidHom τ) ?_ ?_
    · have := T.basicOpen_of_isUnit H
      rw [Scheme.basicOpen_appLE, Scheme.basicOpen_res] at this
      exact (show y ∈ A ⊓ e ⁻¹ᵁ (U a₀ ⊓ X.basicOpen t) from this.ge hyA).2.2
    · rw [hnat, appLE_res, Units.coe_map, hτ,
        ← show j.appLE ⊤ ⊤ le_top = j.appTop from j.appLE_eq_app]
      exact congrArg (e'.appLE (W a₀) A' hA'') (res_appLE j _ _ _)
    · rw [hnat, hs, map_mul, hur, ← map_zpow, Units.coe_map]
      rfl
  exact ⟨s, hsu, hc, fun a ↦ by simpa using hs a⟩

end Immersion

theorem isIntegral_of_basicOpen {X Y : Scheme.{u}} {t : Γ(X, ⊤)}
    (ht : ∀ U : X.Opens, IsAffineOpen U →
      X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t ∈ nonZeroDivisors Γ(X, U))
    (j : Y ⟶ X) [IsOpenImmersion j] [IsIntegral Y] (hj : j.opensRange = X.basicOpen t) :
    IsIntegral X := by
  have hinj : ∀ U : X.Opens, IsAffineOpen U →
      Function.Injective (j.appLE U (j ⁻¹ᵁ U) le_rfl) := fun U hU s s' h ↦ by
    have := hU.isLocalization_basicOpen (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t)
    refine IsLocalization.injective
      Γ(X, X.basicOpen (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t))
      ((Submonoid.powers_le).2 (ht U hU)) ?_
    have he : X.basicOpen (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t) =
      U ⊓ X.basicOpen t := X.basicOpen_res _ _
    refine (appLE_bijective j (W := j ⁻¹ᵁ U) (he.le.trans (inf_le_right.trans hj.ge))
      (he ▸ eq_preimage_inf hj rfl)).1 ?_
    exact (appLE_res j _ _ s).trans (h.trans (appLE_res j _ _ s').symm)
  have : IsReduced X := ⟨fun W ↦ ⟨fun s hs ↦ X.IsSheaf.section_ext fun x hx ↦ by
    obtain ⟨U, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset hx
    refine ⟨U, hUW, hxU, hinj U hU ?_⟩
    rw [map_zero, map_zero]
    exact ((hs.map _).map _).eq_zero⟩⟩
  have hdense : Dense (Set.range j) := by
    refine dense_iff_inter_open.2 fun W hW ⟨x, hx⟩ ↦ ?_
    obtain ⟨U, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset (U := ⟨W, hW⟩) hx
    by_contra hne
    have hbot : j ⁻¹ᵁ U = ⊥ := eq_bot_iff.2 fun y hy ↦ hne ⟨j y, hUW hy, y, rfl⟩
    have : Subsingleton Γ(Y, j ⁻¹ᵁ U) := by rw [hbot]; infer_instance
    have : Nonempty U := ⟨⟨x, hxU⟩⟩
    exact not_subsingleton Γ(X, U) (hinj U hU).subsingleton
  have : IrreducibleSpace X := by
    have h := (IrreducibleSpace.isIrreducible_univ Y).image j j.continuous.continuousOn
    rw [Set.image_univ] at h
    have h' := h.closure
    rw [hdense.closure_eq] at h'
    exact (irreducibleSpace_def X).2 h'
  exact isIntegral_of_irreducibleSpace_of_isReduced X

theorem ker_eq_map_of_isPushout {A B C P : CommRingCat.{u}} {α : A ⟶ B} {β : A ⟶ C} {γ : B ⟶ P}
    {δ : C ⟶ P} (h : IsPushout α β γ δ) (hβ : Function.Surjective β) :
    RingHom.ker γ.hom = (RingHom.ker β.hom).map α.hom := by
  refine le_antisymm (fun z hz ↦ ?_) (Ideal.map_le_iff_le_comap.2 fun a ha ↦ ?_)
  · let J := (RingHom.ker β.hom).map α.hom
    have hJ : RingHom.ker β.hom ≤ RingHom.ker ((Ideal.Quotient.mk J).comp α.hom) := fun a ha ↦
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha)
    let ψ : C →+* B ⧸ J := RingHom.liftOfSurjective β.hom hβ ⟨_, hJ⟩
    have w : α ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) = β ≫ CommRingCat.ofHom ψ := by
      ext a
      exact (RingHom.liftOfSurjective_comp_apply β.hom hβ ⟨_, hJ⟩ a).symm
    have := congrArg (fun φ : B ⟶ CommRingCat.of (B ⧸ J) ↦ φ z) (h.inl_desc _ _ w)
    rw [CommRingCat.comp_apply, show γ z = 0 from hz, map_zero] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this.symm
  · have := congrArg (fun φ : A ⟶ P ↦ φ a) h.w
    simp only [CommRingCat.comp_apply] at this
    rw [show β a = 0 from ha, map_zero] at this
    exact this

theorem ker_app_eq_span {X Z : Scheme.{u}} {A C : CommRingCat.{u}} {β : A ⟶ C}
    (hβ : Function.Surjective β) {c : A} (hc : RingHom.ker β.hom = Ideal.span {c})
    {f : X ⟶ Spec A} {i : Z ⟶ X} {f' : Z ⟶ Spec C} (h : IsPullback i f' f (Spec.map β))
    {U : X.Opens} (hU : IsAffineOpen U) :
    RingHom.ker (i.app U).hom = Ideal.span {X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
      (f.appTop ((Scheme.ΓSpecIso A).inv c))} := by
  have hpo := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := U) (UY := i ⁻¹ᵁ U) le_top
    le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  have hpo' : IsPushout ((Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ U le_top) β (i.app U)
      ((Scheme.ΓSpecIso C).inv ≫ f'.appLE ⊤ (i ⁻¹ᵁ U) le_top) := by
    refine hpo.of_iso (Scheme.ΓSpecIso A) (Iso.refl _) (Scheme.ΓSpecIso C) (Iso.refl _)
      (by simp) ?_ (by simp [Scheme.Hom.appLE_eq_app]) (by simp)
    rw [← Scheme.ΓSpecIso_naturality]
    congr 1
  rw [ker_eq_map_of_isPushout hpo' hβ, hc, Ideal.map_span, Set.image_singleton]
  rfl

end GlobalTheory.PrimeSection
