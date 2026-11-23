import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.LocIso

theorem isPullback_resLE_opensRange {W W' Y Z T S : Scheme.{0}} (π : Z ⟶ Y) (s : Z ⟶ T) (b : Y ⟶ S)
    (c : T ⟶ S) (i : W ⟶ Y) [IsOpenImmersion i] (k : W' ⟶ Z) (p : W' ⟶ W)
    (h₁ : IsPullback k p π i) (h₂ : IsPullback p (k ≫ s) (i ≫ b) c) :
    IsPullback (π.resLE i.opensRange (π ⁻¹ᵁ i.opensRange) le_rfl) ((π ⁻¹ᵁ i.opensRange).ι ≫ s)
      (i.opensRange.ι ≫ b) c := by
  let e : W ≅ i.opensRange.toScheme := IsOpenImmersion.isoOfRangeEq i i.opensRange.ι (by simp)
  have he : e.hom ≫ i.opensRange.ι = i := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hR : IsPullback (π.resLE i.opensRange (π ⁻¹ᵁ i.opensRange) le_rfl) (π ⁻¹ᵁ i.opensRange).ι
      i.opensRange.ι π := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]; exact isPullback_morphismRestrict π _
  have hW : IsPullback (p ≫ e.hom) k i.opensRange.ι π := by
    refine IsPullback.of_iso h₁.flip (Iso.refl _) e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp [he]
  let φ := IsPullback.isoIsPullback _ _ hW hR
  refine IsPullback.of_iso h₂ φ e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (IsPullback.isoIsPullback_hom_fst _ _ hW hR).symm
  · rw [Iso.refl_hom, Category.comp_id, ← Category.assoc, IsPullback.isoIsPullback_hom_snd]
  · simp [← he]
  · simp

theorem isLocalization_tensor (R R' C' : Type) [CommRing R] [CommRing R'] [CommRing C'] [Algebra R R']
    [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] (C : Subalgebra R C') (f g : C)
    (hcok : ∀ x : C', ∃ n : ℕ, (f : C') ^ n * x ∈ Set.range (Algebra.TensorProduct.lift C.val
      (IsScalarTower.toAlgHom R R' C') fun _ _ => Commute.all _ _))
    (hker : ∀ t : TensorProduct R C R', (Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C')
      fun _ _ => Commute.all _ _) t = 0 → ∃ n : ℕ, ((f ^ n) ⊗ₜ[R] (1 : R')) * t = 0) :
    letI : Algebra (TensorProduct R C R') (Localization.Away (algebraMap C C' (f * g))) :=
      ((algebraMap C' _).comp (Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C')
        fun _ _ => Commute.all _ _).toRingHom).toAlgebra
    IsLocalization (Submonoid.powers ((f * g) ⊗ₜ[R] (1 : R'))) (Localization.Away (algebraMap C C' (f * g))) := by
  set Φ := Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') fun _ _ => Commute.all _ _ with hΦdef
  letI : Algebra (TensorProduct R C R') (Localization.Away (algebraMap C C' (f * g))) :=
    ((algebraMap C' _).comp Φ.toRingHom).toAlgebra
  have hΦ : ∀ c : C, Φ (c ⊗ₜ[R] (1 : R')) = algebraMap C C' c := fun c => by simp [Φ]
  have halg : ∀ t, algebraMap (TensorProduct R C R') (Localization.Away (algebraMap C C' (f * g))) t =
      algebraMap C' _ (Φ t) := fun t => rfl
  have hpow : ∀ n : ℕ, ((f * g) ⊗ₜ[R] (1 : R')) ^ n = ((g ^ n) ⊗ₜ[R] (1 : R')) * ((f ^ n) ⊗ₜ[R] (1 : R')) := by
    intro n
    rw [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_pow, one_pow, _root_.mul_one, _root_.mul_comm (g ^ n)]
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [halg, map_pow, hΦ, map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit _).pow n
  · intro z
    obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, hz⟩ := IsLocalization.surj (Submonoid.powers (algebraMap C C' (f * g))) z
    obtain ⟨k, t, ht⟩ := hcok a
    refine ⟨⟨t * ((g ^ k) ⊗ₜ[R] (1 : R')), ⟨((f * g) ⊗ₜ[R] (1 : R')) ^ (m + k), m + k, rfl⟩⟩, ?_⟩
    rw [halg, halg, map_pow Φ, hΦ, map_mul Φ, hΦ, ht, pow_add, map_mul (algebraMap C' _), ← _root_.mul_assoc, hz,
      ← map_mul (algebraMap C' _)]
    refine congrArg (algebraMap C' _) ?_
    have hco : ∀ c : C, algebraMap C C' c = (c : C') := fun _ => rfl
    simp only [hco, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
    ring
  · intro x y hxy
    rw [halg, halg] at hxy
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (algebraMap C C' (f * g))) hxy
    have h0 : Φ (((f * g) ⊗ₜ[R] (1 : R')) ^ m * (x - y)) = 0 := by
      rw [map_mul, map_pow, hΦ, map_sub, mul_sub]
      exact sub_eq_zero.mpr hm
    obtain ⟨n, hn⟩ := hker _ h0
    refine ⟨⟨((f * g) ⊗ₜ[R] (1 : R')) ^ (n + m), n + m, rfl⟩, ?_⟩
    change ((f * g) ⊗ₜ[R] (1 : R')) ^ (n + m) * x = ((f * g) ⊗ₜ[R] (1 : R')) ^ (n + m) * y
    rw [← sub_eq_zero, ← mul_sub, pow_add, hpow, _root_.mul_assoc, _root_.mul_assoc, hn, mul_zero]

theorem exists_smooth_basicOpen_iso : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (X : Over (Sp R)) (Z : Scheme.{0}) (π : Z ⟶ X.left) (s : Z ⟶ Sp R') (hX : π ≫ X.hom = s ≫ spMap (algebraMap R R')) (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] (C : Subalgebra R C') (j : Sp C' ⟶ Z) (l : Sp C ⟶ X.left) [IsOpenImmersion l], IsPullback j (spMap (algebraMap C C')) π l → j ≫ s = spMap (algebraMap R' C') → l ≫ X.hom = spMap (algebraMap R C) → ∀ f g : C, (∀ x : C', ∃ n : ℕ, (f : C') ^ n * x ∈ Set.range (Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') fun _ _ => Commute.all _ _)) → (∀ t : TensorProduct R C R', (Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') fun _ _ => Commute.all _ _) t = 0 → ∃ n : ℕ, ((f ^ n) ⊗ₜ[R] (1 : R')) * t = 0) → Algebra.Smooth R (Localization.Away g) → ∀ q : Sp C, f ∉ q.asIdeal → g ∉ q.asIdeal → ∃ V : X.left.Opens, l q ∈ V ∧ IsAffineOpen V ∧ Smooth (V.ι ≫ X.hom) ∧ IsIso (pullback.lift (π.resLE V (π ⁻¹ᵁ V) le_rfl) ((π ⁻¹ᵁ V).ι ≫ s) (by rw [Scheme.Hom.resLE_comp_ι_assoc, hX]; simp only [Category.assoc]) : (π ⁻¹ᵁ V).toScheme ⟶ pullback (V.ι ≫ X.hom) (spMap (algebraMap R R'))) := by
  intro R R' _ _ _ X Z π s hX C' _ _ _ _ C j l _ hP hj hl f g hcok hker hsm q hf hg
  let A := Localization.Away (f * g)
  let A' := Localization.Away (algebraMap C C' (f * g))
  let φ : A →+* A' := IsLocalization.Away.map A A' (algebraMap C C') (f * g)
  have hφ : φ.comp (algebraMap C A) = (algebraMap C' A').comp (algebraMap C C') := IsLocalization.map_comp _
  have hLoc : IsPushout (CommRingCat.ofHom (algebraMap C C')) (CommRingCat.ofHom (algebraMap C A))
      (CommRingCat.ofHom (algebraMap C' A')) (CommRingCat.ofHom φ) := by
    have : IsLocalization ((Submonoid.powers (f * g)).map (algebraMap C C')) A' := by
      rw [Submonoid.map_powers]; infer_instance
    exact CommRingCat.isPushout_of_isLocalization _ _ hφ (Submonoid.powers (f * g))
  haveI : IsOpenImmersion (spMap (algebraMap C A)) := IsOpenImmersion.of_isLocalization (f * g)
  have h₁ : IsPullback (spMap (algebraMap C' A') ≫ j) (spMap φ) π (spMap (algebraMap C A) ≫ l) :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ hLoc).paste_horiz hP
  have hRing : IsPushout (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom (algebraMap R R'))
      (CommRingCat.ofHom φ) (CommRingCat.ofHom (algebraMap R' A')) := by
    let Φ := Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') fun _ _ => Commute.all _ _
    letI : Algebra (TensorProduct R C R') A' := ((algebraMap C' A').comp Φ.toRingHom).toAlgebra
    have hL := isLocalization_tensor R R' C' C f g hcok hker
    have Q1 := CommRingCat.isPushout_tensorProduct R C R'
    have : IsLocalization ((Submonoid.powers (f * g)).map
        (Algebra.TensorProduct.includeLeftRingHom : C →+* TensorProduct R C R')) A' := by
      rw [Submonoid.map_powers]; exact hL
    have H : φ.comp (algebraMap C A) = (algebraMap (TensorProduct R C R') A').comp
        Algebra.TensorProduct.includeLeftRingHom := by
      rw [hφ]
      ext c
      simp [RingHom.algebraMap_toAlgebra, Φ]
    have Q2 := CommRingCat.isPushout_of_isLocalization (S := TensorProduct R C R') (Rₘ := A) (Sₘ := A')
      Algebra.TensorProduct.includeLeftRingHom φ H (Submonoid.powers (f * g))
    have Q := (Q1.flip.paste_vert Q2).flip
    convert Q using 1
    · ext c; simp [← IsScalarTower.algebraMap_apply]
    · ext r; simp [RingHom.algebraMap_toAlgebra, Φ, ← IsScalarTower.algebraMap_apply]
  have hs : (spMap (algebraMap C' A') ≫ j) ≫ s = spMap (algebraMap R' A') := by
    rw [Category.assoc, hj, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have hb : (spMap (algebraMap C A) ≫ l) ≫ X.hom = spMap (algebraMap R A) := by
    rw [Category.assoc, hl, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have h₂ : IsPullback (spMap φ) ((spMap (algebraMap C' A') ≫ j) ≫ s)
      ((spMap (algebraMap C A) ≫ l) ≫ X.hom) (spMap (algebraMap R R')) := by
    rw [hs, hb]; exact isPullback_SpecMap_of_isPushout _ _ _ _ hRing
  have hG := isPullback_resLE_opensRange π s X.hom (spMap (algebraMap R R')) _ _ _ h₁ h₂
  refine ⟨(spMap (algebraMap C A) ≫ l).opensRange, ?_, isAffineOpen_opensRange _, ?_, ?_⟩
  · obtain ⟨w, hw⟩ : q ∈ Set.range (PrimeSpectrum.comap (algebraMap C A)) := by
      rw [PrimeSpectrum.localization_away_comap_range A (f * g)]
      exact fun h => (q.isPrime.mem_or_mem h).elim hf hg
    refine ⟨w, ?_⟩
    first
      | exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg l hw)
      | exact (Scheme.comp_base_apply _ _ _).trans (congrArg l hw)
      | exact congrArg l hw
  · let B := Localization.Away (algebraMap C (Localization.Away g) f)
    haveI : Algebra.Smooth R B := Algebra.Smooth.comp R (Localization.Away g) B
    haveI : Algebra.Smooth R A :=
      Algebra.Smooth.of_equiv ((IsLocalization.algEquiv (Submonoid.powers (f * g)) B A).restrictScalars R)
    haveI : Smooth (spMap (algebraMap R A)) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)
    let e := IsOpenImmersion.isoOfRangeEq (spMap (algebraMap C A) ≫ l)
      (spMap (algebraMap C A) ≫ l).opensRange.ι (by simp)
    have hfac : e.hom ≫ (spMap (algebraMap C A) ≫ l).opensRange.ι = spMap (algebraMap C A) ≫ l :=
      IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
    have : (spMap (algebraMap C A) ≫ l).opensRange.ι ≫ X.hom = e.inv ≫ spMap (algebraMap R A) := by
      calc _ = e.inv ≫ (e.hom ≫ (spMap (algebraMap C A) ≫ l).opensRange.ι) ≫ X.hom := by simp
        _ = _ := by rw [hfac, hb]
    rw [this]; infer_instance
  · convert (inferInstance : IsIso hG.isoPullback.hom)
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans hG.isoPullback_hom_fst.symm
    · exact (pullback.lift_snd _ _ _).trans hG.isoPullback_hom_snd.symm

end GlobalTheory.Mum.LocIso
