import ReciprocityTheory.AnalyticForms.RegularLocalRings.WChartsA

namespace ReciprocityTheory.AnForm.R

open AlgebraicGeometry CategoryTheory

noncomputable section

theorem algebraMap_mem_nonZeroDivisors_of_isLocalization {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S] {a : R} (ha : a ∈ nonZeroDivisors R) :
    algebraMap R S a ∈ nonZeroDivisors S := by
  rw [mem_nonZeroDivisors_iff_right] at ha ⊢
  intro x hx
  obtain ⟨⟨y, m⟩, rfl⟩ := IsLocalization.mk'_surjective M x
  have h1 : algebraMap R S (y * a) = 0 := by
    rw [map_mul, ← IsLocalization.mk'_spec S y m, mul_right_comm, hx, zero_mul]
  obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff M S _).1 h1
  exact (IsLocalization.mk'_eq_zero_iff y m).2 ⟨c, ha _ (by rw [← hc, mul_assoc])⟩

theorem reesChart_lift {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {m : ℕ} (g : Fin m → R)
    (j : Fin m) (hj : φ (g j) ∈ nonZeroDivisors S) (c : Fin m → S) (hc : ∀ k, φ (g k) = c k * φ (g j)) :
    ∃ ψ : FinalTheorems.reesChart g j →+* S, ψ.comp (algebraMap R (FinalTheorems.reesChart g j)) = φ := by
  let S' := Localization.Away (φ (g j))
  have hinj : Function.Injective (algebraMap S S') :=
    IsLocalization.injective S' (Submonoid.powers_le.2 hj)
  let L : Localization.Away (g j) →+* S' := IsLocalization.Away.map _ _ φ (g j)
  have hL : ∀ r, L (algebraMap R _ r) = algebraMap S S' (φ r) := fun r =>
    IsLocalization.map_eq _ _
  have key : ∀ x ∈ FinalTheorems.reesChart g j, L x ∈ (algebraMap S S').range := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      refine ⟨c k, ?_⟩
      have hu : IsUnit (algebraMap S S' (φ (g j))) := IsLocalization.Away.algebraMap_isUnit _
      apply hu.mul_left_injective
      have := congrArg L (IsLocalization.mk'_spec (Localization.Away (g j)) (g k)
        (⟨g j, Submonoid.mem_powers _⟩ : Submonoid.powers (g j)))
      rw [map_mul, hL, hL] at this
      show algebraMap S S' (c k) * _ = L _ * _
      rw [← map_mul, ← hc]; exact this.symm
    | algebraMap r => exact ⟨φ r, (hL r).symm⟩
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  let F : FinalTheorems.reesChart g j →+* (algebraMap S S').range :=
    (L.comp (FinalTheorems.reesChart g j).val.toRingHom).codRestrict _ (fun x => key x.1 x.2)
  let E : S ≃+* (algebraMap S S').range :=
    RingEquiv.ofBijective (algebraMap S S').rangeRestrict
      ⟨fun a b h => hinj (congrArg Subtype.val h), (algebraMap S S').rangeRestrict_surjective⟩
  refine ⟨E.symm.toRingHom.comp F, ?_⟩
  ext r
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [RingEquiv.symm_apply_eq]
  apply Subtype.ext
  simp [F, E, hL]
  try rfl

theorem ringEquiv_mem_nonZeroDivisors {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) {a : A}
    (ha : a ∈ nonZeroDivisors A) : e a ∈ nonZeroDivisors B := by
  rw [mem_nonZeroDivisors_iff_right] at ha ⊢
  intro x hx
  have : e.symm x * a = 0 := by
    apply e.injective; rw [map_mul, e.apply_symm_apply, hx, map_zero]
  simpa using congrArg e (ha _ this)

theorem effCartier_comap_of_isOpenImmersion' {X Y : Scheme.{0}} (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] (hI : FinalTheorems.EffCartier I) : FinalTheorems.EffCartier (I.comap f) := by
  intro x
  obtain ⟨U, h, hxU, hh, hU⟩ := hI (f x)
  obtain ⟨r, hrle, hxr⟩ := U.2.exists_basicOpen_le (V := f.opensRange) ⟨f x, ⟨x, rfl⟩⟩ hxU
  have himg : f ''ᵁ (f ⁻¹ᵁ Y.basicOpen r) = Y.basicOpen r := by
    rw [f.image_preimage_eq_opensRange_inf, inf_eq_right.2 hrle]
  have hUX : IsAffineOpen (f ⁻¹ᵁ Y.basicOpen r) := by
    rw [← f.isAffineOpen_iff_of_isOpenImmersion, himg]; exact U.2.basicOpen r
  have hle : f ''ᵁ (f ⁻¹ᵁ Y.basicOpen r) ≤ U.1 := himg.le.trans (Y.basicOpen_le r)
  have hnzd : ∀ (O : Y.Opens) (hO : O = Y.basicOpen r) (hOU : O ≤ U.1),
      Y.presheaf.map (homOfLE hOU).op h ∈ nonZeroDivisors Γ(Y, O) := by
    rintro O rfl hOU
    have := U.2.isLocalization_basicOpen r
    exact algebraMap_mem_nonZeroDivisors_of_isLocalization (Submonoid.powers r) hh
  let e := (f.appIso (f ⁻¹ᵁ Y.basicOpen r)).commRingCatIsoToRingEquiv
  refine ⟨⟨_, hUX⟩, e (Y.presheaf.map (homOfLE hle).op h), hxr, ?_, ?_⟩
  · exact ringEquiv_mem_nonZeroDivisors e (hnzd _ himg hle)
  · rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
    rw [← I.map_ideal (U := ⟨_, (f.isAffineOpen_iff_of_isOpenImmersion).2 hUX⟩) (V := U) hle, hU,
      Ideal.map_span, Set.image_singleton]
    rw [show ((f.appIso (f ⁻¹ᵁ Y.basicOpen r)).inv.hom : _ →+* _) = (e.symm : _ →+* _) from rfl,
      Ideal.comap_coe, Ideal.comap_symm, Ideal.map_span, Set.image_singleton]
    rfl

theorem inter_reesCharts' {X W : Scheme.{0}} (π : W ⟶ X) (J : X.IdealSheafData) (hB : FinalTheorems.Blowup π J)
    (U : X.affineOpens) {m : ℕ} (g : Fin m → Γ(X, U.1)) (hg : Ideal.span (Set.range g) = J.ideal U)
    (V : Fin m → W.Opens) (hV : ∀ i, V i ≤ π ⁻¹ᵁ U.1)
    (e : ∀ i, (V i).toScheme ≅ Spec (CommRingCat.of (FinalTheorems.reesChart g i)))
    (he : ∀ i, (e i).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (FinalTheorems.reesChart g i))) ≫
      U.2.fromSpec = (V i).ι ≫ π)
    (i j : Fin m) (t : Γ(W, V i))
    (ht : t = (V i).topIso.hom ((e i).hom.appTop ((Scheme.ΓSpecIso _).inv
      ⟨IsLocalization.mk' (Localization.Away (g i)) (g j) (⟨g i, Submonoid.mem_powers _⟩ : Submonoid.powers (g i)),
        Algebra.subset_adjoin ⟨j, rfl⟩⟩))) :
    V i ⊓ V j = W.basicOpen t := by
  classical
  let σ : ∀ k, FinalTheorems.reesChart g k →+* Γ(W, V k) := fun k =>
    (V k).topIso.hom.hom.comp (((e k).hom.appTop).hom.comp
      (Scheme.ΓSpecIso (.of (FinalTheorems.reesChart g k))).inv.hom)
  let q : ∀ k l, FinalTheorems.reesChart g k := fun k l =>
    ⟨IsLocalization.mk' (Localization.Away (g k)) (g l) (⟨g k, Submonoid.mem_powers _⟩ : Submonoid.powers (g k)),
      Algebra.subset_adjoin ⟨l, rfl⟩⟩
  have hq : ∀ k l, algebraMap Γ(X, U.1) (FinalTheorems.reesChart g k) (g l) =
      q k l * algebraMap Γ(X, U.1) (FinalTheorems.reesChart g k) (g k) := fun k l =>
    Subtype.ext (IsLocalization.mk'_spec _ _ _).symm
  have hsec : ∀ k r, σ k (algebraMap _ _ r) = π.appLE _ (V k) (hV k) r := fun k r =>
    sec_algebraMap_of_iso π U (V k) (hV k) _ (e k) (he k) r
  have hP : ∀ k l, π.appLE _ (V k) (hV k) (g l) = σ k (q k l) * π.appLE _ (V k) (hV k) (g k) := by
    intro k l; rw [← hsec, ← hsec, ← map_mul, ← hq]
  have hnz : ∀ k, π.appLE _ (V k) (hV k) (g k) ∈ nonZeroDivisors Γ(W, V k) := by
    intro k
    rw [← hsec]
    apply sec_mem_nonZeroDivisors (V k) (e k)
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    have hu : IsUnit (algebraMap Γ(X, U.1) (Localization.Away (g k)) (g k)) :=
      IsLocalization.Away.algebraMap_isUnit _
    apply Subtype.ext
    exact hu.mul_left_eq_zero.1 (congrArg Subtype.val hx)
  have hti : t = σ i (q i j) := ht
  have hVi : IsAffineOpen (V i) := isAffineOpen_of_iso (V i) (e i)
  apply le_antisymm
  · intro w hw
    have hwi : w ∈ V i := hw.1
    have hwj : w ∈ V j := hw.2
    rw [Scheme.mem_basicOpen W t w hwi, hti]
    have hg : ∀ k l (hwk : w ∈ V k), W.presheaf.germ (V k) w hwk (π.appLE _ (V k) (hV k) (g l)) =
        W.presheaf.germ (π ⁻¹ᵁ U.1) w (hV k hwk) (π.app U.1 (g l)) := by
      intro k l hwk
      simp only [Scheme.Hom.appLE, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]
    have h1 := congrArg (W.presheaf.germ (V i) w hwi) (hP i j)
    have h2 := congrArg (W.presheaf.germ (V j) w hwj) (hP j i)
    rw [map_mul, hg, hg] at h1
    rw [map_mul, hg, hg] at h2
    have hA := germ_mem_nonZeroDivisors hVi (hnz i) w hwi
    rw [hg] at hA
    have h3 : (W.presheaf.germ (V j) w hwj (σ j (q j i)) * W.presheaf.germ (V i) w hwi (σ i (q i j)) - 1) *
        W.presheaf.germ (π ⁻¹ᵁ U.1) w (hV i hwi) (π.app U.1 (g i)) = 0 := by
      rw [sub_mul, one_mul, mul_assoc, ← h1, ← h2, sub_self]
    have h4 := sub_eq_zero.1 ((mem_nonZeroDivisors_iff_right.1 hA) _ h3)
    exact IsUnit.of_mul_eq_one_right _ h4
  · have hD : IsAffineOpen (W.basicOpen t) := hVi.basicOpen t
    have hDle : W.basicOpen t ≤ V i := W.basicOpen_le t
    have hDU : W.basicOpen t ≤ π ⁻¹ᵁ U.1 := hDle.trans (hV i)
    let ρ := W.presheaf.map (homOfLE hDle).op
    let φ := π.appLE U.1 (W.basicOpen t) hDU
    have hφ : ∀ l, φ (g l) = ρ (π.appLE _ (V i) (hV i) (g l)) := fun l => by
      show _ = (π.appLE _ (V i) (hV i) ≫ W.presheaf.map (homOfLE hDle).op) (g l)
      rw [Scheme.Hom.appLE_map]
    have hu : IsUnit (ρ t) := W.toRingedSpace.isUnit_res_basicOpen t
    have key : ∀ (a b u x : Γ(W, W.basicOpen t)), u * x = 1 → a * b = a * u * (x * b) := by
      intro a b u x h; linear_combination (-(a * b)) * h
    have hc : ∀ l, φ.hom (g l) = (ρ (σ i (q i l)) * ↑hu.unit⁻¹) * φ.hom (g j) := by
      intro l
      show φ (g l) = _ * φ (g j)
      rw [hφ, hφ, hP i l, hP i j, ← hti, map_mul, map_mul]
      exact key _ _ _ _ hu.val_inv_mul
    have hnzj : φ.hom (g j) ∈ nonZeroDivisors Γ(W, W.basicOpen t) := by
      show φ (g j) ∈ _
      rw [hφ, hP i j, map_mul, ← hti]
      exact mul_mem hu.mem_nonZeroDivisors (res_mem_nonZeroDivisors hDle hVi (hnz i))
    obtain ⟨ψ, hψ⟩ := reesChart_lift φ.hom g j hnzj _ hc
    let a := hD.fromSpec
    let b := Spec.map (CommRingCat.ofHom ψ) ≫ (e j).inv ≫ (V j).ι
    have hab : b ≫ π = a ≫ π := by
      simp only [a, b, Category.assoc]
      rw [← he j, Iso.inv_hom_id_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hψ,
        ← IsAffineOpen.SpecMap_appLE_fromSpec π U.2 hD hDU]
      rfl
    have hE : FinalTheorems.EffCartier (J.comap (a ≫ π)) := by
      rw [Scheme.IdealSheafData.comap_comp]; exact effCartier_comap_of_isOpenImmersion' _ a hB.1
    obtain ⟨h0, -, huniq⟩ := hB.2 _ (a ≫ π) hE
    have hab' : b = a := (huniq b hab).trans (huniq a rfl).symm
    intro w hw
    have hw' : w ∈ Set.range hD.fromSpec := by rw [hD.range_fromSpec]; exact hw
    obtain ⟨x, rfl⟩ := hw'
    refine ⟨hDle hw, ?_⟩
    change a x ∈ V j
    rw [← hab']
    change (V j).ι ((Spec.map (CommRingCat.ofHom ψ) ≫ (e j).inv) x) ∈ V j
    exact ((Spec.map (CommRingCat.ofHom ψ) ≫ (e j).inv) x).2

end

end ReciprocityTheory.AnForm.R
