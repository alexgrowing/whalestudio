import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.FnOfComp

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isOpenImmersion_of_section_of_etale {X S : Scheme.{0}} (f : X ⟶ S) [Etale f] (s : S ⟶ X)
    (hs : s ≫ f = 𝟙 S) : IsOpenImmersion s := by
  have : Etale (s ≫ f) := by rw [hs]; infer_instance
  have : Etale s := Etale.of_comp s f
  have : Mono s := (SplitMono.mk f hs).mono
  exact IsOpenImmersion.of_flat_of_mono s

theorem exists_section_of_etale {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of K)) [Etale f] (x : X) :
    ∃ s : Spec (CommRingCat.of K) ⟶ X, s ≫ f = 𝟙 _ ∧ x ∈ Set.range s := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  let W : Set X := ⋃ s : {s : Spec (CommRingCat.of K) ⟶ X // s ≫ f = 𝟙 _}, Set.range s.1
  have hW : IsOpen W := isOpen_iUnion fun s => by
    have := isOpenImmersion_of_section_of_etale f s.1 s.2
    exact s.1.isOpenEmbedding.isOpen_range
  have hx : x ∈ W := by
    by_contra hx
    obtain ⟨c, hc, hc'⟩ := nonempty_inter_closedPoints (Z := Wᶜ) ⟨x, hx⟩
      hW.isClosed_compl.isLocallyClosed
    replace hc' : IsClosed {c} := hc'
    exact hc (Set.mem_iUnion.mpr ⟨⟨_, pointOfClosedPoint_comp f c hc'⟩,
      IsLocalRing.closedPoint K, pointOfClosedPoint_apply f c hc' _⟩)
  obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
  exact ⟨s.1, s.2, hs⟩

theorem exists_local_rational_torsion {K : Type} [Field K] [IsAlgClosed K]
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A] (n : ℕ) [Etale (mulA A n).left]
    {Z : Over (Spec (CommRingCat.of K))} (d : Z ⟶ A) (hd : d ^ n = 1) (p : Z.left) :
    ∃ (W : Over (Spec (CommRingCat.of K))) (c : W ⟶ Z) (_ : IsOpenImmersion c.left),
      p ∈ Set.range c.left ∧ ∃ y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A,
        y ^ n = 1 ∧ c ≫ d = toUnit W ≫ y := by
  have hmul : ∀ {Z : Over (Spec (CommRingCat.of K))} (y : Z ⟶ A), y ≫ mulA A n = y ^ n :=
    fun y => by rw [mulA, MonObj.comp_pow, Category.comp_id]
  have hone : ∀ {Z : Over (Spec (CommRingCat.of K))},
      (1 : Z ⟶ A).left = Z.hom ≫ η[A].left := fun {Z} => by
    rw [Hom.one_def, Over.comp_left]; rfl
  have hη : η[A].left ≫ A.hom = 𝟙 _ := Over.w η[A]
  have e : d.left ≫ (mulA A n).left = Z.hom ≫ η[A].left := by
    rw [← Over.comp_left, hmul, hd, hone]
  let l : Z.left ⟶ pullback (mulA A n).left η[A].left := pullback.lift _ _ e
  obtain ⟨s, hs, t, ht⟩ := exists_section_of_etale (K := K)
    (pullback.snd (mulA A n).left η[A].left) (l p)
  have := isOpenImmersion_of_section_of_etale (pullback.snd (mulA A n).left η[A].left) s hs
  have hy : (s ≫ pullback.fst (mulA A n).left η[A].left) ≫ A.hom = 𝟙 _ := by
    rw [← Over.w (mulA A n), Category.assoc, pullback.condition_assoc]
    erw [hη]
    exact (congrArg (s ≫ ·) (Category.comp_id _)).trans hs
  let y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A := Over.homMk _ hy
  refine ⟨Over.mk (pullback.fst l s ≫ Z.hom), Over.homMk (pullback.fst l s) rfl,
    inferInstanceAs (IsOpenImmersion (pullback.fst l s)), ?_, y, ?_, ?_⟩
  · obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := l) (g := s) p t ht.symm
    exact ⟨w, hw⟩
  · rw [← hmul]
    apply Over.OverMorphism.ext
    rw [hone]
    change (s ≫ pullback.fst (mulA A n).left η[A].left) ≫ (mulA A n).left = 𝟙 _ ≫ η[A].left
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ η[A].left) hs
  · apply Over.OverMorphism.ext
    change pullback.fst l s ≫ d.left =
      (pullback.fst l s ≫ Z.hom) ≫ s ≫ pullback.fst (mulA A n).left η[A].left
    have h1 : d.left = l ≫ pullback.fst (mulA A n).left η[A].left := (pullback.lift_fst _ _ _).symm
    have h2 : Z.hom = l ≫ pullback.snd (mulA A n).left η[A].left := (pullback.lift_snd _ _ _).symm
    have h3 : pullback.fst l s ≫ Z.hom = pullback.snd l s := by
      rw [h2, pullback.condition_assoc]
      exact (congrArg (pullback.snd l s ≫ ·) hs).trans (Category.comp_id _)
    rw [h3, h1, pullback.condition_assoc]

theorem existsUnique_appTop_eq_of_flat {X Y : Scheme.{0}} (m : X ⟶ Y) [QuasiCompact m]
    [Surjective m] [Flat m] (f : Γ(X, ⊤))
    (h : ∀ {Z : Scheme.{0}} (a b : Z ⟶ X), a ≫ m = b ≫ m → a ≫ TLinPf.mOf f = b ≫ TLinPf.mOf f) :
    ∃! g : Γ(Y, ⊤), m.appTop.hom g = f := by
  refine ⟨TLinPf.fnOf (EffectiveEpi.desc m (TLinPf.mOf f) h), ?_, ?_⟩
  · beta_reduce
    rw [← TLinPf.fnOf_comp, EffectiveEpi.fac, TLinPf.fnOf_mOf]
  · intro g hg
    rw [← TLinPf.fnOf_mOf g]
    congr 1
    apply EffectiveEpi.uniq
    rw [TLinPf.comp_mOf, hg]

theorem resLE_appTop_topIso_inv {X Y : Scheme.{0}} (t : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (e : V ≤ t ⁻¹ᵁ U) (g : Γ(Y, U)) :
    (t.resLE U V e).appTop.hom (U.topIso.inv.hom g) = V.topIso.inv.hom ((t.appLE U V e).hom g) := by
  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, ← CommRingCat.comp_apply,
    Iso.inv_hom_id_assoc, CommRingCat.comp_apply]

theorem existsUnique_descend_of_torsion_invariant {K : Type} [Field K] [IsAlgClosed K]
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A] (n : ℕ)
    [Etale (mulA A n).left] [Surjective (mulA A n).left] [QuasiCompact (mulA A n).left]
    (U : A.left.Opens) (f : Γ(A.left, (mulA A n).left ⁻¹ᵁ U))
    (hf : ∀ y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A, y ^ n = 1 →
      ∀ (e : (mulA A n).left ⁻¹ᵁ U ≤
        ((toUnit A ≫ y) * 𝟙 A).left ⁻¹ᵁ ((mulA A n).left ⁻¹ᵁ U)),
        (((toUnit A ≫ y) * 𝟙 A).left.appLE _ _ e).hom f = f) :
    ∃! g : Γ(A.left, U), ((mulA A n).left.app U).hom g = f := by
  have hmul : ∀ {Z : Over (Spec (CommRingCat.of K))} (y : Z ⟶ A), y ≫ mulA A n = y ^ n :=
    fun y => by rw [mulA, MonObj.comp_pow, Category.comp_id]
  let m := (mulA A n).left
  have hm : m = (mulA A n).left := rfl
  let V := m ⁻¹ᵁ U
  let f' : Γ(V, ⊤) := V.topIso.inv.hom f
  have key : ∀ {Z : Scheme.{0}} (a b : Z ⟶ V), a ≫ (m ∣_ U) = b ≫ (m ∣_ U) →
      a ≫ TLinPf.mOf f' = b ≫ TLinPf.mOf f' := by
    intro Z a b hab
    have hab' : (a ≫ V.ι) ≫ m = (b ≫ V.ι) ≫ m := by
      rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, reassoc_of% hab]
    have hw : (a ≫ V.ι) ≫ A.hom = (b ≫ V.ι) ≫ A.hom := by
      rw [← Over.w (mulA A n), ← hm, ← Category.assoc, hab', Category.assoc _ m]
    let FinalForm : Over (Spec (CommRingCat.of K)) := Over.mk ((b ≫ V.ι) ≫ A.hom)
    let z₁ : FinalForm ⟶ A := Over.homMk (a ≫ V.ι) hw
    let z₂ : FinalForm ⟶ A := Over.homMk (b ≫ V.ι) rfl
    have hz : z₁ ^ n = z₂ ^ n := by
      rw [← hmul, ← hmul]
      exact Over.OverMorphism.ext hab'
    have hd : (z₁ * z₂⁻¹) ^ n = 1 := by
      rw [mul_pow, inv_pow, hz, mul_inv_cancel]
    have hloc := exists_local_rational_torsion A n _ hd
    choose W c hc hp y hy hcy using hloc
    let 𝒰 : Z.OpenCover := Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) Z (fun p => (W p).left)
      (fun p => (c p).left) (fun p => ⟨p, hp p⟩) hc
    refine Scheme.Cover.hom_ext 𝒰 _ _ fun p => ?_
    change (c p).left ≫ a ≫ _ = (c p).left ≫ b ≫ _
    let t : A ⟶ A := (toUnit A ≫ y p) * 𝟙 A
    have htm : t ≫ mulA A n = mulA A n := by
      rw [hmul, mul_pow, ← MonObj.comp_pow, hy p, MonObj.comp_one, _root_.one_mul]
    have htm' : t.left ≫ m = m := by rw [hm, ← Over.comp_left, htm]
    have e : V ≤ t.left ⁻¹ᵁ V := by
      rw [← Scheme.Hom.comp_preimage, htm']
    have h1 : c p ≫ z₁ = c p ≫ z₂ ≫ t := by
      have h2 := hcy p
      rw [MonObj.comp_mul, GrpObj.comp_inv, mul_inv_eq_iff_eq_mul] at h2
      rw [h2, ← Category.assoc _ z₂, MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]
    have h3 : (c p).left ≫ a = (c p).left ≫ b ≫ t.left.resLE V V e := by
      rw [← cancel_mono V.ι]
      simp only [Category.assoc, Scheme.Hom.resLE_comp_ι]
      have := congr(($h1).left)
      simpa [z₁, z₂] using this
    have h4 : t.left.resLE V V e ≫ TLinPf.mOf f' = TLinPf.mOf f' := by
      rw [TLinPf.comp_mOf]
      congr 1
      exact (resLE_appTop_topIso_inv t.left e f).trans (congrArg _ (hf _ (hy p) e))
    rw [← Category.assoc, h3, Category.assoc, Category.assoc, h4]
  have : Surjective (m ∣_ U) := IsZariskiLocalAtTarget.restrict (P := @Surjective) ‹_› U
  obtain ⟨g, hg, hu⟩ := existsUnique_appTop_eq_of_flat (m ∣_ U) f' key
  have h7 : ∀ g : Γ(A.left, U), (m ∣_ U).appTop.hom (U.topIso.inv.hom g) =
      V.topIso.inv.hom ((m.app U).hom g) := fun g => by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict, resLE_appTop_topIso_inv, Scheme.Hom.appLE_eq_app]
  have hV : Function.Injective V.topIso.inv.hom := V.topIso.symm.commRingCatIsoToRingEquiv.injective
  have hU : Function.Bijective U.topIso.inv.hom := U.topIso.symm.commRingCatIsoToRingEquiv.bijective
  obtain ⟨g, rfl⟩ := hU.2 g
  refine ⟨g, hV ((h7 g).symm.trans hg), fun g' hg' => hU.1 (hu _ ?_)⟩
  exact (h7 g').trans (congrArg _ hg')

theorem torsion_invariant_descends :
    (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n →
      IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧
        (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ),
      (n : K) ≠ 0 → ∀ (U : P.A.left.Opens) (f : Γ(P.A.left, (mulA P.A n).left ⁻¹ᵁ U)),
      (∀ y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P.A, y ^ n = 1 →
        ∀ (e : (mulA P.A n).left ⁻¹ᵁ U ≤
          ((toUnit P.A ≫ y) * 𝟙 P.A).left ⁻¹ᵁ ((mulA P.A n).left ⁻¹ᵁ U)),
          (((toUnit P.A ≫ y) * 𝟙 P.A).left.appLE _ _ e).hom f = f) →
      ∃! g : Γ(P.A.left, U), ((mulA P.A n).left.app U).hom g = f := by
  intro H K _ _ P n hn U f hf
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr fun h => hn (by rw [h, Nat.cast_zero])
  obtain ⟨h1, -, h3, h4⟩ := H _ P n hn1
  have : Etale (mulA P.A n).left := h4 (by
    simpa using (Ne.isUnit hn).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
  have : IsCommMonObj P.A := P.isAb.comm
  exact existsUnique_descend_of_torsion_invariant P.A n U f hf

end GlobalTheory
