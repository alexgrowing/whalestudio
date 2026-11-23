import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ProdGlue

variable {T T₁ : Scheme.{0}}

theorem isPb (Y : Over T) : IsPullback (fst Y Y).left (snd Y Y).left Y.hom Y.hom :=
  IsPullback.of_hasPullback Y.hom Y.hom

theorem tens_hom (Y : Over T) : (Y ⊗ Y).hom = (fst Y Y).left ≫ Y.hom := (Over.w (fst Y Y)).symm

noncomputable def incl (v : T₁ ⟶ T) (Y : Over T) (Y₁ : Over T₁) (j : Y₁.left ⟶ Y.left)
    (w : j ≫ Y.hom = Y₁.hom ≫ v) : (Y₁ ⊗ Y₁).left ⟶ (Y ⊗ Y).left :=
  (isPb Y).lift ((fst Y₁ Y₁).left ≫ j) ((snd Y₁ Y₁).left ≫ j) (by
    rw [Category.assoc, Category.assoc, w, ← Category.assoc, ← Category.assoc, (isPb Y₁).w])

@[reassoc (attr := simp)] theorem incl_fst (v : T₁ ⟶ T) (Y : Over T) (Y₁ : Over T₁) (j : Y₁.left ⟶ Y.left)
    (w : j ≫ Y.hom = Y₁.hom ≫ v) : incl v Y Y₁ j w ≫ (fst Y Y).left = (fst Y₁ Y₁).left ≫ j :=
  (isPb Y).lift_fst _ _ _

@[reassoc (attr := simp)] theorem incl_snd (v : T₁ ⟶ T) (Y : Over T) (Y₁ : Over T₁) (j : Y₁.left ⟶ Y.left)
    (w : j ≫ Y.hom = Y₁.hom ≫ v) : incl v Y Y₁ j w ≫ (snd Y Y).left = (snd Y₁ Y₁).left ≫ j :=
  (isPb Y).lift_snd _ _ _

theorem incl_pullback (v : T₁ ⟶ T) (Y : Over T) (Y₁ : Over T₁) (j : Y₁.left ⟶ Y.left)
    (h : IsPullback j Y₁.hom Y.hom v) :
    IsPullback (incl v Y Y₁ j h.w) (Y₁ ⊗ Y₁).hom (Y ⊗ Y).hom v := by
  have w : incl v Y Y₁ j h.w ≫ (Y ⊗ Y).hom = (Y₁ ⊗ Y₁).hom ≫ v := by
    rw [tens_hom, tens_hom, incl_fst_assoc, h.w, Category.assoc]
  have e1 : ∀ s : Limits.PullbackCone (Y ⊗ Y).hom v, (s.fst ≫ (fst Y Y).left) ≫ Y.hom = s.snd ≫ v := fun s => by
    rw [Category.assoc, ← tens_hom, s.condition]
  have e2 : ∀ s : Limits.PullbackCone (Y ⊗ Y).hom v, (s.fst ≫ (snd Y Y).left) ≫ Y.hom = s.snd ≫ v := fun s => by
    rw [Category.assoc, ← (isPb Y).w, ← tens_hom, s.condition]
  let lf : ∀ s : Limits.PullbackCone (Y ⊗ Y).hom v, s.pt ⟶ (Y₁ ⊗ Y₁).left := fun s =>
    (isPb Y₁).lift (h.lift (s.fst ≫ (fst Y Y).left) s.snd (e1 s)) (h.lift (s.fst ≫ (snd Y Y).left) s.snd (e2 s))
      (by rw [h.lift_snd, h.lift_snd])
  have lf1 : ∀ s, lf s ≫ (fst Y₁ Y₁).left = h.lift (s.fst ≫ (fst Y Y).left) s.snd (e1 s) :=
    fun s => (isPb Y₁).lift_fst _ _ _
  have lf2 : ∀ s, lf s ≫ (snd Y₁ Y₁).left = h.lift (s.fst ≫ (snd Y Y).left) s.snd (e2 s) :=
    fun s => (isPb Y₁).lift_snd _ _ _
  refine ⟨⟨w⟩, ⟨Limits.PullbackCone.IsLimit.mk w lf ?_ ?_ ?_⟩⟩
  · intro s
    apply (isPb Y).hom_ext
    · rw [Category.assoc, incl_fst, reassoc_of% (lf1 s), h.lift_fst]
    · rw [Category.assoc, incl_snd, reassoc_of% (lf2 s), h.lift_fst]
  · intro s
    rw [tens_hom Y₁, reassoc_of% (lf1 s), h.lift_snd]
  · intro s m hm1 hm2
    rw [tens_hom Y₁] at hm2
    apply (isPb Y₁).hom_ext
    · rw [lf1]
      apply h.hom_ext
      · rw [h.lift_fst, Category.assoc, ← incl_fst v Y Y₁ j h.w, reassoc_of% hm1]
      · rw [h.lift_snd]; simpa only [Category.assoc] using hm2
    · rw [lf2]
      apply h.hom_ext
      · rw [h.lift_fst, Category.assoc, ← incl_snd v Y Y₁ j h.w, reassoc_of% hm1]
      · rw [h.lift_snd, ← hm2, Category.assoc, (isPb Y₁).w]

theorem incl_mul (f : T₁ ⟶ T) (A : Over T) [GrpObj A] (B : Over T₁) [GrpObj B] (φ : B.left ⟶ A.left)
    (h : IsGrpPullback B A f φ) : incl f A B φ h.1.w ≫ (μ[A]).left = (μ[B]).left ≫ φ := by
  let x₀ : Over.mk ((B ⊗ B).hom ≫ f) ⟶ A := Over.homMk ((fst B B).left ≫ φ) (by
    show _ = (B ⊗ B).hom ≫ f
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w])
  let y₀ : Over.mk ((B ⊗ B).hom ≫ f) ⟶ A := Over.homMk ((snd B B).left ≫ φ) (by
    show _ = (B ⊗ B).hom ≫ f
    rw [Category.assoc, h.1.w, ← Category.assoc, ← (isPb B).w, Over.w])
  have hm := h.2 (B ⊗ B) (fst B B) (snd B B) x₀ y₀ rfl rfl
  rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, Over.comp_left] at hm
  have e : incl f A B φ h.1.w = (lift x₀ y₀).left := by
    apply (isPb A).hom_ext
    · rw [incl_fst, ← Over.comp_left, lift_fst]; rfl
    · rw [incl_snd, ← Over.comp_left, lift_snd]; rfl
  rw [e]; exact hm

theorem colim_of_pullbacks {T T₁ T₂ : Scheme.{0}} (v₁ : T₁ ⟶ T) (v₂ : T₂ ⟶ T)
    (hT : Limits.IsColimit (Limits.BinaryCofan.mk v₁ v₂)) (Y : Over T) (Y₁ : Over T₁) (Y₂ : Over T₂)
    (j₁ : Y₁.left ⟶ Y.left) (j₂ : Y₂.left ⟶ Y.left)
    (h₁ : IsPullback j₁ Y₁.hom Y.hom v₁) (h₂ : IsPullback j₂ Y₂.hom Y.hom v₂) :
    Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk (incl v₁ Y Y₁ j₁ h₁.w) (incl v₂ Y Y₂ j₂ h₂.w))) := by
  refine (((BinaryCofan.isVanKampen_iff _).1 (FinitaryExtensive.vanKampen _ hT)
    (Limits.BinaryCofan.mk (incl v₁ Y Y₁ j₁ h₁.w) (incl v₂ Y Y₂ j₂ h₂.w)) (Y₁ ⊗ Y₁).hom (Y₂ ⊗ Y₂).hom (Y ⊗ Y).hom
    ?_ ?_).2 ⟨incl_pullback v₁ Y Y₁ j₁ h₁, incl_pullback v₂ Y Y₂ j₂ h₂⟩)
  · exact (incl_pullback v₁ Y Y₁ j₁ h₁).w.symm
  · exact (incl_pullback v₂ Y Y₂ j₂ h₂).w.symm

end GlobalTheory.ProdGlue

open GlobalTheory.ProdGlue in
theorem GlobalTheory.ProdGlue.mul_glue : ∀ {S S₁ S₂ T T₁ T₂ : Scheme.{0}} (u₁ : S₁ ⟶ S) (u₂ : S₂ ⟶ S), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk u₁ u₂)) → ∀ (v₁ : T₁ ⟶ T) (v₂ : T₂ ⟶ T), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk v₁ v₂)) → ∀ (f₁ : T₁ ⟶ S₁) (f₂ : T₂ ⟶ S₂) (A₁ : Over S₁) [GrpObj A₁] (A₂ : Over S₂) [GrpObj A₂] (B₁ : Over T₁) [GrpObj B₁] (B₂ : Over T₂) [GrpObj B₂] (A₀ : Over T) [GrpObj A₀] (i₁ : B₁.left ⟶ A₁.left) (i₂ : B₂.left ⟶ A₂.left) (j₁ : B₁.left ⟶ A₀.left) (j₂ : B₂.left ⟶ A₀.left), IsGrpPullback B₁ A₁ f₁ i₁ → IsGrpPullback B₂ A₂ f₂ i₂ → IsGrpPullback B₁ A₀ v₁ j₁ → IsGrpPullback B₂ A₀ v₂ j₂ → ∀ (i : A₀.left ⟶ A₁.left ⨿ A₂.left), j₁ ≫ i = i₁ ≫ Limits.coprod.inl → j₂ ≫ i = i₂ ≫ Limits.coprod.inr → ∃ m : Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)) ⊗ Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)) ⟶ Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)), ∀ l : (A₀ ⊗ A₀).left ⟶ (Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)) ⊗ Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂))).left, l ≫ (fst (Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂))) (Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)))).left = (fst A₀ A₀).left ≫ i → l ≫ (snd (Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂))) (Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)))).left = (snd A₀ A₀).left ≫ i → l ≫ m.left = (μ[A₀]).left ≫ i := by

  intro S S₁ S₂ T T₁ T₂ u₁ u₂ ⟨hS⟩ v₁ v₂ ⟨hT⟩ f₁ f₂ A₁ _ A₂ _ B₁ _ B₂ _ A₀ _ i₁ i₂ j₁ j₂ hi₁ hi₂ hj₁ hj₂ i ei₁ ei₂
  set X := Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)) with hX
  have hV := (BinaryCofan.isVanKampen_iff _).1 (FinitaryExtensive.vanKampen _ hS)
    (Limits.BinaryCofan.mk (Limits.coprod.inl : A₁.left ⟶ A₁.left ⨿ A₂.left) Limits.coprod.inr) A₁.hom A₂.hom X.hom
    (Limits.coprod.inl_desc _ _).symm (Limits.coprod.inr_desc _ _).symm
  have pX : _ := hV.1 ⟨Limits.coprodIsCoprod _ _⟩
  have pX₁ : IsPullback (Limits.coprod.inl : A₁.left ⟶ A₁.left ⨿ A₂.left) A₁.hom X.hom u₁ := pX.1
  have pX₂ : IsPullback (Limits.coprod.inr : A₂.left ⟶ A₁.left ⨿ A₂.left) A₂.hom X.hom u₂ := pX.2
  obtain ⟨cX⟩ := colim_of_pullbacks u₁ u₂ hS X A₁ A₂ _ _ pX₁ pX₂
  obtain ⟨c0⟩ := colim_of_pullbacks v₁ v₂ hT A₀ B₁ B₂ _ _ hj₁.1 hj₂.1
  have D := Limits.BinaryCofan.IsColimit.desc' cX
    ((μ[A₁]).left ≫ Limits.coprod.inl) ((μ[A₂]).left ≫ Limits.coprod.inr)
  let ml : (X ⊗ X).left ⟶ X.left := D.1
  have hm₁ : incl u₁ X A₁ Limits.coprod.inl pX₁.w ≫ ml = (μ[A₁]).left ≫ Limits.coprod.inl := D.2.1
  have hm₂ : incl u₂ X A₂ Limits.coprod.inr pX₂.w ≫ ml = (μ[A₂]).left ≫ Limits.coprod.inr := D.2.2
  have hw : ml ≫ X.hom = (X ⊗ X).hom := by
    apply Limits.BinaryCofan.IsColimit.hom_ext cX
    · change incl u₁ X A₁ Limits.coprod.inl pX₁.w ≫ ml ≫ X.hom = incl u₁ X A₁ Limits.coprod.inl pX₁.w ≫ (X ⊗ X).hom
      rw [← Category.assoc, hm₁, Category.assoc, tens_hom, incl_fst_assoc]
      simp only [X, Over.mk_hom, Limits.coprod.inl_desc]
      rw [← Category.assoc, Over.w, ← Category.assoc, Over.w]
    · change incl u₂ X A₂ Limits.coprod.inr pX₂.w ≫ ml ≫ X.hom = incl u₂ X A₂ Limits.coprod.inr pX₂.w ≫ (X ⊗ X).hom
      rw [← Category.assoc, hm₂, Category.assoc, tens_hom, incl_fst_assoc]
      simp only [X, Over.mk_hom, Limits.coprod.inr_desc]
      rw [← Category.assoc, Over.w, ← Category.assoc, Over.w]
  refine ⟨Over.homMk ml hw, fun l hl₁ hl₂ => ?_⟩
  change l ≫ ml = _
  have key : ∀ {Tk Sk : Scheme.{0}} (vk : Tk ⟶ T) (uk : Sk ⟶ S) (fk : Tk ⟶ Sk) (Ak : Over Sk) [GrpObj Ak]
      (Bk : Over Tk) [GrpObj Bk] (ik : Bk.left ⟶ Ak.left) (jk : Bk.left ⟶ A₀.left) (ink : Ak.left ⟶ X.left)
      (hik : IsGrpPullback Bk Ak fk ik) (hjk : IsGrpPullback Bk A₀ vk jk) (eik : jk ≫ i = ik ≫ ink)
      (κ : (Ak ⊗ Ak).left ⟶ (X ⊗ X).left)
      (κf : κ ≫ (fst X X).left = (fst Ak Ak).left ≫ ink) (κs : κ ≫ (snd X X).left = (snd Ak Ak).left ≫ ink)
      (hmk : κ ≫ ml = (μ[Ak]).left ≫ ink),
      incl vk A₀ Bk jk hjk.1.w ≫ l ≫ ml = incl vk A₀ Bk jk hjk.1.w ≫ (μ[A₀]).left ≫ i := by
    intro Tk Sk vk uk fk Ak _ Bk _ ik jk ink hik hjk eik κ κf κs hmk
    have e : incl vk A₀ Bk jk hjk.1.w ≫ l = incl fk Ak Bk ik hik.1.w ≫ κ := by
      apply (isPb X).hom_ext
      · rw [Category.assoc, hl₁, incl_fst_assoc, eik, Category.assoc, κf, incl_fst_assoc]
      · rw [Category.assoc, hl₂, incl_snd_assoc, eik, Category.assoc, κs, incl_snd_assoc]
    rw [reassoc_of% e, hmk, reassoc_of% (incl_mul fk Ak Bk ik hik), reassoc_of% (incl_mul vk A₀ Bk jk hjk), eik]
  apply Limits.BinaryCofan.IsColimit.hom_ext c0
  · exact key v₁ u₁ f₁ A₁ B₁ i₁ j₁ _ hi₁ hj₁ ei₁ _ (incl_fst _ _ _ _ _) (incl_snd _ _ _ _ _) hm₁
  · exact key v₂ u₂ f₂ A₂ B₂ i₂ j₂ _ hi₂ hj₂ ei₂ _ (incl_fst _ _ _ _ _) (incl_snd _ _ _ _ _) hm₂
