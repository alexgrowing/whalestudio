import Development.EtaleCohomology.EtaleSheaves.KummerInduction.StepKOf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ContPf LateralTheory.E.ContStepPf LateralTheory.E.StepKPf
  LateralTheory.E.StepKPf.ChasePf

namespace LateralTheory.E.ChaseBPf

attribute [reassoc] rL_ι rD_ι

theorem pc {R : Type} [CommRing R] {A B C : Scheme.{0}} (a : A ⟶ B) (b : B ⟶ C) (F : Shv R) (n : ℤ)
    (x : H R (sch.obj C) F n) :
    pull R (sch.map (a ≫ b)) F n x = pull R (sch.map a) F n (pull R (sch.map b) F n x) := by
  rw [Functor.map_comp, pull_comp]

theorem pbInf {Y : Scheme.{0}} (A B C : Y.Opens) (hA : C ≤ A) (hB : C ≤ B) (hC : C = A ⊓ B) :
    IsPullback (Y.homOfLE hA) (Y.homOfLE hB) A.ι B.ι := by
  subst hC; exact isPullback_opens_inf A B

theorem cover {Y : Scheme.{0}} (A B : Y.Opens) (h : A ⊔ B = ⊤) :
    Set.range A.ι ∪ Set.range B.ι = Set.univ := by
  rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι, ← TopologicalSpace.Opens.coe_sup, h,
    TopologicalSpace.Opens.coe_top]

variable {J : Type} [SmallCategory J]

theorem lv_inf (D : J ⥤ Scheme.{0}) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U V : X.Opens) {k : J}
    (f : k ⟶ j0) : lv D e (U ⊓ V) f = lv D e U f ⊓ lv D e V f := Scheme.Hom.preimage_inf _

theorem lm_inf {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U V : X.Opens) :
    lm c e (U ⊓ V) = lm c e U ⊓ lm c e V := Scheme.Hom.preimage_inf _

theorem lv_sup (D : J ⥤ Scheme.{0}) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U V : X.Opens) (h : U ⊔ V = ⊤)
    {k : J} (f : k ⟶ j0) : lv D e U f ⊔ lv D e V f = ⊤ := by
  rw [lv, lv, ← Scheme.Hom.preimage_sup, h, Scheme.Hom.preimage_top]

theorem lm_sup {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U V : X.Opens)
    (h : U ⊔ V = ⊤) : lm c e U ⊔ lm c e V = ⊤ := by
  rw [lm, lm, ← Scheme.Hom.preimage_sup, h, Scheme.Hom.preimage_top]

def kv (D : J ⥤ Scheme.{0}) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U V : X.Opens) {k : J} (f : k ⟶ j0) :
    (lv D e (U ⊓ V) f).toScheme ≅ pullback (lv D e U f).ι (lv D e V f).ι :=
  (pbInf _ _ _ ((lv_inf D e U V f).le.trans inf_le_left) ((lv_inf D e U V f).le.trans inf_le_right)
    (lv_inf D e U V f)).isoPullback

def km {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U V : X.Opens) :
    (lm c e (U ⊓ V)).toScheme ≅ pullback (lm c e U).ι (lm c e V).ι :=
  (pbInf _ _ _ ((lm_inf c e U V).le.trans inf_le_left) ((lm_inf c e U V).le.trans inf_le_right)
    (lm_inf c e U V)).isoPullback

def pm (D : J ⥤ Scheme.{0}) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U V : X.Opens) {k l : J} (f : k ⟶ j0)
    (g : l ⟶ k) : pullback (lv D e U (g ≫ f)).ι (lv D e V (g ≫ f)).ι ⟶ pullback (lv D e U f).ι (lv D e V f).ι :=
  pullback.map _ _ _ _ (rD D e U f g) (rD D e V f g) (D.map g) (rD_ι D e U f g).symm (rD_ι D e V f g).symm

def pL {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U V : X.Opens) {k : J}
    (f : k ⟶ j0) : pullback (lm c e U).ι (lm c e V).ι ⟶ pullback (lv D e U f).ι (lv D e V f).ι :=
  pullback.map _ _ _ _ (rL c e U f) (rL c e V f) (c.π.app k) (rL_ι c e U f).symm (rL_ι c e V f).symm

@[reassoc]
theorem rL_rD {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U : X.Opens) {k l : J}
    (f : k ⟶ j0) (g : l ⟶ k) : rL c e U (g ≫ f) ≫ rD D e U f g = rL c e U f := by
  rw [← cancel_mono (lv D e U f).ι, Category.assoc, rD_ι, rL_ι_assoc, c.w, rL_ι]

theorem pL_pm {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U V : X.Opens)
    {k l : J} (f : k ⟶ j0) (g : l ⟶ k) : pL c e U V (g ≫ f) ≫ pm D e U V f g = pL c e U V f := by
  apply pullback.hom_ext <;> simp only [pL, pm, pullback.map] <;> simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_snd, pullback.lift_snd_assoc, IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_hom_snd_assoc, rL_ι, rL_ι_assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι_assoc, rD_ι, rD_ι_assoc, rL_rD, rL_rD_assoc]

theorem km_pL {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U V : X.Opens)
    {k : J} (f : k ⟶ j0) : (km c e U V).hom ≫ pL c e U V f = rL c e (U ⊓ V) f ≫ (kv D e U V f).hom := by
  apply pullback.hom_ext
  · rw [← cancel_mono (lv D e U f).ι]
    simp only [pL, km, kv, pullback.map, Category.assoc]
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_snd, pullback.lift_snd_assoc, IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_hom_snd_assoc, rL_ι, rL_ι_assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι_assoc, rD_ι, rD_ι_assoc, rL_rD, rL_rD_assoc]
  · rw [← cancel_mono (lv D e V f).ι]
    simp only [pL, km, kv, pullback.map, Category.assoc]
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_snd, pullback.lift_snd_assoc, IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_hom_snd_assoc, rL_ι, rL_ι_assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι_assoc, rD_ι, rD_ι_assoc, rL_rD, rL_rD_assoc]

theorem kv_pm (D : J ⥤ Scheme.{0}) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U V : X.Opens) {k l : J}
    (f : k ⟶ j0) (g : l ⟶ k) : (kv D e U V (g ≫ f)).hom ≫ pm D e U V f g = rD D e (U ⊓ V) f g ≫ (kv D e U V f).hom := by
  apply pullback.hom_ext
  · rw [← cancel_mono (lv D e U f).ι]
    simp only [pm, kv, pullback.map, Category.assoc]
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_snd, pullback.lift_snd_assoc, IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_hom_snd_assoc, rL_ι, rL_ι_assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι_assoc, rD_ι, rD_ι_assoc, rL_rD, rL_rD_assoc]
  · rw [← cancel_mono (lv D e V f).ι]
    simp only [pm, kv, pullback.map, Category.assoc]
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_snd, pullback.lift_snd_assoc, IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_hom_snd_assoc, rL_ι, rL_ι_assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι_assoc, rD_ι, rD_ι_assoc, rL_rD, rL_rD_assoc]

theorem pL_fst {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U V : X.Opens) {k : J}
    (f : k ⟶ j0) : pL c e U V f ≫ pullback.fst _ _ = pullback.fst _ _ ≫ rL c e U f := pullback.lift_fst _ _ _

theorem pL_snd {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U V : X.Opens) {k : J}
    (f : k ⟶ j0) : pL c e U V f ≫ pullback.snd _ _ = pullback.snd _ _ ≫ rL c e V f := pullback.lift_snd _ _ _

theorem liftR {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U : X.Opens) {q : ℕ}
    {n i : ℤ} {k1 l : J} (f1 : k1 ⟶ j0) (a1 : Ht q (sch.obj (lv D e U f1).toScheme) n i) (g1 : l ⟶ k1) (φ : l ⟶ j0)
    (h : g1 ≫ f1 = φ) : ∃ a' : Ht q (sch.obj (lv D e U φ).toScheme) n i,
      pull _ (sch.map (rL c e U φ)) _ _ a' = pull _ (sch.map (rL c e U f1)) _ _ a1 := by
  subst h
  exact ⟨pull _ (sch.map (rD D e U f1 g1)) _ _ a1, by rw [← pc, rL_rD]⟩

theorem cone3 [IsCofiltered J] {j0 k k1 k2 : J} (f : k ⟶ j0) (f1 : k1 ⟶ j0) (f2 : k2 ⟶ j0) :
    ∃ (l : J) (g : l ⟶ k) (g1 : l ⟶ k1) (g2 : l ⟶ k2), g1 ≫ f1 = g ≫ f ∧ g2 ≫ f2 = g ≫ f := by
  obtain ⟨l1, g, g1, h1⟩ := IsCofiltered.cospan f f1
  obtain ⟨l, h, g2, h2⟩ := IsCofiltered.cospan (g ≫ f) f2
  exact ⟨l, h ≫ g, h ≫ g1, g2, by rw [Category.assoc, Category.assoc, h1], by rw [Category.assoc, h2]⟩

theorem ChaseB_of : ChaseB := by
  intro h hmv q J _ _ D c hc j0 X e U V hUV rU rV rW n i k f y hy hyU hyV
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  obtain ⟨δ, hex, hnat⟩ := hmv h (ZMod q) (tw q i)
  have cv : ∀ {l : J} (φ : l ⟶ j0), Set.range (lv D e U φ).ι ∪ Set.range (lv D e V φ).ι = Set.univ :=
    fun φ => cover _ _ (lv_sup D e U V hUV φ)
  have cL : Set.range (lm c e U).ι ∪ Set.range (lm c e V).ι = Set.univ := cover _ _ (lm_sup c e U V hUV)
  have hpm : ∀ {k l : J} (f : k ⟶ j0) (g : l ⟶ k) w, δ _ _ m (pull _ (sch.map (pm D e U V f g)) _ _ w) =
      pull _ (sch.map (D.map g)) _ _ (δ _ _ m w) := fun f g w =>
    hnat _ _ _ _ (cv _) (cv f) _ _ _ (rD_ι D e U f g).symm (rD_ι D e V f g).symm m w
  obtain ⟨w, hw⟩ := ((hex _ _ (cv f) m).2.2 y).1 ⟨hyU, hyV⟩
  have hinf : δ (lm c e U).ι (lm c e V).ι m (pull _ (sch.map (pL c e U V f)) _ _ w) = 0 :=
    (hnat _ _ _ _ cL (cv f) _ _ _ (rL_ι c e U f).symm (rL_ι c e V f).symm m w).trans (by rw [hw]; exact hy)
  obtain ⟨a, b, hab⟩ := ((hex _ _ cL m).2.1 _).1 hinf
  obtain ⟨k1, f1, a1, ha1⟩ := (rU m i).1 a
  obtain ⟨k2, f2, b1, hb1⟩ := (rV m i).1 b
  obtain ⟨l, g, g1, g2, h1, h2⟩ := cone3 f f1 f2
  obtain ⟨a', ha'⟩ := liftR c e U f1 a1 g1 (g ≫ f) h1
  obtain ⟨b', hb'⟩ := liftR c e V f2 b1 g2 (g ≫ f) h2
  set z := pull _ (sch.map (pm D e U V f g)) _ _ w - (pull _ (sch.map (pullback.fst _ _)) _ _ a' -
    pull _ (sch.map (pullback.snd _ _)) _ _ b') with hz_def
  have hz : pull _ (sch.map (pL c e U V (g ≫ f))) _ _ z = 0 := by
    rw [hz_def, map_sub, map_sub, ← pc, pL_pm, ← pc, ← pc, pL_fst, pL_snd, pc, pc, ha', hb', ha1, hb1, hab, sub_self]
  have hδz : δ _ _ m z = pull _ (sch.map (D.map g)) _ _ y := by
    rw [hz_def, map_sub, ((hex _ _ (cv (g ≫ f)) m).2.1 _).2 ⟨a', b', rfl⟩, sub_zero, hpm, hw]
  have hz' : pull _ (sch.map (rL c e (U ⊓ V) (g ≫ f))) _ _ (pull _ (sch.map (kv D e U V (g ≫ f)).hom) _ _ z) = 0 := by
    rw [← pc, ← km_pL, pc, hz, map_zero]
  obtain ⟨l2, g', hg'⟩ := (rW m i).2 l (g ≫ f) _ hz'
  have hzz : pull _ (sch.map (pm D e U V (g ≫ f) g')) _ _ z = 0 := by
    have e0 : pm D e U V (g ≫ f) g' =
        (kv D e U V (g' ≫ g ≫ f)).inv ≫ rD D e (U ⊓ V) (g ≫ f) g' ≫ (kv D e U V (g ≫ f)).hom := by
      rw [← kv_pm, Iso.inv_hom_id_assoc]
    rw [e0, pc, pc, hg', map_zero]
  refine ⟨l2, g' ≫ g, ?_⟩
  have e1 := hpm (g ≫ f) g' z
  rw [hzz, map_zero, hδz, ← pc] at e1
  rw [D.map_comp]
  exact e1.symm

end LateralTheory.E.ChaseBPf
