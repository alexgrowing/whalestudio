import Development.EtaleCohomology.EtaleSheaves.CechSqPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescIntPf LateralTheory.E.CechSqPf

namespace LateralTheory.E.CechSqPf

def lev0Iso {C D : CommRingCat.{0}} (g : C ⟶ D) : D ≅ widePushout C (fun _ : Fin 1 => D) (fun _ => g) where
  hom := WidePushout.ι (fun _ => g) 0
  inv := WidePushout.desc g (fun _ => 𝟙 D) (fun _ => by simp)
  hom_inv_id := by apply WidePushout.ι_desc
  inv_hom_id := by
    apply WidePushout.hom_ext
    · intro j
      rw [Subsingleton.elim j 0, ← Category.assoc, WidePushout.ι_desc, Category.comp_id, Category.id_comp]
    · rw [← Category.assoc, WidePushout.head_desc, Category.comp_id]
      convert WidePushout.arrow_ι (fun _ : Fin 1 => g) (0 : Fin 1) using 1

theorem Level0_of (h : LevelPush) : Level0 := by
  intro q i A Y C D Y' φ c w φ' g hpo
  have hp := h φ c w φ' g hpo (SimplexCategory.mk 0)
  refine ⟨_, w ≫ (coAug (pushout.inr g φ')).app (SimplexCategory.mk 0),
    (lev0Iso g).hom ≫ (Arrow.mapCechConerve (sqHom g φ')).app (SimplexCategory.mk 0), ?_, fun m hm => ?_⟩
  · refine hp.of_iso (Iso.refl _) (Iso.refl _) (lev0Iso g).symm (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp, Iso.symm_hom, Category.assoc]
      change c ≫ WidePushout.head _ ≫ (lev0Iso g).inv = c ≫ g
      rw [← WidePushout.arrow_ι (fun _ : Fin 1 => g) 0]
      change c ≫ (g ≫ (lev0Iso g).hom) ≫ (lev0Iso g).inv = c ≫ g
      simp
    · simp
    · exact (Category.comp_id _).trans (Iso.inv_hom_id_assoc (lev0Iso g) _).symm
  · have key : sch.map (Spec.map ((lev0Iso g).hom ≫ (Arrow.mapCechConerve (sqHom g φ')).app (SimplexCategory.mk 0))) ≫
        sch.map (Spec.map (lev0Iso g).inv) =
        𝟙 _ ≫ sch.map (Spec.map ((Arrow.mapCechConerve (sqHom g φ')).app (SimplexCategory.mk 0))) := by
      have hring : (lev0Iso g).inv ≫ (lev0Iso g).hom ≫ (Arrow.mapCechConerve (sqHom g φ')).app (SimplexCategory.mk 0) =
          (Arrow.mapCechConerve (sqHom g φ')).app (SimplexCategory.mk 0) := Iso.inv_hom_id_assoc _ _
      rw [← sch.map_comp, ← Spec.map_comp, Category.id_comp]
      exact congrArg (fun f => sch.map (Spec.map f)) hring
    exact RelZS.of_iso (ZMod q) (tw q i) _ _ (Iso.refl _) (sch.mapIso (asIso (Spec.map (lev0Iso g).inv))) key m hm

theorem arrowι {C D : CommRingCat.{0}} (g : C ⟶ D) (n : SimplexCategory) (j : Fin (n.len + 1)) :
    g ≫ (WidePushout.ι (fun _ : Fin (n.len + 1) => g) j : D ⟶ (Arrow.mk g).cechConerve.obj n) = (coAug g).app n :=
  @WidePushout.arrow_ι _ _ _ C (fun _ => D) (fun _ => g) _ j

theorem basePush {C D Y' : CommRingCat.{0}} (g : C ⟶ D) (φ' : C ⟶ Y') (n : SimplexCategory) :
    IsPushout φ' ((coAug g).app n) ((coAug (pushout.inr g φ')).app n)
      ((Arrow.mapCechConerve (sqHom g φ')).app n) := by
  have hw : φ' ≫ (coAug (pushout.inr g φ')).app n =
      (coAug g).app n ≫ (Arrow.mapCechConerve (sqHom g φ')).app n := by
    simp [coAug, sqHom]
    symm; apply WidePushout.head_desc
  refine IsPushout.of_isColimit' ⟨hw⟩ (PushoutCocone.IsColimit.mk _
    (fun s => WidePushout.desc s.inl
      (fun j => pushout.desc ((WidePushout.ι (fun _ : Fin (n.len + 1) => g) j : D ⟶ (Arrow.mk g).cechConerve.obj n) ≫ s.inr) s.inl (by
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ s.inr) (arrowι g n j)).trans s.condition.symm)))
      (fun j => pushout.inr_desc _ _ _)) ?_ ?_ ?_)
  · intro s
    apply WidePushout.head_desc
  · intro s
    apply WidePushout.hom_ext
    · intro j
      have key : (WidePushout.ι (fun _ : Fin (n.len + 1) => g) j : D ⟶ (Arrow.mk g).cechConerve.obj n) ≫
          (Arrow.mapCechConerve (sqHom g φ')).app n = pushout.inl g φ' ≫
          (WidePushout.ι (fun _ : Fin (n.len + 1) => pushout.inr g φ') j :
            _ ⟶ (Arrow.mk (pushout.inr g φ')).cechConerve.obj n) := by
        apply WidePushout.ι_desc
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ _) key).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      erw [WidePushout.ι_desc]
      exact pushout.inl_desc _ _ _
    · refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ _) hw.symm).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      erw [WidePushout.head_desc]
      exact s.condition
  · intro s m h1 h2
    apply WidePushout.hom_ext
    · intro j
      apply pushout.hom_ext
      · erw [WidePushout.ι_desc, pushout.inl_desc]
        rw [← h2]
        have key : (WidePushout.ι (fun _ : Fin (n.len + 1) => g) j : D ⟶ (Arrow.mk g).cechConerve.obj n) ≫
            (Arrow.mapCechConerve (sqHom g φ')).app n = pushout.inl g φ' ≫
            (WidePushout.ι (fun _ : Fin (n.len + 1) => pushout.inr g φ') j :
              _ ⟶ (Arrow.mk (pushout.inr g φ')).cechConerve.obj n) := by
          apply WidePushout.ι_desc
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ m) key.symm).trans (Category.assoc _ _ _))
      · erw [WidePushout.ι_desc, pushout.inr_desc]
        rw [← h1]
        exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ m) (arrowι (pushout.inr g φ') n j))
    · erw [WidePushout.head_desc]
      rw [← h1]
      rfl

theorem LevelPush_of : LevelPush := by
  intro A Y C D Y' φ c w φ' g hpo n
  exact hpo.paste_vert (basePush g φ' n)

theorem integral_surjective_ring_cech_augmentation_etale_eqv : IntegralSurjectiveRingCechAugmentationEtaleEqv := by
  intro hB4 q i C D g hgi hgs hq
  haveI : IsIntegralHom (Spec.map g) := IsIntegralHom.SpecMap_iff.mpr hgi
  haveI : Surjective (Spec.map g) := ⟨fun x => by
    obtain ⟨Q, hQ, hQc⟩ := hgs x.asIdeal x.isPrime
    refine ⟨⟨Q, hQ⟩, ?_⟩
    rw [Spec.map_base]
    exact PrimeSpectrum.ext hQc⟩
  have hq' : IsUnit (q : Γ(Spec C, ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso C).inv.hom
  exact hB4 q (Spec.map g) hq' i

theorem BaseChange_of : BaseChange := by
  intro C D Y' g φ' hgi hgs
  have hp := (isPullback_SpecMap_pushout g φ')
  have hI : IsIntegralHom (Spec.map g) := IsIntegralHom.SpecMap_iff.mpr hgi
  have hS : Surjective (Spec.map g) := ⟨fun x => by
    obtain ⟨Q, hQ, hQc⟩ := hgs x.asIdeal x.isPrime
    refine ⟨⟨Q, hQ⟩, ?_⟩
    rw [Spec.map_base]
    exact PrimeSpectrum.ext hQc⟩
  have hI' : IsIntegralHom (Spec.map (pushout.inr g φ')) := MorphismProperty.of_isPullback (P := @IsIntegralHom) hp hI
  have hS' : Surjective (Spec.map (pushout.inr g φ')) := MorphismProperty.of_isPullback (P := @Surjective) hp hS
  refine ⟨IsIntegralHom.SpecMap_iff.mp hI', fun r hr => ?_⟩
  obtain ⟨y, hy⟩ := hS'.surj ⟨r, hr⟩
  refine ⟨y.asIdeal, y.isPrime, ?_⟩
  have := congrArg PrimeSpectrum.asIdeal hy
  rw [Spec.map_base] at this
  exact this

section helpers
variable {C D : CommRingCat.{0}} (g : C ⟶ D) {J : Type} [HasWidePushout C (fun _ : J => D) (fun _ => g)]

theorem ιd (j : J) {X : CommRingCat.{0}} (f : C ⟶ X) (fs : J → (D ⟶ X)) (w : ∀ j, g ≫ fs j = f) :
    WidePushout.ι (fun _ : J => g) j ≫ WidePushout.desc f fs w = fs j :=
  WidePushout.ι_desc (arrows := fun _ => g) (f := f) (fs := fs) (w := w) j

theorem hd {X : CommRingCat.{0}} (f : C ⟶ X) (fs : J → (D ⟶ X)) (w : ∀ j, g ≫ fs j = f) :
    WidePushout.head (fun _ : J => g) ≫ WidePushout.desc f fs w = f :=
  WidePushout.head_desc (arrows := fun _ => g) (f := f) (fs := fs) (w := w)

theorem ar (j : J) : g ≫ WidePushout.ι (fun _ : J => g) j = WidePushout.head (fun _ : J => g) :=
  WidePushout.arrow_ι (arrows := fun _ : J => g) j

theorem ιd_assoc (j : J) {X Y : CommRingCat.{0}} (f : C ⟶ X) (fs : J → (D ⟶ X)) (w : ∀ j, g ≫ fs j = f) (h : X ⟶ Y) :
    WidePushout.ι (fun _ : J => g) j ≫ WidePushout.desc f fs w ≫ h = fs j ≫ h := by
  rw [← Category.assoc, ιd]

theorem hd_assoc {X Y : CommRingCat.{0}} (f : C ⟶ X) (fs : J → (D ⟶ X)) (w : ∀ j, g ≫ fs j = f) (h : X ⟶ Y) :
    WidePushout.head (fun _ : J => g) ≫ WidePushout.desc f fs w ≫ h = f ≫ h := by
  rw [← Category.assoc, hd]

end helpers

abbrev up {C D : CommRingCat.{0}} (g : C ⟶ D) (k : ℕ) :
    widePushout C (fun _ : Fin (k + 1) => D) (fun _ => g) ⟶ widePushout C (fun _ : Fin (k + 2) => D) (fun _ => g) :=
  WidePushout.desc (WidePushout.head _) (fun i => WidePushout.ι (fun _ : Fin (k + 2) => g) i.castSucc)
    (fun i => ar g i.castSucc)

theorem wp {C D : CommRingCat.{0}} (g : C ⟶ D) (k : ℕ) :
    IsPushout (WidePushout.head (fun _ : Fin (k + 1) => g)) g (up g k)
      (WidePushout.ι (fun _ : Fin (k + 2) => g) (Fin.last _)) := by
  have hw : WidePushout.head (fun _ : Fin (k + 1) => g) ≫ up g k =
      g ≫ WidePushout.ι (fun _ : Fin (k + 2) => g) (Fin.last _) := by
    simp [up, hd, ar]
  refine IsPushout.of_isColimit' ⟨hw⟩ (PushoutCocone.IsColimit.mk _
    (fun s => WidePushout.desc (g ≫ s.inr)
      (fun i => Fin.lastCases s.inr (fun i => WidePushout.ι (fun _ : Fin (k + 1) => g) i ≫ s.inl) i)
      (fun i => by
        induction i using Fin.lastCases with
        | last => simp
        | cast i =>
          simp only [Fin.lastCases_castSucc]
          rw [← Category.assoc, ar]
          exact s.condition)) ?_ ?_ ?_)
  · intro s
    apply WidePushout.hom_ext
    · intro j
      simp [up, ιd, ιd_assoc, hd, hd_assoc]
    · simp [up, ιd, ιd_assoc, hd, hd_assoc]
      exact s.condition.symm
  · intro s
    simp [ιd]
  · intro s m h1 h2
    apply WidePushout.hom_ext
    · intro j
      induction j using Fin.lastCases with
      | last => simpa [ιd] using h2
      | cast i =>
        simp only [WidePushout.ι_desc, Fin.lastCases_castSucc]
        rw [← h1]
        simp [up, ιd, ιd_assoc]
    · simp only [WidePushout.head_desc]
      rw [← h2, ← Category.assoc]
      exact congrArg (· ≫ m) (WidePushout.arrow_ι (fun _ : Fin (k + 2) => g) (Fin.last _)).symm

theorem cechConerve_levelwise : LevelP := by
  intro A P hP C D c g hCc hDc
  have Q : ∀ k : ℕ, P _ (c ≫ WidePushout.head (fun _ : Fin (k + 1) => g)) := by
    intro k
    induction k with
    | zero =>
      have hsq : IsPushout g (𝟙 C) (WidePushout.ι (fun _ : Fin 1 => g) 0) (WidePushout.head (fun _ : Fin 1 => g)) := by
        have : IsIso (WidePushout.ι (fun _ : Fin 1 => g) 0) := (lev0Iso g).isIso_hom
        exact IsPushout.of_vert_isIso ⟨(WidePushout.arrow_ι (fun _ : Fin 1 => g) 0).trans (Category.id_comp _).symm⟩
      have := hP c g (𝟙 C) _ _ hsq hCc hDc (by simpa using hCc)
      rw [WidePushout.arrow_ι (fun _ : Fin 1 => g) 0] at this
      exact this
    | succ k ih =>
      have := hP c _ g _ _ (wp g k) hCc ih hDc
      have e : WidePushout.head (fun _ : Fin (k + 1) => g) ≫ up g k = WidePushout.head (fun _ : Fin (k + 2) => g) :=
        hd g _ _ _
      rw [e] at this
      exact this
  intro n
  exact Q n.len

theorem CechSq_full : CechSq :=
  CechSq_of integral_surjective_ring_cech_augmentation_etale_eqv BaseChange_of LevelPush_of cechConerve_levelwise (Level0_of LevelPush_of)

end LateralTheory.E.CechSqPf

theorem LateralTheory.E.CechSqPf2.CechSq_of : LateralTheory.E.DescIntPf.CechSq := LateralTheory.E.CechSqPf.CechSq_full
