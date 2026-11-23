import Development.EtaleCohomology.EtaleSheaves.CechLevelsGeneration.CechLevelIso
import Development.EtaleCohomology.EtaleSheaves.CechLevelIsomorphism.BaseChangeLimit

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.TruncCokPf LateralTheory.E.LevelsPf.Tp Opposite LateralTheory.E.CechLevelIsoPf.Gen

namespace LateralTheory.E.CechLevelIsoPf

abbrev y {A B : CommRingCat.{0}} (f : A ⟶ B) := yoneda.map (Spec.map f)

lemma y_comp {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C) : y (f ≫ g) = y g ≫ y f := by
  simp [y]

lemma ypb {A B C P : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C} {inl : B ⟶ P} {inr : C ⟶ P}
    (h : IsPushout f g inl inr) : IsPullback (y inl) (y inr) (y f) (y g) :=
  (isPullback_SpecMap_of_isPushout f g inl inr h).map yoneda

lemma mk_congr {C : Type*} [Category C] {ι : Type*} {S X W : C} {f : X ⟶ S} {b b' : W ⟶ S}
    {π π' : ι → (W ⟶ X)} (hb : b = b') (hπ : π = π') (h : ∀ i, π i ≫ f = b) (h' : ∀ i, π' i ≫ f = b') :
    WidePullbackCone.mk (f := fun _ : ι => f) b π h = WidePullbackCone.mk (f := fun _ : ι => f) b' π' h' := by
  subst hb; subst hπ; rfl

def lim0 {C : Type*} [Category C] {S X : C} (f : X ⟶ S) :
    IsLimit (WidePullbackCone.mk (f := fun _ : Fin 1 => f) f (fun _ => 𝟙 X) (fun _ => Category.id_comp f)) := by
  refine WidePullbackCone.IsLimit.mk _ (fun t => t.π 0) ?_ ?_ ?_
  · intro t
    have : t.π 0 ≫ f = t.base := WidePullbackCone.condition t 0
    exact this
  · intro t i
    have : t.π 0 ≫ 𝟙 X = t.π i := by rw [Category.comp_id, Subsingleton.elim i 0]
    exact this
  · intro t m _ hπ
    have key : ∀ m : t.pt ⟶ X, m ≫ 𝟙 X = t.π 0 → m = t.π 0 := fun m h => by rwa [Category.comp_id] at h
    exact key m (hπ 0)

def ι {D E : CommRingCat.{0}} (e : D ⟶ E) : (p : ℕ) → Fin (p+1) → (E ⟶ (tp e p).1)
  | 0 => fun _ => 𝟙 E
  | p+1 => Fin.lastCases (pushout.inr (tp e p).2 e) (fun i => ι e p i ≫ pushout.inl (tp e p).2 e)

lemma ι_zero {D E : CommRingCat.{0}} (e : D ⟶ E) (i : Fin 1) : ι e 0 i = 𝟙 E := rfl

lemma ι_last {D E : CommRingCat.{0}} (e : D ⟶ E) (p : ℕ) :
    ι e (p+1) (Fin.last _) = pushout.inr (tp e p).2 e := by
  first | rfl | (dsimp only [ι]; exact Fin.lastCases_last) | (dsimp only [ι]; rw [Fin.lastCases_last])

lemma ι_cast {D E : CommRingCat.{0}} (e : D ⟶ E) (p : ℕ) (i : Fin (p+1)) :
    ι e (p+1) (Fin.castSucc i) = ι e p i ≫ pushout.inl (tp e p).2 e := by
  first | rfl | (dsimp only [ι]; exact Fin.lastCases_castSucc i) | (dsimp only [ι]; rw [Fin.lastCases_castSucc])

lemma ι_w {D E : CommRingCat.{0}} (e : D ⟶ E) : ∀ (p : ℕ) (i : Fin (p+1)), e ≫ ι e p i = (tp e p).2
  | 0, i => Category.comp_id e
  | p+1, i => by
    induction i using Fin.lastCases with
    | last => rw [ι_last]; exact pushout.condition.symm
    | cast i =>
      rw [ι_cast]
      show e ≫ ι e p i ≫ pushout.inl _ _ = (tp e p).2 ≫ pushout.inl _ _
      rw [← Category.assoc, ι_w e p i]

lemma hπE {D E : CommRingCat.{0}} (e : D ⟶ E) (p : ℕ) (i : Fin (p+1)) : y (ι e p i) ≫ y e = y (tp e p).2 := by
  rw [← y_comp, ι_w]

def limE {D E : CommRingCat.{0}} (e : D ⟶ E) : ∀ p : ℕ,
    IsLimit (WidePullbackCone.mk (f := fun _ : Fin (p+1) => y e) (y (tp e p).2) (fun i => y (ι e p i)) (hπE e p))
  | 0 => cast (congrArg IsLimit (mk_congr rfl (funext fun i => (show y (𝟙 E) = 𝟙 _ by simp [y]).symm) _ _)) (lim0 (y e))
  | p+1 => by
    have hpb := ypb (IsPushout.of_hasPushout (tp e p).2 e)
    have h' : ∀ i, (Fin.lastCases (y (pushout.inr (tp e p).2 e)) (fun i => y (pushout.inl (tp e p).2 e) ≫ y (ι e p i)) i :
        _ ⟶ _) ≫ y e = y (pushout.inl (tp e p).2 e) ≫ y (tp e p).2 := by
      intro i
      induction i using Fin.lastCases with
      | last => rw [Fin.lastCases_last]; exact hpb.w.symm
      | cast i => rw [Fin.lastCases_castSucc, Category.assoc, hπE]
    have := stepLimit (fun i => y (ι e p i)) (hπE e p) (limE e p) _ _ hpb h'
    refine cast (congrArg IsLimit (mk_congr ?_ ?_ _ _)) this
    · exact (y_comp _ _).symm
    · funext i
      induction i using Fin.lastCases with
      | last => rw [Fin.lastCases_last, ι_last]; rfl
      | cast i => rw [Fin.lastCases_castSucc, ι_cast]; exact (y_comp _ _).symm

section Y
variable {D E Y' Y'' : CommRingCat.{0}} {e : D ⟶ E} {φ' : D ⟶ Y'} {u : Y' ⟶ Y''} {φ'' : E ⟶ Y''}

def κ (hpo : IsPushout φ' e u φ'') (p : ℕ) (i : Fin (p+1)) : Y'' ⟶ pushout φ' (tp e p).2 :=
  hpo.desc (pushout.inl _ _) (ι e p i ≫ pushout.inr _ _) (by rw [← Category.assoc, ι_w]; exact pushout.condition)

lemma hπY (hpo : IsPushout φ' e u φ'') (p : ℕ) (i : Fin (p+1)) :
    y (κ hpo p i) ≫ y u = y (pushout.inl φ' (tp e p).2) := by
  rw [← y_comp, κ, hpo.inl_desc]

lemma hgi (hpo : IsPushout φ' e u φ'') (p : ℕ) (i : Fin (p+1)) :
    y (κ hpo p i) ≫ y φ'' = y (pushout.inr φ' (tp e p).2) ≫ y (ι e p i) := by
  rw [← y_comp, κ, hpo.inr_desc, y_comp]

def limY (hpo : IsPushout φ' e u φ'') (p : ℕ) :
    IsLimit (WidePullbackCone.mk (f := fun _ : Fin (p+1) => y u) (y (pushout.inl φ' (tp e p).2))
      (fun i => y (κ hpo p i)) (hπY hpo p)) :=
  baseChangeLimit (fun i => y (ι e p i)) (hπE e p) (limE e p) (ypb hpo).flip
    (ypb (IsPushout.of_hasPushout φ' (tp e p).2)).flip (fun i => y (κ hpo p i)) (hπY hpo p) (hgi hpo p)

end Y

theorem CechLevelIso_of : LateralTheory.E.LevelsPf.Tp.CechLevelIso := by
  intro p D E Y' Y'' e φ' u φ'' hpo
  let R := (limE e p).conePointUniqueUpToIso (limit.isLimit _)
  let L := (limY hpo p).conePointUniqueUpToIso (limit.isLimit _)
  have hR : ∀ j, R.hom ≫ WidePullback.π (fun _ : Fin (p+1) => y e) j = y (ι e p j) := fun j =>
    (limE e p).conePointUniqueUpToIso_hom_comp (limit.isLimit _) (some j)
  have hRb : R.hom ≫ WidePullback.base (fun _ : Fin (p+1) => y e) = y (tp e p).2 :=
    (limE e p).conePointUniqueUpToIso_hom_comp (limit.isLimit _) none
  have hL : ∀ j, L.hom ≫ WidePullback.π (fun _ : Fin (p+1) => y u) j = y (κ hpo p j) := fun j =>
    (limY hpo p).conePointUniqueUpToIso_hom_comp (limit.isLimit _) (some j)
  have hLb : L.hom ≫ WidePullback.base (fun _ : Fin (p+1) => y u) = y (pushout.inl φ' (tp e p).2) :=
    (limY hpo p).conePointUniqueUpToIso_hom_comp (limit.isLimit _) none
  have hw : L.hom ≫ (Arrow.mapCechNerve (sq e φ' u φ'' hpo.w)).app (op (SimplexCategory.mk p)) =
      y (pushout.inr φ' (tp e p).2) ≫ R.hom := by
    apply WidePullback.hom_ext
    · intro j
      simp only [Arrow.mapCechNerve_app, Category.assoc, WidePullback.lift_π]
      have key : (L.hom ≫ WidePullback.π (fun _ : Fin (p+1) => y u) j) ≫ y φ'' =
          y (pushout.inr φ' (tp e p).2) ≫ R.hom ≫ WidePullback.π (fun _ : Fin (p+1) => y e) j := by
        exact (congrArg (· ≫ y φ'') (hL j)).trans ((hgi hpo p j).trans
          (congrArg (y (pushout.inr φ' (tp e p).2) ≫ ·) (hR j).symm))
      rw [← Category.assoc]
      exact key
    · simp only [Arrow.mapCechNerve_app, Category.assoc, WidePullback.lift_base]
      have key : (L.hom ≫ WidePullback.base (fun _ : Fin (p+1) => y u)) ≫ y φ' =
          y (pushout.inr φ' (tp e p).2) ≫ R.hom ≫ WidePullback.base (fun _ : Fin (p+1) => y e) := by
        exact (congrArg (· ≫ y φ') hLb).trans (((ypb (IsPushout.of_hasPushout φ' (tp e p).2)).w).trans
          (congrArg (y (pushout.inr φ' (tp e p).2) ≫ ·) hRb.symm))
      rw [← Category.assoc]
      exact key
  exact ⟨(Arrow.isoMk (f := Arrow.mk (y (pushout.inr φ' (tp e p).2)))
    (g := Arrow.mk ((Arrow.mapCechNerve (sq e φ' u φ'' hpo.w)).app (op (SimplexCategory.mk p)))) L R hw).symm⟩

end LateralTheory.E.CechLevelIsoPf
