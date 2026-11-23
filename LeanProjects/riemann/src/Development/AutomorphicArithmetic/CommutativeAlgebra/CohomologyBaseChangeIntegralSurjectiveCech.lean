import Mathlib
import Development.EtaleCohomology.EtaleSheaves.LineHigh
import Development.EtaleCohomology.EtaleSheaves.DescIntPf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLevelRepresentable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCechNerveBaseChangeIsPullback

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.DescIntPf

private theorem level_rel {Y X Y₀ S S₀ L : Scheme.{0}} (k : Y ⟶ X) (r : X ⟶ S) (c : S₀ ⟶ S)
    (k₀ : Y₀ ⟶ pullback r c) (m : cech k₀ ⟶ cech k)
    (hm : IsPullback m (cechAug k₀) (cechAug k) (sch.map (pullback.fst r c)))
    (p : SimplexCategoryᵒᵖ) (l : L ⟶ X) (e : yoneda.obj L ≅ (cech k).obj p)
    (he : e.hom ≫ (cechAug k).app p = yoneda.map l) (q : ℕ) (i n : ℤ)
    (h : RelZS (ZMod q) (tw q i) n (sch.map (pullback.fst (l ≫ r) c))) :
    RelZS (ZMod q) (tw q i) n (disc.map (m.app p)) := by
  have hp : IsPullback (m.app p) ((cechAug k₀).app p) ((cechAug k).app p)
      (yoneda.map (pullback.fst r c)) :=
    hm.map ((evaluation _ _).obj p)
  have hB : IsPullback (m.app p ≫ e.inv) ((cechAug k₀).app p) (yoneda.map l)
      (yoneda.map (pullback.fst r c)) := by
    refine hp.of_iso (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp
    · rw [Iso.refl_hom, Iso.symm_hom, ← he]
      erw [Iso.inv_hom_id_assoc, Category.comp_id]
    · erw [Category.comp_id]
      try erw [Category.id_comp]
  let φ : pullback (l ≫ r) c ⟶ pullback r c :=
    pullback.lift (pullback.fst (l ≫ r) c ≫ l) (pullback.snd (l ≫ r) c)
      (by simp [pullback.condition])
  have hφ₁ : φ ≫ pullback.fst r c = pullback.fst (l ≫ r) c ≫ l := pullback.lift_fst _ _ _
  have hφ₂ : φ ≫ pullback.snd r c = pullback.snd (l ≫ r) c := pullback.lift_snd _ _ _
  have hS : IsPullback (pullback.fst (l ≫ r) c) φ l (pullback.fst r c) := by
    refine IsPullback.of_bot ?_ hφ₁.symm (IsPullback.of_hasPullback r c)
    rw [hφ₂]
    exact IsPullback.of_hasPullback (l ≫ r) c
  have hA := hS.map yoneda
  let ι := IsPullback.isoIsPullback _ _ hA hB
  have hι : ι.hom ≫ m.app p ≫ e.inv = yoneda.map (pullback.fst (l ≫ r) c) :=
    IsPullback.isoIsPullback_hom_fst _ _ hA hB
  have key : yoneda.map (pullback.fst (l ≫ r) c) ≫ e.hom = ι.hom ≫ m.app p := by
    rw [← hι]
    simp
  refine RelZS.of_iso (ZMod q) (tw q i) (sch.map (pullback.fst (l ≫ r) c)) (disc.map (m.app p))
    (disc.mapIso ι) (disc.mapIso e) ?_ n h
  have := congrArg (fun f => disc.map f) key
  simp only [Functor.map_comp] at this
  exact this

private noncomputable def wpOne {A B : Scheme.{0}ᵒᵖ ⥤ Type} (f : A ⟶ B) :
    A ≅ widePullback B (fun _ : Fin (0 + 1) => A) (fun _ => f) where
  hom := WidePullback.lift f (fun _ => 𝟙 _) (fun _ => Category.id_comp _)
  inv := WidePullback.π (fun _ : Fin (0 + 1) => f) 0
  hom_inv_id := WidePullback.lift_π _ _ _ _ _
  inv_hom_id := by
    apply WidePullback.hom_ext (fun _ : Fin (0 + 1) => f)
    · intro j
      obtain rfl : j = 0 := Fin.fin_one_eq_zero j
      rw [Category.assoc, WidePullback.lift_π]
      simp
    · rw [Category.assoc, WidePullback.lift_base]
      simp

private noncomputable def cech_zero {Y X : Scheme.{0}} (k : Y ⟶ X) :
    yoneda.obj Y ≅ (cech k).obj (Opposite.op (SimplexCategory.mk 0)) :=
  wpOne (yoneda.map k)

private theorem cech_zero_aug {Y X : Scheme.{0}} (k : Y ⟶ X) :
    (cech_zero k).hom ≫ (cechAug k).app (Opposite.op (SimplexCategory.mk 0)) = yoneda.map k :=
  WidePullback.lift_base _ _ _ _

theorem UpperTheory.cohomology_base_change_integral_surjective_cech :
    B4 → ∀ (q : ℕ) (i : ℤ) {Y X S S₀ : Scheme.{0}} (k : Y ⟶ X) [IsIntegralHom k] [Surjective k] (r : X ⟶ S) (c : S₀ ⟶ S), IsUnit (q : Γ(X, ⊤)) → ∃ (U E : Spc) (u : U ⟶ E) (a' : U ⟶ sch.obj (pullback r c)) (a : E ⟶ sch.obj X), u ≫ a = a' ≫ sch.map (pullback.fst r c) ∧ Eqv _ a (tw q i) ∧ Eqv _ a' (tw q i) ∧ (∀ p : ℕ, ∃ (L : Scheme.{0}) (l : L ⟶ X), IsIntegralHom l ∧ ∀ m, RelZS (ZMod q) (tw q i) m (sch.map (pullback.fst (l ≫ r) c)) → RelZS (ZMod q) (tw q i) m (disc.map (u.app (Opposite.op (SimplexCategory.mk p))))) ∧ ∀ m, RelZS (ZMod q) (tw q i) m (sch.map (pullback.fst (k ≫ r) c)) → RelZS (ZMod q) (tw q i) m (disc.map (u.app (Opposite.op (SimplexCategory.mk 0)))) := by
  intro b4 q i Y X S S₀ k _ _ r c hq
  have hP := IsPullback.of_hasPullback k (pullback.fst r c)
  obtain ⟨u, hu, -⟩ := GlobalTheory.cech_baseChange Y X _ _ _ _ k (pullback.fst r c) hP
  have hq₀ : IsUnit (q : Γ(pullback r c, ⊤)) := by
    simpa using hq.map (pullback.fst r c).appTop.hom
  haveI : IsIntegralHom (pullback.snd k (pullback.fst r c)) := MorphismProperty.of_isPullback hP inferInstance
  haveI : Surjective (pullback.snd k (pullback.fst r c)) := MorphismProperty.of_isPullback hP inferInstance
  refine ⟨_, _, u, cechAug _, cechAug k, hu.w, b4 q k hq i, b4 q _ hq₀ i, fun p => ?_, fun n h => ?_⟩
  · obtain ⟨Z, π, e, hπ, he⟩ := GlobalTheory.EtC.cech_level_representable (@IsIntegralHom) Y X k inferInstance
      (Opposite.op (SimplexCategory.mk p))
    haveI : IsIntegralHom π := hπ
    exact ⟨Z, π ≫ k, inferInstance, fun n h =>
      level_rel k r c _ u hu _ (π ≫ k) e he q i n h⟩
  · exact level_rel k r c _ u hu _ k (cech_zero k) (cech_zero_aug k) q i n h
