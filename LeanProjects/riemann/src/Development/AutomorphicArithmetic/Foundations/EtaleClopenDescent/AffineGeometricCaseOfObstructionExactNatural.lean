import Mathlib
import Development.EtaleCohomology.EtaleSheaves.GeoProof
import Development.EtaleCohomology.KummerTheory.FinSHen
import Development.EtaleCohomology.KummerTheory.FinCont

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open LateralTheory.E.E4 LateralTheory.E.Bridge_yfiPf LateralTheory.E.EtaleTopologySheaves LateralTheory.E.SecondDegreeKilling

namespace UpperTheory.Cb.MorphismCompositionLaws

section Maps
variable {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B)

private abbrev mY {S S' : Scheme.{0}} {s : S ⟶ B} {s' : S' ⟶ B} (g : S' ⟶ S) (h : g ≫ s = s') :
    pullback p s' ⟶ pullback p s :=
  pullback.map p s' p s (𝟙 Y) g (𝟙 B) (by simp) (by simp [h])

private abbrev mW {S S' : Scheme.{0}} {s : S ⟶ B} {s' : S' ⟶ B} (g : S' ⟶ S) (h : g ≫ s = s') :
    pullback (pullback.snd p s' ≫ s') ι ⟶ pullback (pullback.snd p s ≫ s) ι :=
  pullback.map _ _ _ _ (mY p g h) (𝟙 W) (𝟙 B)
    (by subst h; simp [pullback.lift_snd_assoc]) (by simp)

private theorem mY_comp_pullback_fst {S S' : Scheme.{0}} {s : S ⟶ B} {s' : S' ⟶ B} (g : S' ⟶ S) (h : g ≫ s = s') :
    mY p g h ≫ pullback.fst p s = pullback.fst p s' := by
  unfold mY pullback.map
  erw [pullback.lift_fst]
  exact Category.comp_id _

private theorem mY_comp_pullback_snd {S S' : Scheme.{0}} {s : S ⟶ B} {s' : S' ⟶ B} (g : S' ⟶ S) (h : g ≫ s = s') :
    mY p g h ≫ pullback.snd p s = pullback.snd p s' ≫ g := by
  unfold mY pullback.map
  erw [pullback.lift_snd]

private theorem mW_comp_fst_eq_fst_comp_mY {S S' : Scheme.{0}} {s : S ⟶ B} {s' : S' ⟶ B} (g : S' ⟶ S) (h : g ≫ s = s') :
    mW p ι g h ≫ pullback.fst _ ι = pullback.fst _ ι ≫ mY p g h := by
  unfold mW pullback.map
  erw [pullback.lift_fst]

private theorem mW_comp_pullback_snd {S S' : Scheme.{0}} {s : S ⟶ B} {s' : S' ⟶ B} (g : S' ⟶ S) (h : g ≫ s = s') :
    mW p ι g h ≫ pullback.snd _ ι = pullback.snd _ ι := by
  unfold mW pullback.map
  erw [pullback.lift_snd]
  exact Category.comp_id _

private theorem mY_comp {S S' S'' : Scheme.{0}} {s : S ⟶ B} {s' : S' ⟶ B} {s'' : S'' ⟶ B} (g : S' ⟶ S) (h : g ≫ s = s')
    (g' : S'' ⟶ S') (h' : g' ≫ s' = s'') :
    mY p g' h' ≫ mY p g h = mY p (g' ≫ g) (by simp [h, h']) := by
  apply pullback.hom_ext
  · rw [Category.assoc, mY_comp_pullback_fst, mY_comp_pullback_fst, mY_comp_pullback_fst]
  · rw [Category.assoc, mY_comp_pullback_snd, reassoc_of% (mY_comp_pullback_snd p g' h'), mY_comp_pullback_snd]

private theorem mW_comp {S S' S'' : Scheme.{0}} {s : S ⟶ B} {s' : S' ⟶ B} {s'' : S'' ⟶ B} (g : S' ⟶ S) (h : g ≫ s = s')
    (g' : S'' ⟶ S') (h' : g' ≫ s' = s'') :
    mW p ι g' h' ≫ mW p ι g h = mW p ι (g' ≫ g) (by simp [h, h']) := by
  apply pullback.hom_ext
  · rw [Category.assoc, mW_comp_fst_eq_fst_comp_mY, reassoc_of% (mW_comp_fst_eq_fst_comp_mY p ι g' h'), mW_comp_fst_eq_fst_comp_mY, mY_comp p g h g' h']
  · rw [Category.assoc, mW_comp_pullback_snd, mW_comp_pullback_snd, mW_comp_pullback_snd]

private theorem mY_comp' {S S' S'' : Scheme.{0}} {s : S ⟶ B} {s' : S' ⟶ B} {s'' : S'' ⟶ B} (g : S' ⟶ S) (h : g ≫ s = s')
    (g' : S'' ⟶ S') (h' : g' ≫ s' = s'') (g'' : S'' ⟶ S) (h'' : g'' ≫ s = s'') (e : g' ≫ g = g'') :
    mY p g' h' ≫ mY p g h = mY p g'' h'' := by
  subst e; exact mY_comp p g h g' h'

private theorem mW_comp' {S S' S'' : Scheme.{0}} {s : S ⟶ B} {s' : S' ⟶ B} {s'' : S'' ⟶ B} (g : S' ⟶ S) (h : g ≫ s = s')
    (g' : S'' ⟶ S') (h' : g' ≫ s' = s'') (g'' : S'' ⟶ S) (h'' : g'' ≫ s = s'') (e : g' ≫ g = g'') :
    mW p ι g' h' ≫ mW p ι g h = mW p ι g'' h'' := by
  subst e; exact mW_comp p ι g h g' h'

private theorem mW_fst {S S' : Scheme.{0}} {s : S ⟶ B} {s' : S' ⟶ B} (g : S' ⟶ S) (h : g ≫ s = s') :
    pullback.fst _ _ ≫ mY p g h = mW p ι g h ≫ pullback.fst _ _ := by
  rw [mW_comp_fst_eq_fst_comp_mY]

end Maps

section Transfer

private def ContP (q : ℕ) (i n : ℤ) {J : Type} [Category J] (E : J → Spc) (L : Spc) (b : ∀ j, L ⟶ E j)
    (tr : ∀ {j k : J}, (j ⟶ k) → (E k ⟶ E j)) : Prop :=
  (∀ x : Ht q L n i, ∃ j, ∃ y : Ht q (E j) n i, pull (ZMod q) (b j) (tw q i) n y = x) ∧
  ∀ j (y : Ht q (E j) n i), pull (ZMod q) (b j) (tw q i) n y = 0 →
    ∃ (k : J) (f : j ⟶ k), pull (ZMod q) (tr f) (tw q i) n y = 0

private theorem pull_cancel {q : ℕ} {i n : ℤ} {E E' : Spc} (e : E ≅ E') (x : Ht q E' n i) :
    pull (ZMod q) e.inv (tw q i) n (pull (ZMod q) e.hom (tw q i) n x) = x := by
  rw [← pull_comp, e.inv_hom_id, pull_id]

private theorem transfer {q : ℕ} {i n : ℤ} {J : Type} [Category J] {E E' : J → Spc} {L L' : Spc}
    {b : ∀ j, L ⟶ E j} {b' : ∀ j, L' ⟶ E' j}
    {tr : ∀ {j k : J}, (j ⟶ k) → (E k ⟶ E j)} {tr' : ∀ {j k : J}, (j ⟶ k) → (E' k ⟶ E' j)}
    (φ : ∀ j, E j ≅ E' j) (φL : L ≅ L')
    (hb : ∀ j, φL.hom ≫ b' j = b j ≫ (φ j).hom)
    (htr : ∀ {j k : J} (f : j ⟶ k), (φ k).hom ≫ tr' f = tr f ≫ (φ j).hom)
    (h : ContP q i n E L b tr) : ContP q i n E' L' b' tr' := by
  obtain ⟨hs, hi⟩ := h
  refine ⟨fun x' => ?_, fun j y' hy' => ?_⟩
  · obtain ⟨j, y, hy⟩ := hs (pull (ZMod q) φL.hom (tw q i) n x')
    refine ⟨j, pull (ZMod q) (φ j).inv (tw q i) n y, ?_⟩
    have hc := pull_cancel (φ j).symm y
    simp only [Iso.symm_inv, Iso.symm_hom] at hc
    have key : pull (ZMod q) φL.hom (tw q i) n
        (pull (ZMod q) (b' j) (tw q i) n (pull (ZMod q) (φ j).inv (tw q i) n y)) =
        pull (ZMod q) φL.hom (tw q i) n x' := by
      rw [← pull_comp, hb, pull_comp, hc, hy]
    have key2 := congrArg (pull (ZMod q) φL.inv (tw q i) n) key
    rwa [pull_cancel, pull_cancel] at key2
  · obtain ⟨k, f, hf⟩ := hi j (pull (ZMod q) (φ j).hom (tw q i) n y')
      (by rw [← pull_comp, ← hb, pull_comp, hy', map_zero])
    refine ⟨k, f, ?_⟩
    have key : pull (ZMod q) (φ k).hom (tw q i) n (pull (ZMod q) (tr' f) (tw q i) n y') = 0 := by
      rw [← pull_comp, htr, pull_comp, hf]
    rw [← pull_cancel (φ k) (pull (ZMod q) (tr' f) (tw q i) n y'), key, map_zero]

end Transfer

section Isos
variable {Y B W C : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (π : C ⟶ B)

private def eY {S : Scheme.{0}} (g : S ⟶ C) (s : S ⟶ B) (h : g ≫ π = s) :
    pullback (pullback.snd p π) g ≅ pullback p s :=
  pullbackLeftPullbackSndIso p π g ≪≫ pullback.congrHom rfl h

@[reassoc (attr := simp)] private theorem eY_hom_fst {S : Scheme.{0}} (g : S ⟶ C) (s : S ⟶ B) (h : g ≫ π = s) :
    (eY p π g s h).hom ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ := by
  subst h; simp [eY]

@[reassoc (attr := simp)] private theorem eY_hom_snd {S : Scheme.{0}} (g : S ⟶ C) (s : S ⟶ B) (h : g ≫ π = s) :
    (eY p π g s h).hom ≫ pullback.snd _ _ = pullback.snd _ _ := by
  subst h; simp [eY]

end Isos

section IsosW
variable {Y B W C : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (π : C ⟶ B)

private theorem eY_inv_snd {S : Scheme.{0}} (g : S ⟶ C) (s : S ⟶ B) (h : g ≫ π = s) :
    (eY p π g s h).inv ≫ pullback.snd _ _ = pullback.snd _ _ := by
  rw [Iso.inv_comp_eq, eY_hom_snd]

private abbrev p2 : pullback (pullback.snd p π ≫ π) ι ⟶ C := pullback.fst _ _ ≫ pullback.snd p π

private abbrev aW {S : Scheme.{0}} (g : S ⟶ C) : pullback (p2 p ι π) g ⟶ pullback (pullback.snd p π) g :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _)
    (by rw [Category.assoc, pullback.condition])

private theorem equiv_hom_comp_projection {S : Scheme.{0}} (g : S ⟶ C) (s : S ⟶ B) (h : g ≫ π = s) :
    (aW p ι π g ≫ (eY p π g s h).hom) ≫ pullback.snd p s ≫ s =
      (pullback.fst (p2 p ι π) g ≫ pullback.snd (pullback.snd p π ≫ π) ι) ≫ ι := by
  subst h
  rw [Category.assoc, Category.assoc, eY_hom_snd_assoc]
  erw [pullback.lift_snd_assoc]
  rw [← pullback.condition (f := pullback.snd p π ≫ π) (g := ι),
    ← pullback.condition_assoc (f := p2 p ι π) (g := g)]
  simp only [Category.assoc]

private theorem equiv_inv_comp_projection {S : Scheme.{0}} (g : S ⟶ C) (s : S ⟶ B) (h : g ≫ π = s) :
    ((pullback.fst (pullback.snd p s ≫ s) ι ≫ (eY p π g s h).inv) ≫ pullback.fst _ _) ≫ pullback.snd p π ≫ π =
      pullback.snd (pullback.snd p s ≫ s) ι ≫ ι := by
  simp only [Category.assoc]
  rw [pullback.condition_assoc, reassoc_of% (eY_inv_snd p π g s h), h]
  exact pullback.condition

private def eW {S : Scheme.{0}} (g : S ⟶ C) (s : S ⟶ B) (h : g ≫ π = s) :
    pullback (p2 p ι π) g ≅ pullback (pullback.snd p s ≫ s) ι where
  hom := pullback.lift (aW p ι π g ≫ (eY p π g s h).hom) (pullback.fst _ _ ≫ pullback.snd _ _)
    (equiv_hom_comp_projection p ι π g s h)
  inv := pullback.lift
    (pullback.lift ((pullback.fst _ _ ≫ (eY p π g s h).inv) ≫ pullback.fst _ _) (pullback.snd _ _)
      (equiv_inv_comp_projection p ι π g s h))
    ((pullback.fst _ _ ≫ (eY p π g s h).inv) ≫ pullback.snd _ _)
    (by rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, Category.assoc, pullback.condition, Category.assoc])
  hom_inv_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
      · simp [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
    · simp [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, ← Iso.eq_comp_inv, Category.id_comp]
      apply pullback.hom_ext <;> simp [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
    · simp [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]

end IsosW

section Nat
variable {Y B W C : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (π : C ⟶ B)
variable {S S' : Scheme.{0}} {g : S ⟶ C} {g' : S' ⟶ C} {s : S ⟶ B} {s' : S' ⟶ B}

private abbrev bc {X : Scheme.{0}} (P : X ⟶ C) (k : S' ⟶ S) (hg : k ≫ g = g') : pullback P g' ⟶ pullback P g :=
  pullback.map _ _ _ _ (𝟙 _) k (𝟙 _) (by simp) (by simp [hg])

private theorem eY_nat (h : g ≫ π = s) (h' : g' ≫ π = s') (k : S' ⟶ S) (hk : k ≫ s = s') (hg : k ≫ g = g') :
    (eY p π g' s' h').hom ≫ mY p k hk = bc (pullback.snd p π) k hg ≫ (eY p π g s h).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, mY_comp_pullback_fst, eY_hom_fst, Category.assoc, eY_hom_fst]
    erw [pullback.lift_fst_assoc]
    rw [Category.comp_id]
  · rw [Category.assoc, mY_comp_pullback_snd, eY_hom_snd_assoc, Category.assoc, eY_hom_snd]
    erw [pullback.lift_snd]

private theorem bc_comp_pullback_fst {X : Scheme.{0}} (P : X ⟶ C) (k : S' ⟶ S) (hg : k ≫ g = g') :
    bc P k hg ≫ pullback.fst P g = pullback.fst P g' := by
  unfold bc pullback.map
  erw [pullback.lift_fst]
  exact Category.comp_id _

private theorem bc_comp_pullback_snd {X : Scheme.{0}} (P : X ⟶ C) (k : S' ⟶ S) (hg : k ≫ g = g') :
    bc P k hg ≫ pullback.snd P g = pullback.snd P g' ≫ k := by
  unfold bc pullback.map
  erw [pullback.lift_snd]

private theorem aW_comp_pullback_fst (g : S ⟶ C) :
    aW p ι π g ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ := by
  unfold aW
  erw [pullback.lift_fst]

private theorem aW_comp_pullback_snd (g : S ⟶ C) :
    aW p ι π g ≫ pullback.snd _ _ = pullback.snd _ _ := by
  unfold aW
  erw [pullback.lift_snd]

private theorem eW_hom_comp_fst_eq_aW_comp_eY (g : S ⟶ C) (h : g ≫ π = s) :
    (eW p ι π g s h).hom ≫ pullback.fst _ _ = aW p ι π g ≫ (eY p π g s h).hom := by
  unfold eW
  erw [pullback.lift_fst]

private theorem eW_hom_comp_snd (g : S ⟶ C) (h : g ≫ π = s) :
    (eW p ι π g s h).hom ≫ pullback.snd _ _ = pullback.fst _ _ ≫ pullback.snd _ _ := by
  unfold eW
  erw [pullback.lift_snd]

private theorem eW_nat (h : g ≫ π = s) (h' : g' ≫ π = s') (k : S' ⟶ S) (hk : k ≫ s = s') (hg : k ≫ g = g') :
    (eW p ι π g' s' h').hom ≫ mW p ι k hk = bc (p2 p ι π) k hg ≫ (eW p ι π g s h).hom := by
  have hA : aW p ι π g' ≫ bc (pullback.snd p π) k hg = bc (p2 p ι π) k hg ≫ aW p ι π g := by
    apply pullback.hom_ext
    · rw [Category.assoc, bc_comp_pullback_fst, aW_comp_pullback_fst, Category.assoc, aW_comp_pullback_fst, reassoc_of% (bc_comp_pullback_fst (p2 p ι π) k hg)]
    · rw [Category.assoc, bc_comp_pullback_snd, reassoc_of% (aW_comp_pullback_snd p ι π g'), Category.assoc, aW_comp_pullback_snd, bc_comp_pullback_snd]
  apply pullback.hom_ext
  · rw [Category.assoc, mW_comp_fst_eq_fst_comp_mY, reassoc_of% (eW_hom_comp_fst_eq_aW_comp_eY p ι π g' h'), eY_nat p π h h' k hk hg,
      reassoc_of% hA, Category.assoc, eW_hom_comp_fst_eq_aW_comp_eY]
  · rw [Category.assoc, mW_comp_pullback_snd, eW_hom_comp_snd, Category.assoc, eW_hom_comp_snd, reassoc_of% (bc_comp_pullback_fst (p2 p ι π) k hg)]

end Nat

section Cont
variable {q : ℕ} [NeZero q] {R : CommRingCat.{0}} {J : Type} [SmallCategory J] [IsFiltered J]
  {D : J ⥤ CommRingCat.{0}} {c : Cocone D} (hc : IsColimit c) {u : ∀ j, R ⟶ D.obj j}
  (hu : ∀ {j k : J} (f : j ⟶ k), u j ≫ D.map f = u k) {v : R ⟶ c.pt} (hv : ∀ j, u j ≫ c.ι.app j = v)

include hc in
private theorem contOf (hA : A2) (hB : B1) {X : Scheme.{0}} (P : X ⟶ Spec R) [QuasiCompact P] [IsSeparated P]
    (hq : IsUnit (q : R)) (i n : ℤ) :
    ContP q i n (fun j => sch.obj (pullback P (Spec.map (u j)))) (sch.obj (pullback P (Spec.map v)))
      (fun j => sch.map (LateralTheory.KummerTheory.bcMap P (u j) v (c.ι.app j) (hv j)))
      (fun {j k} f => sch.map (LateralTheory.KummerTheory.bcMap P (u j) (u k) (D.map f) (hu f))) :=
  LateralTheory.Fin.Cont.intersectionNumber_baseChange hA hB q P hq D c hc u hu v hv n i

end Cont

section Cont2
variable {q : ℕ} [NeZero q] {R : CommRingCat.{0}} {J : Type} [SmallCategory J] [IsFiltered J]
  {D : J ⥤ CommRingCat.{0}} {c : Cocone D} (hc : IsColimit c) {u : ∀ j, R ⟶ D.obj j}
  (hu : ∀ {j k : J} (f : j ⟶ k), u j ≫ D.map f = u k) {v : R ⟶ c.pt} (hv : ∀ j, u j ≫ c.ι.app j = v)
  {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (π : Spec R ⟶ B)
  {s : ∀ j, Spec (D.obj j) ⟶ B} {sL : Spec c.pt ⟶ B}
  (hs : ∀ j, Spec.map (u j) ≫ π = s j) (hsL : Spec.map v ≫ π = sL)
  (h1 : ∀ j, Spec.map (c.ι.app j) ≫ s j = sL)
  (h2 : ∀ {j k : J} (f : j ⟶ k), Spec.map (D.map f) ≫ s j = s k)

include hc hu hv hs hsL in
private theorem contY (hA : A2) (hB : B1) [QuasiCompact (pullback.snd p π)] [IsSeparated (pullback.snd p π)]
    (hq : IsUnit (q : R)) (i n : ℤ) :
    ContP q i n (fun j => sch.obj (pullback p (s j))) (sch.obj (pullback p sL))
      (fun j => sch.map (mY p (Spec.map (c.ι.app j)) (h1 j)))
      (fun {j k} f => sch.map (mY p (Spec.map (D.map f)) (h2 f))) := by
  refine transfer (fun j => sch.mapIso (eY p π (Spec.map (u j)) (s j) (hs j)))
    (sch.mapIso (eY p π (Spec.map v) sL hsL)) (fun j => ?_) (fun {j k} f => ?_)
    (contOf hc hu hv hA hB (pullback.snd p π) hq i n)
  · simp only [CategoryTheory.Functor.mapIso_hom]
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    congr 1
    exact eY_nat p π (hs j) hsL (Spec.map (c.ι.app j)) (h1 j) (by rw [← Spec.map_comp, hv j])
  · simp only [CategoryTheory.Functor.mapIso_hom]
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    congr 1
    exact eY_nat p π (hs j) (hs k) (Spec.map (D.map f)) (h2 f) (by rw [← Spec.map_comp, hu f])

include hc hu hv hs hsL in
private theorem contW (hA : A2) (hB : B1) [QuasiCompact (p2 p ι π)] [IsSeparated (p2 p ι π)]
    (hq : IsUnit (q : R)) (i n : ℤ) :
    ContP q i n (fun j => sch.obj (pullback (pullback.snd p (s j) ≫ s j) ι))
      (sch.obj (pullback (pullback.snd p sL ≫ sL) ι))
      (fun j => sch.map (mW p ι (Spec.map (c.ι.app j)) (h1 j)))
      (fun {j k} f => sch.map (mW p ι (Spec.map (D.map f)) (h2 f))) := by
  refine transfer (fun j => sch.mapIso (eW p ι π (Spec.map (u j)) (s j) (hs j)))
    (sch.mapIso (eW p ι π (Spec.map v) sL hsL)) (fun j => ?_) (fun {j k} f => ?_)
    (contOf hc hu hv hA hB (p2 p ι π) hq i n)
  · simp only [CategoryTheory.Functor.mapIso_hom]
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    congr 1
    exact eW_nat p ι π (hs j) hsL (Spec.map (c.ι.app j)) (h1 j) (by rw [← Spec.map_comp, hv j])
  · simp only [CategoryTheory.Functor.mapIso_hom]
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    congr 1
    exact eW_nat p ι π (hs j) (hs k) (Spec.map (D.map f)) (h2 f) (by rw [← Spec.map_comp, hu f])

end Cont2

section Main

private theorem sys_of {q : ℕ} [NeZero q] (i : ℤ) {B W Y : Scheme.{0}} (ι : W ⟶ B) [IsClosedImmersion ι] (p : Y ⟶ B)
    (hp : IsProper p) (U : B.Etale) (R : CommRingCat.{0}) (e : U.left ≅ Spec R) (m : ℤ) (u : U.left)
    (hq : IsUnit (q : R)) (hA : A2) (hB : B1) : Nonempty (Sys q i p ι U m u) := by
  haveI := hp
  obtain ⟨J, _, _, D, c, hc, uu, hSH, hE⟩ := LateralTheory.Fin.StrictHenselization.intersectionNumber_baseChange R (e.hom u)
  obtain ⟨uj, huj⟩ : ∃ uj : ∀ j, R ⟶ D.obj j, ∀ j, uj j = uu.app j := ⟨fun j => uu.app j, fun _ => rfl⟩
  have hu : ∀ {j k : J} (f : j ⟶ k), uj j ≫ D.map f = uj k := by
    intro j k f
    rw [huj, huj]
    simpa using (uu.naturality f).symm
  obtain ⟨v, hv⟩ : ∃ v : R ⟶ c.pt, ∀ j, uj j ≫ c.ι.app j = v := by
    obtain ⟨j0⟩ := IsFiltered.nonempty (C := J)
    refine ⟨uj j0 ≫ c.ι.app j0, fun j => ?_⟩
    obtain ⟨k, f, g, -⟩ := IsFilteredOrEmpty.cocone_objs j j0
    have a1 : uj j ≫ c.ι.app j = uj k ≫ c.ι.app k := by rw [← c.w f, ← Category.assoc, hu f]
    have a2 : uj j0 ≫ c.ι.app j0 = uj k ≫ c.ι.app k := by rw [← c.w g, ← Category.assoc, hu g]
    exact a1.trans a2.symm
  have hEt : ∀ j, Etale (((Spec.map (uj j) ≫ e.inv) ≫ U.hom : Spec (D.obj j) ⟶ B)) := by
    intro j
    haveI : Etale (Spec.map (uj j)) := HasRingHomProperty.Spec_iff.mpr (by rw [huj]; exact (hE j).1)
    haveI : Etale U.hom := U.prop
    infer_instance
  let π : Spec R ⟶ B := e.inv ≫ U.hom
  let s : ∀ j, Spec (D.obj j) ⟶ B := fun j => (Spec.map (uj j) ≫ e.inv) ≫ U.hom
  let sL : Spec c.pt ⟶ B := (Spec.map v ≫ e.inv) ≫ U.hom
  have hs : ∀ j, Spec.map (uj j) ≫ π = s j := fun j => (Category.assoc _ _ _).symm
  have hsL : Spec.map v ≫ π = sL := (Category.assoc _ _ _).symm
  have h1 : ∀ j, Spec.map (c.ι.app j) ≫ s j = sL := by
    intro j
    simp only [s, sL, ← Category.assoc, ← Spec.map_comp, hv j]
  have h2 : ∀ {j k : J} (f : j ⟶ k), Spec.map (D.map f) ≫ s j = s k := by
    intro j k f
    simp only [s, ← Category.assoc, ← Spec.map_comp, hu f]
  let V : J → B.Etale := fun j => MorphismProperty.Over.mk ⊤ (s j) (hEt j)
  let a : ∀ j, V j ⟶ U := fun j => MorphismProperty.Over.homMk (Spec.map (uj j) ≫ e.inv) rfl trivial
  let tr : ∀ {j k : J}, (j ⟶ k) → (V k ⟶ V j) := fun {j k} f =>
    MorphismProperty.Over.homMk (Spec.map (D.map f)) (h2 f) trivial
  have cY := fun n => contY (hc := hc) (hu := hu) (hv := hv) (p := p) (π := π) (hs := hs) (hsL := hsL)
    (h1 := h1) (h2 := h2) hA hB hq i n
  have cW := fun n => contW (hc := hc) (hu := hu) (hv := hv) (p := p) (ι := ι) (π := π) (hs := hs)
    (hsL := hsL) (h1 := h1) (h2 := h2) hA hB hq i n
  have ea : ∀ j, Spec.map (c.ι.app j) ≫ (a j).left = Spec.map v ≫ e.inv := by
    intro j
    show Spec.map (c.ι.app j) ≫ Spec.map (uj j) ≫ e.inv = Spec.map v ≫ e.inv
    rw [← Category.assoc, ← Spec.map_comp, hv j]
  have etr : ∀ {j k : J} (f : j ⟶ k), Spec.map (c.ι.app k) ≫ (tr f).left = Spec.map (c.ι.app j) := by
    intro j k f
    show Spec.map (c.ι.app k) ≫ Spec.map (D.map f) = Spec.map (c.ι.app j)
    rw [← Spec.map_comp, c.w f]
  refine ⟨Sys.mk J V a ?_ tr ?_ ?_ ?_ c.pt hSH (Spec.map v ≫ e.inv)
    (fun j => mY p (Spec.map (c.ι.app j)) (h1 j)) (fun j => mW p ι (Spec.map (c.ι.app j)) (h1 j))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · intro j
    obtain ⟨𝔮, h𝔮⟩ := (hE j).2
    refine ⟨𝔮, ?_⟩
    have hp𝔮 : Spec.map (uj j) 𝔮 = e.hom u := by
      rw [huj]
      exact PrimeSpectrum.ext h𝔮
    show e.inv (Spec.map (uj j) 𝔮) = u
    rw [hp𝔮]
    simp
  · intro j
    apply MorphismProperty.Over.Hom.ext
    show Spec.map (D.map (𝟙 j)) = 𝟙 _
    rw [CategoryTheory.Functor.map_id, Spec.map_id]
  · intro j k l f g
    apply MorphismProperty.Over.Hom.ext
    show Spec.map (D.map (f ≫ g)) = Spec.map (D.map g) ≫ Spec.map (D.map f)
    rw [CategoryTheory.Functor.map_comp, Spec.map_comp]
  · intro j k f
    apply MorphismProperty.Over.Hom.ext
    show Spec.map (D.map f) ≫ Spec.map (uj j) ≫ e.inv = Spec.map (uj k) ≫ e.inv
    rw [← Category.assoc, ← Spec.map_comp, hu f]
  · intro j
    exact mW_fst p ι _ _
  · intro j
    exact mY_comp' p (a j).left rfl (Spec.map (c.ι.app j)) (h1 j) (Spec.map v ≫ e.inv) rfl (ea j)
  · intro j
    exact mW_comp' p ι (a j).left rfl (Spec.map (c.ι.app j)) (h1 j) (Spec.map v ≫ e.inv) rfl (ea j)
  · intro j k f
    exact mY_comp' p (tr f).left (h2 f) (Spec.map (c.ι.app k)) (h1 k) (Spec.map (c.ι.app j)) (h1 j) (etr f)
  · intro j k f
    exact mW_comp' p ι (tr f).left (h2 f) (Spec.map (c.ι.app k)) (h1 k) (Spec.map (c.ι.app j)) (h1 j) (etr f)
  · intro j y hy
    exact (cY m).2 j y hy
  · intro y
    exact (cY (m - 1)).1 y
  · intro j w hw
    exact (cW (m - 1)).2 j w hw

end Main

end UpperTheory.Cb.MorphismCompositionLaws

theorem UpperTheory.Cb.affineGeometricCase_of_obstructionExact_natural :
    LateralTheory.E.NeighbourhoodKilling.ObsExact → LateralTheory.E.NeighbourhoodKilling.ObsNat → LateralTheory.E.GeoProof.AffGeo := by
  intro _ _ hyps q _ k _ hqk i B W Y x ι _ p hp U R e m u
  have hq : IsUnit (q : R) := by
    have h := hqk.map (Spec.preimage (e.inv ≫ U.hom ≫ x)).hom
    rwa [map_natCast] at h
  exact UpperTheory.Cb.MorphismCompositionLaws.sys_of i ι p hp U R e m u hq hyps.2.1 hyps.2.2.2.2.2.2.2.2.2.2.1
