import Development.EtaleCohomology.EtaleSheaves.ProEqvPfA

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut LateralTheory.E.ProEqvPf

namespace LateralTheory.E.StageBPf

theorem pp {q : ℕ} {i n : ℤ} {X Y Z : Scheme.{0}} (a : X ⟶ Y) (b : Y ⟶ Z) (x : Ht q (sch.obj Z) n i) :
    pull _ (sch.map a) _ _ (pull _ (sch.map b) _ _ x) = pull _ (sch.map (a ≫ b)) (tw q i) n x := by
  rw [Functor.map_comp, pull_comp]

theorem indep {Y : Scheme.{0}} {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D)
    (ι : ∀ j, D.obj j ⟶ Y) (hι : ∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j) (j j' : J) :
    c.π.app j ≫ ι j = c.π.app j' ≫ ι j' := by
  rw [← c.w (IsCofiltered.minToLeft j j'), ← c.w (IsCofiltered.minToRight j j'), Category.assoc, Category.assoc, hι, hι]

theorem qc_of {X Y : Scheme.{0}} (f : X ⟶ Y) (h : IsAffineHom f) (hY : CompactSpace Y) : CompactSpace X :=
  QuasiCompact.compactSpace_of_compactSpace f
theorem qs_of {X Y : Scheme.{0}} (f : X ⟶ Y) (h : IsAffineHom f) (hY : QuasiSeparatedSpace Y) : QuasiSeparatedSpace X :=
  quasiSeparatedSpace_of_quasiSeparated f
theorem aff_canc {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h1 : IsAffineHom (f ≫ g)) (h2 : IsAffineHom g) : IsAffineHom f := by
  have := IsSeparated.of_isAffineHom g; exact IsAffineHom.of_comp f g
theorem aff_comp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h1 : IsAffineHom f) (h2 : IsAffineHom g) : IsAffineHom (f ≫ g) :=
  inferInstance

variable {A : Type} [CommRing A] [IsLocalRing A]

@[simps]
def DO {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of A)) {J : Type} [SmallCategory J] (D : J ⥤ Scheme.{0})
    (ι : ∀ j, D.obj j ⟶ Y) (hι : ∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j) : J ⥤ Over (Spec (CommRingCat.of A)) where
  obj j := Over.mk (ι j ≫ g)
  map f := Over.homMk (D.map f) (by dsimp; rw [← Category.assoc, hι])
  map_id := by intros; ext; simp
  map_comp := by intros; ext; simp

@[simps]
def CO {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of A)) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0})
    (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y) (hι : ∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j) (j0 : J) :
    Cone (DO g D ι hι) where
  pt := Over.mk ((c.π.app j0 ≫ ι j0) ≫ g)
  π := { app := fun j => Over.homMk (c.π.app j) (by show c.π.app j ≫ ι j ≫ g = _; rw [← Category.assoc, indep D c ι hι j j0]; rfl)
         naturality := by intro j k f; ext; exact (c.w f).symm }

def isLimit_CO {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of A)) {J : Type} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y) (hι : ∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j) (j0 : J)
    (hl : IsLimit c) : IsLimit (CO g D c ι hι j0) := by
  haveI := IsCofiltered.isConnected J
  exact isLimitOfReflects (Over.forget _) hl

def isLimit_fib {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of A)) {J : Type} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y) (hι : ∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j) (j0 : J)
    (hl : IsLimit c) :
    IsLimit ((Over.forget _).mapCone ((Over.pullback (cpt A)).mapCone (CO g D c ι hι j0))) := by
  haveI := IsCofiltered.isConnected J
  haveI := (Over.mapPullbackAdj (cpt A)).rightAdjoint_preservesLimits
  exact isLimitOfPreserves _ (isLimitOfPreserves _ (isLimit_CO g D c ι hι j0 hl))

theorem fm_comp {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of A)) {U V : Scheme.{0}} (u : U ⟶ Y) (v : V ⟶ Y) (d : U ⟶ V)
    (hd : d ≫ v = u) (h : pullback (u ≫ g) (cpt A) ⟶ pullback (v ≫ g) (cpt A))
    (h1 : h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ d) (h2 : h ≫ pullback.snd _ _ = pullback.snd _ _) :
    h ≫ fm v g = fm u g := by
  apply pullback.hom_ext
  · simp only [fm, pullback.map, Category.assoc]
    erw [pullback.lift_fst, pullback.lift_fst, ← Category.assoc, h1, Category.assoc, hd]
  · simp only [fm, pullback.map, Category.assoc]
    erw [pullback.lift_snd, pullback.lift_snd, Category.comp_id, Category.comp_id, h2]

end LateralTheory.E.StageBPf

namespace LateralTheory.E.StageBPf

theorem StageB_of : StageB := by
  intro hC H q i A _ _ hq Y _ _ g y J _ _ D c ι hc hp n z
  obtain ⟨⟨hl⟩, hι, hD⟩ := hc
  obtain ⟨j0⟩ := IsCofiltered.nonempty (C := J)
  have hcs : ∀ j, CompactSpace (D.obj j) := fun j => by
    have := (hι j).2.1; exact QuasiCompact.compactSpace_of_compactSpace (ι j)
  have hqs : ∀ j, QuasiSeparatedSpace (D.obj j) := fun j => by
    have := (hι j).1; exact quasiSeparatedSpace_of_quasiSeparated (ι j)
  have hι' : ∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j := fun f => (hD f).1
  obtain ⟨w, hw⟩ := (hp j0 n).2 (pull _ (sch.map (fm (c.π.app j0 ≫ ι j0) g)) _ _ z)
  obtain ⟨j1, u, hu⟩ := (hC H q D c hl (fun f => (hD f).2) hcs hqs (fun j => unit_of hq (ι j ≫ g)) n i).1 w
  have hfa : ∀ j, IsAffineHom (pullback.fst (ι j ≫ g) (cpt A)) := fun j =>
    MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback _ _).flip inferInstance
  have hκ : IsUnit (q : IsLocalRing.ResidueField A) := by simpa using hq.map (IsLocalRing.residue A)
  let Cg := (Over.forget _).mapCone ((Over.pullback (cpt A)).mapCone (CO g D c ι hι' j0))
  have hlim : IsLimit Cg := isLimit_fib g D c ι hι' j0 hl
  have hEaff : ∀ {j k : J} (f : j ⟶ k), IsAffineHom (((DO g D ι hι' ⋙ Over.pullback (cpt A)) ⋙ Over.forget _).map f) := by
    intro j k f
    have e : ((DO g D ι hι' ⋙ Over.pullback (cpt A)) ⋙ Over.forget _).map f ≫ pullback.fst (ι k ≫ g) (cpt A) =
        pullback.fst (ι j ≫ g) (cpt A) ≫ D.map f := pullback.lift_fst _ _ _
    refine aff_canc _ (pullback.fst (ι k ≫ g) (cpt A)) ?_ (hfa k)
    rw [e]; exact aff_comp _ _ (hfa j) (hD f).2
  have hEc : ∀ j, CompactSpace (((DO g D ι hι' ⋙ Over.pullback (cpt A)) ⋙ Over.forget _).obj j) := fun j =>
    qc_of (pullback.fst (ι j ≫ g) (cpt A)) (hfa j) (hcs j)
  have hEq : ∀ j, QuasiSeparatedSpace (((DO g D ι hι' ⋙ Over.pullback (cpt A)) ⋙ Over.forget _).obj j) := fun j =>
    qs_of (pullback.fst (ι j ≫ g) (cpt A)) (hfa j) (hqs j)
  have hEu : ∀ j, IsUnit (q : Γ((((DO g D ι hι' ⋙ Over.pullback (cpt A)) ⋙ Over.forget _).obj j), ⊤)) := fun j =>
    unit_of hκ (pullback.snd (ι j ≫ g) (cpt A))
  have key1 : Cg.π.app j1 ≫ pullback.fst (ι j1 ≫ g) (cpt A) = pullback.fst _ _ ≫ c.π.app j1 := pullback.lift_fst _ _ _
  have key1s : Cg.π.app j1 ≫ pullback.snd (ι j1 ≫ g) (cpt A) = pullback.snd _ _ := pullback.lift_snd _ _ _
  have key2 : Cg.π.app j1 ≫ fm (ι j1) g = fm (c.π.app j0 ≫ ι j0) g :=
    fm_comp g (c.π.app j0 ≫ ι j0) (ι j1) (c.π.app j1) (indep D c ι hι' j1 j0) _ key1 key1s
  have hv : pull _ (sch.map (Cg.π.app j1)) _ _ (pull _ (sch.map (pullback.fst (ι j1 ≫ g) (cpt A))) _ _ u -
      pull _ (sch.map (fm (ι j1) g)) (tw q i) n z) = 0 := by
    erw [map_sub, pp, pp, key1, key2, ← pp, hu, hw, sub_self]
  obtain ⟨k, f, hk⟩ := (hC H q _ Cg hlim hEaff hEc hEq hEu n i).2 j1 _ hv
  refine ⟨k, pull _ (sch.map (D.map f)) _ _ u, ?_⟩
  have key3 : ((DO g D ι hι' ⋙ Over.pullback (cpt A)) ⋙ Over.forget _).map f ≫ pullback.fst (ι j1 ≫ g) (cpt A) =
      pullback.fst (ι k ≫ g) (cpt A) ≫ D.map f := pullback.lift_fst _ _ _
  have key5 : ((DO g D ι hι' ⋙ Over.pullback (cpt A)) ⋙ Over.forget _).map f ≫ pullback.snd (ι j1 ≫ g) (cpt A) =
      pullback.snd (ι k ≫ g) (cpt A) := pullback.lift_snd _ _ _
  have key4 := fm_comp g (ι k) (ι j1) (D.map f) (hι' f) _ key3 key5
  erw [map_sub, pp, pp, key3, key4, ← pp, sub_eq_zero] at hk
  exact hk

end LateralTheory.E.StageBPf
