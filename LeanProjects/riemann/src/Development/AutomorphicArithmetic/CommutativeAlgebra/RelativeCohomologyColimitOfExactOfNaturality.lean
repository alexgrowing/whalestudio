import Mathlib
import Development.EtaleCohomology.EtaleSheaves.BridgeYfiPf
import Development.EtaleCohomology.EtaleSheaves.GlueRelPfCone

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.Cb.RelativeCohomologyColimit
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.SecondDegreeKilling.Nbhd
  LateralTheory.E.NeighbourhoodKilling LateralTheory.E.SecondDegreeKilling LateralTheory.E.Bridge_yfiPf

private theorem hk_id {R : Type} [CommRing R] (K : Cx R) (F : Shv R) (n : ℤ) (x : HK R K F n) :
    HK.pull R (𝟙 K) F n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CochainComplex.HomComplex.CohomologyClass.mk (CochainComplex.HomComplex.Cocycle.ext ?_)
  simp [zcomp]

private theorem cone_id {R : Type} [CommRing R] {K L : Cx R} (φ : K ⟶ L) (a : K ⟶ K) (b : L ⟶ L) (ha : a = 𝟙 K)
    (hb : b = 𝟙 L) (comm) : CochainComplex.mappingCone.map φ φ a b comm = 𝟙 _ := by
  subst ha hb
  exact CochainComplex.mappingCone.map_id φ

private theorem rpl_one (q : ℕ) (i : ℤ) {U E : Scheme.{0}} (f : U ⟶ E) (u : U ⟶ U) (e : E ⟶ E)
    (h : f ≫ e = u ≫ f) (hu : u = 𝟙 U) (he : e = 𝟙 E) (n : ℤ)
    (y : Hrel (ZMod q) (sch.map f) (tw q i) n) : rpl q i f f u e h n y = y := by
  subst hu he
  have key : rmap (ZMod q) (sch.map f) (sch.map f) (sch.map (𝟙 U)) (sch.map (𝟙 E))
      (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, h]) = 𝟙 _ :=
    cone_id _ _ _ (by rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id])
      (by rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]) _
  exact (congrArg (fun c => HK.pull (ZMod q) c (tw q i) n y) key).trans (hk_id _ _ _ y)

private theorem rpl_two (q : ℕ) (i : ℤ) {U E U' E' U'' E'' : Scheme.{0}} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (comm : f' ≫ e = u ≫ f) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (comm' : f'' ≫ e' = u' ≫ f')
    (u2 : U'' ⟶ U) (e2 : E'' ⟶ E) (comm2 : f'' ≫ e2 = u2 ≫ f) (hu : u' ≫ u = u2) (he : e' ≫ e = e2) (n : ℤ)
    (y : Hrel (ZMod q) (sch.map f) (tw q i) n) :
    rpl q i f' f'' u' e' comm' n (rpl q i f f' u e comm n y) = rpl q i f f'' u2 e2 comm2 n y := by
  subst hu he
  exact LateralTheory.E.SecondDegreeKilling.Comp.rpl_comp q i f f' f'' u e comm u' e' comm' comm2 n y

private theorem pull_one {X : Scheme.{0}} (a : X ⟶ X) (h : a = 𝟙 X) (q : ℕ) (i n : ℤ) (y : Ht q (sch.obj X) n i) :
    pull (ZMod q) (sch.map a) (tw q i) n y = y := by
  subst h
  rw [CategoryTheory.Functor.map_id, pull_id]

private theorem pull_two {X X' X'' : Scheme.{0}} (c : X ⟶ X'') (a : X ⟶ X') (b : X' ⟶ X'') (h : c = a ≫ b) (q : ℕ)
    (i n : ℤ) (y : Ht q (sch.obj X'') n i) :
    pull (ZMod q) (sch.map c) (tw q i) n y =
      pull (ZMod q) (sch.map a) (tw q i) n (pull (ZMod q) (sch.map b) (tw q i) n y) := by
  subst h
  rw [CategoryTheory.Functor.map_comp, pull_comp]

private theorem pull_sq {X X' X'' X''' : Scheme.{0}} (a : X ⟶ X') (b : X' ⟶ X''') (c : X ⟶ X'') (d : X'' ⟶ X''')
    (h : a ≫ b = c ≫ d) (q : ℕ) (i n : ℤ) (y : Ht q (sch.obj X''') n i) :
    pull (ZMod q) (sch.map a) (tw q i) n (pull (ZMod q) (sch.map b) (tw q i) n y) =
      pull (ZMod q) (sch.map c) (tw q i) n (pull (ZMod q) (sch.map d) (tw q i) n y) := by
  rw [← pull_two _ a b rfl, ← pull_two _ c d rfl, h]

private def obsC (q : ℕ) [NeZero q] {U E : Spc} (u : U ⟶ E) (i n m : ℤ) (h : n + 1 = m) :
    Ht q U n i →+ Hrel (ZMod q) u (tw q i) m := by
  subst h
  exact LateralTheory.E.GlueRelPf.obs q u i n

private theorem obsC_exact (hO : ObsExact) (q : ℕ) [NeZero q] {U E : Spc} (u : U ⟶ E) (i n m : ℤ) (h : n + 1 = m)
    (y : Hrel (ZMod q) u (tw q i) m) (hy : fgt (ZMod q) u (tw q i) m y = 0) : ∃ w, obsC q u i n m h w = y := by
  subst h
  exact hO q u i n y hy

private theorem obsC_nat (hN : ObsNat) (q : ℕ) [NeZero q] {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U)
    (e : E' ⟶ E) (comm : f' ≫ e = u ≫ f) (i n m : ℤ) (h : n + 1 = m) (w : Ht q U n i) :
    rpull (ZMod q) f f' u e comm (tw q i) m (obsC q f i n m h w) =
      obsC q f' i n m h (pull (ZMod q) u (tw q i) n w) := by
  subst h
  exact hN q f f' u e comm i n w

private theorem obsC_lift (q : ℕ) [NeZero q] {U E : Spc} (u : U ⟶ E) (i n m : ℤ) (h : n + 1 = m) (w : Ht q U n i)
    (hw : obsC q u i n m h w = 0) : ∃ y, pull (ZMod q) u (tw q i) n y = w := by
  subst h
  exact (LateralTheory.E.GlueRelPfCone.coneExact (ZMod q) ((chains (ZMod q)).map u) (tw q i) n w).1 hw

private theorem obsC_pull (q : ℕ) [NeZero q] {U E : Spc} (u : U ⟶ E) (i n m : ℤ) (h : n + 1 = m)
    (y : Ht q E n i) : obsC q u i n m h (pull (ZMod q) u (tw q i) n y) = 0 := by
  subst h
  exact (LateralTheory.E.GlueRelPfCone.coneExact (ZMod q) ((chains (ZMod q)).map u) (tw q i) n).apply_apply_eq_zero y

private structure Tow (J : Type) [SmallCategory J] where
  A : J → Scheme.{0}
  t : ∀ {j k : J}, (j ⟶ k) → (A k ⟶ A j)
  t_id : ∀ j, t (𝟙 j) = 𝟙 (A j)
  t_comp : ∀ {j k l : J} (f : j ⟶ k) (g : k ⟶ l), t (f ≫ g) = t g ≫ t f
  L : Scheme.{0}
  g : ∀ j, L ⟶ A j
  g_comp_transition : ∀ {j k : J} (f : j ⟶ k), g k ≫ t f = g j

variable {J : Type} [SmallCategory J]

private def Tow.fn (T : Tow J) (q : ℕ) (i n : ℤ) : J ⥤ AddCommGrpCat.{1} where
  obj j := AddCommGrpCat.of (Ht q (sch.obj (T.A j)) n i)
  map f := AddCommGrpCat.ofHom (pull (ZMod q) (sch.map (T.t f)) (tw q i) n)
  map_id j := by
    ext y
    exact pull_one _ (T.t_id j) q i n y
  map_comp {j k l} f g := by
    ext y
    exact pull_two _ _ _ (T.t_comp f g) q i n y

private def Tow.co (T : Tow J) (q : ℕ) (i n : ℤ) : Cocone (T.fn q i n) where
  pt := AddCommGrpCat.of (Ht q (sch.obj T.L) n i)
  ι :=
    { app := fun j => AddCommGrpCat.ofHom (pull (ZMod q) (sch.map (T.g j)) (tw q i) n)
      naturality := fun j k f => by
        ext y
        exact (pull_two _ _ _ (T.g_comp_transition f).symm q i n y).symm }

private structure Fam (J : Type) [SmallCategory J] where
  X : Tow J
  Z : Tow J
  pr : ∀ j, Z.A j ⟶ X.A j
  prt : ∀ {j k : J} (f : j ⟶ k), pr k ≫ X.t f = Z.t f ≫ pr j
  prL : Z.L ⟶ X.L
  sq : ∀ j, prL ≫ X.g j = Z.g j ≫ pr j

private def Fam.rel (F : Fam J) (q : ℕ) (i m : ℤ) : J ⥤ AddCommGrpCat.{1} where
  obj j := AddCommGrpCat.of (Hrel (ZMod q) (sch.map (F.pr j)) (tw q i) m)
  map f := AddCommGrpCat.ofHom (rpl q i (F.pr _) (F.pr _) (F.Z.t f) (F.X.t f) (F.prt f) m)
  map_id j := by
    ext y
    exact rpl_one q i (F.pr j) _ _ (F.prt (𝟙 j)) (F.Z.t_id j) (F.X.t_id j) m y
  map_comp {j k l} f g := by
    ext y
    exact (rpl_two q i (F.pr j) (F.pr k) (F.pr l) _ _ (F.prt f) _ _ (F.prt g) _ _ (F.prt (f ≫ g))
      (F.Z.t_comp f g).symm (F.X.t_comp f g).symm m y).symm

private def Fam.co (F : Fam J) (q : ℕ) (i m : ℤ) : Cocone (F.rel q i m) where
  pt := AddCommGrpCat.of (Hrel (ZMod q) (sch.map F.prL) (tw q i) m)
  ι :=
    { app := fun j => AddCommGrpCat.ofHom (rpl q i (F.pr j) F.prL (F.Z.g j) (F.X.g j) (F.sq j) m)
      naturality := fun j k f => by
        ext y
        exact rpl_two q i (F.pr j) (F.pr k) F.prL _ _ (F.prt f) _ _ (F.sq k) _ _ (F.sq j)
          (F.Z.g_comp_transition f) (F.X.g_comp_transition f) m y }

private def Fam.fg (F : Fam J) (q : ℕ) (i m : ℤ) : F.rel q i m ⟶ F.X.fn q i m where
  app j := AddCommGrpCat.ofHom (fgt (ZMod q) (sch.map (F.pr j)) (tw q i) m)
  naturality j k f := by
    ext y
    exact relNat (ZMod q) (tw q i) (sch.map (F.pr j)) (sch.map (F.pr k)) (sch.map (F.Z.t f)) (sch.map (F.X.t f))
      (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, F.prt f]) m y

private def Fam.rs (F : Fam J) (q : ℕ) (i n : ℤ) : F.X.fn q i n ⟶ F.Z.fn q i n where
  app j := AddCommGrpCat.ofHom (pull (ZMod q) (sch.map (F.pr j)) (tw q i) n)
  naturality j k f := by
    ext y
    exact pull_sq _ _ _ _ (F.prt f) q i n y

private def Fam.dl (F : Fam J) (hN : ObsNat) (q : ℕ) [NeZero q] (i n m : ℤ) (h : n + 1 = m) :
    F.Z.fn q i n ⟶ F.rel q i m where
  app j := AddCommGrpCat.ofHom (obsC q (sch.map (F.pr j)) i n m h)
  naturality j k f := by
    ext w
    exact (obsC_nat hN q (sch.map (F.pr j)) (sch.map (F.pr k)) (sch.map (F.Z.t f)) (sch.map (F.X.t f))
      (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, F.prt f]) i n m h w).symm

private def Fam.tri (F : Fam J) (q : ℕ) [NeZero q] (i n m : ℤ) (h : n + 1 = m) (hO : ObsExact) (hN : ObsNat)
    (iY : ∀ j (y : Ht q (sch.obj (F.X.A j)) m i), pull (ZMod q) (sch.map (F.X.g j)) (tw q i) m y = 0 →
      ∃ (k : J) (f : j ⟶ k), pull (ZMod q) (sch.map (F.X.t f)) (tw q i) m y = 0)
    (sY : ∀ y : Ht q (sch.obj F.X.L) n i, ∃ (j : J) (y' : Ht q (sch.obj (F.X.A j)) n i),
      pull (ZMod q) (sch.map (F.X.g j)) (tw q i) n y' = y)
    (iW : ∀ j (w : Ht q (sch.obj (F.Z.A j)) n i), pull (ZMod q) (sch.map (F.Z.g j)) (tw q i) n w = 0 →
      ∃ (k : J) (f : j ⟶ k), pull (ZMod q) (sch.map (F.Z.t f)) (tw q i) n w = 0) : Tri J where
  Rm := F.rel q i m
  Ym := F.X.fn q i m
  Yp := F.X.fn q i n
  Wp := F.Z.fn q i n
  cR := F.co q i m
  cYm := F.X.co q i m
  cYp := F.X.co q i n
  cWp := F.Z.co q i n
  fg := F.fg q i m
  fgL := AddCommGrpCat.ofHom (fgt (ZMod q) (sch.map F.prL) (tw q i) m)
  fg_w j := by
    ext y
    exact relNat (ZMod q) (tw q i) (sch.map (F.pr j)) (sch.map F.prL) (sch.map (F.Z.g j)) (sch.map (F.X.g j))
      (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, F.sq j]) m y
  dl := F.dl hN q i n m h
  dlL := AddCommGrpCat.ofHom (obsC q (sch.map F.prL) i n m h)
  dl_w j := by
    ext w
    exact (obsC_nat hN q (sch.map (F.pr j)) (sch.map F.prL) (sch.map (F.Z.g j)) (sch.map (F.X.g j))
      (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, F.sq j]) i n m h w).symm
  rs := F.rs q i n
  rsL := AddCommGrpCat.ofHom (pull (ZMod q) (sch.map F.prL) (tw q i) n)
  rs_w j := by
    ext y
    exact pull_sq _ _ _ _ (F.sq j) q i n y
  exR j x hx := obsC_exact hO q (sch.map (F.pr j)) i n m h x hx
  exWL w hw := obsC_lift q (sch.map F.prL) i n m h w hw
  cx j y := obsC_pull q (sch.map (F.pr j)) i n m h y
  injYm := iY
  surYp := sY
  injWp := iW

attribute [local instance] Sys.cat Sys.filt Sys.ring

private theorem resY_id {Y B : Scheme.{0}} (p : Y ⟶ B) (U : B.Etale) : resY p (𝟙 U) = 𝟙 _ := by
  apply pullback.hom_ext
  · erw [pullback.lift_fst]; simp
  · erw [pullback.lift_snd]; simp; exact Category.comp_id _

private theorem resYW_id {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) : resYW p ι (𝟙 U) = 𝟙 _ := by
  apply pullback.hom_ext
  · erw [pullback.lift_fst]; simp [resY_id]
  · erw [pullback.lift_snd]; simp

variable {q : ℕ} {i : ℤ} {B W Y : Scheme.{0}} {p : Y ⟶ B} {ι : W ⟶ B} {U : B.Etale} {m : ℤ} {u : U.left}

private def towY (S : Sys q i p ι U m u) : Tow S.J where
  A j := YU p (S.V j)
  t f := resY p (S.tr f)
  t_id j := by rw [S.tr_id, resY_id]
  t_comp f g := by rw [S.tr_comp, resY_comp]
  L := pullback p (S.t ≫ U.hom)
  g := S.gY
  g_comp_transition := S.gY_tr

private def towW (S : Sys q i p ι U m u) : Tow S.J where
  A j := pullback (pullback.snd p (S.V j).hom ≫ (S.V j).hom) ι
  t f := resYW p ι (S.tr f)
  t_id j := by rw [S.tr_id, resYW_id]
  t_comp f g := by rw [S.tr_comp, resYW_comp]
  L := pullback (pullback.snd p (S.t ≫ U.hom) ≫ (S.t ≫ U.hom)) ι
  g := S.gW
  g_comp_transition := S.gW_tr

private def fam (S : Sys q i p ι U m u) : Fam S.J where
  X := towY S
  Z := towW S
  pr j := prU p ι (S.V j)
  prt f := (pullback.lift_fst _ _ _).symm
  prL := prS p ι (S.t ≫ U.hom)
  sq := S.sq

end UpperTheory.Cb.RelativeCohomologyColimit

open UpperTheory.Cb.RelativeCohomologyColimit LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut
  LateralTheory.E.SecondDegreeKilling.Nbhd LateralTheory.E.NeighbourhoodKilling LateralTheory.E.SecondDegreeKilling LateralTheory.E.Bridge_yfiPf in
attribute [local instance] LateralTheory.E.Bridge_yfiPf.Sys.cat LateralTheory.E.Bridge_yfiPf.Sys.filt LateralTheory.E.Bridge_yfiPf.Sys.ring in
theorem UpperTheory.relativeCohomology_colimit_of_exact_of_naturality :
    LateralTheory.E.NeighbourhoodKilling.ObsExact → LateralTheory.E.NeighbourhoodKilling.ObsNat → LateralTheory.E.Bridge_yfiPf.Pack := by
  intro hO hN q _ i B W Y p ι U m u S z
  obtain ⟨j0⟩ : Nonempty S.J := IsFiltered.nonempty
  refine ⟨S.J, inferInstance, inferInstance,
    (fam S).tri q i (m - 1) m (sub_add_cancel m 1) hO hN S.injY S.surY S.injW, j0,
    rY q i p ι (S.a j0) m z, S.A, inferInstance, S.t, S.sh, ?_, ?_⟩
  · intro h
    exact (rpl_two q i (prU p ι U) (prU p ι (S.V j0)) (prS p ι (S.t ≫ U.hom)) _ _ _ _ _ (S.sq j0) (tW p ι U S.t)
      (tY p U S.t) (pullback.lift_fst _ _ _).symm (S.gW_a j0) (S.gY_a j0) m z).trans h
  · intro j f h
    refine ⟨S.V j, S.a j, S.mem j, ?_⟩
    rw [← S.tr_a f, rY_comp]
    exact h
