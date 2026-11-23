import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsAwayNotMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

section Hom

variable {R : Type} [CommRing R] {M : Over (Spec (CommRingCat.of R))} [GrpObj M]

def preH {X Y : Over (Spec (CommRingCat.of R))} (f : Y ⟶ X) : (X ⟶ M) →* (Y ⟶ M) :=
  MonoidHom.mk' (f ≫ ·) fun a b => MonObj.comp_mul f a b

theorem pre_prod {X Y : Over (Spec (CommRingCat.of R))} (f : Y ⟶ X) {d : ℕ} (v : Fin d → (X ⟶ M)) :
    f ≫ (List.ofFn v).prod = (List.ofFn fun i => f ≫ v i).prod := by
  have h := map_list_prod (preH (M := M) f) (List.ofFn v)
  rw [List.map_ofFn] at h
  exact h

theorem scale_prodPts {d : ℕ} (a : R) (c : Fin d → R) (v : Fin d → (sp (R₀ := R) (DualNumber R) ⟶ M)) :
    spMap (scaleD a) ≫ prodPts c v = prodPts (a • c) v := by
  unfold prodPts
  rw [pre_prod]
  refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
  have hs : (scaleD a).comp (scaleD (c i)) = scaleD ((a • c) i) := by
    apply AlgHom.ext
    intro x
    refine TrivSqZeroExt.ext ?_ ?_
    all_goals (simp only [TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map, AlgHom.comp_apply,
      LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, Pi.smul_apply]; try ring)
  rw [← Category.assoc, spMap_comp, hs]

end Hom

section Push

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
  {P : Type} [CommRing P] [Algebra R' P] [Algebra R P] [IsScalarTower R R' P]

def pushforwardHom : (sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G) →* (sp (R₀ := R) P ⟶ G) :=
  MonoidHom.mk' (pushR G) fun a b => by
    show iotaB ≫ Geo.Tor.pushPt _ (a * b) = (iotaB ≫ Geo.Tor.pushPt _ a) * (iotaB ≫ Geo.Tor.pushPt _ b)
    rw [← MonObj.comp_mul]
    congr 1
    exact map_mul (Geo.Tor.pushHom (Geo.Tor.isGrpPullback_pullback G (fB R R')) _) a b

theorem pushR_prod {d : ℕ} (v : Fin d → (sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G)) :
    pushR G (List.ofFn v).prod = (List.ofFn fun i => pushR G (v i)).prod := by
  have h := map_list_prod (pushforwardHom (R := R) (R' := R') (P := P) G) (List.ofFn v)
  rw [List.map_ofFn] at h
  exact h

end Push

theorem isGrpPullback_factor {S S' S'' : Scheme.{0}} {G : Over S} [GrpObj G] {G'' : Over S''} [GrpObj G'']
    (f : S' ⟶ S) (g : S'' ⟶ S') {F : G''.left ⟶ G.left} (h : Geo.Tor.IsGrpPullback G'' G (g ≫ f) F) :
    Geo.Tor.IsGrpPullback G'' ((Over.pullback f).obj G) g
      (pullback.lift F (G''.hom ≫ g) (by rw [h.1.w, Category.assoc])) := by
  have hfst : pullback.lift F (G''.hom ≫ g) (by rw [h.1.w, Category.assoc]) ≫
      pullback.fst G.hom f = F := pullback.lift_fst _ _ _
  have hsnd : pullback.lift F (G''.hom ≫ g) (by rw [h.1.w, Category.assoc]) ≫
      pullback.snd G.hom f = G''.hom ≫ g := pullback.lift_snd _ _ _
  have hP := Geo.Tor.isGrpPullback_pullback G f
  refine ⟨?_, ?_⟩
  · refine IsPullback.of_right ?_ hsnd (IsPullback.of_hasPullback G.hom f)
    rw [hfst]
    exact h.1
  · intro T x y x₀ y₀ hx hy
    apply pullback.hom_ext
    · let x₀' : Over.mk ((Over.mk (T.hom ≫ g)).hom ≫ f) ⟶ G :=
        Over.homMk (x₀.left ≫ pullback.fst G.hom f) (by
          rw [Category.assoc, pullback.condition, ← Category.assoc]
          exact congrArg (· ≫ f) (Over.w x₀))
      let y₀' : Over.mk ((Over.mk (T.hom ≫ g)).hom ≫ f) ⟶ G :=
        Over.homMk (y₀.left ≫ pullback.fst G.hom f) (by
          rw [Category.assoc, pullback.condition, ← Category.assoc]
          exact congrArg (· ≫ f) (Over.w y₀))
      let x₀'' : Over.mk (T.hom ≫ g ≫ f) ⟶ G :=
        Over.homMk (x.left ≫ F) (by
          rw [Category.assoc, h.1.w]
          simpa using (Over.w x) =≫ (g ≫ f))
      let y₀'' : Over.mk (T.hom ≫ g ≫ f) ⟶ G :=
        Over.homMk (y.left ≫ F) (by
          rw [Category.assoc, h.1.w]
          simpa using (Over.w y) =≫ (g ≫ f))
      have e1 : (x₀' * y₀').left = (x₀ * y₀).left ≫ pullback.fst G.hom f :=
        hP.2 _ x₀ y₀ x₀' y₀' rfl rfl
      have e2 : (x₀'' * y₀'').left = (x * y).left ≫ F := h.2 T x y x₀'' y₀'' rfl rfl
      have e3 : (x₀' * y₀').left = (x₀'' * y₀'').left := by
        refine Geo.Tor.mul_left_congr (Category.assoc T.hom g f) x₀' y₀' x₀'' y₀'' ?_ ?_
        · show x₀.left ≫ pullback.fst G.hom f = x.left ≫ F
          rw [hx, Category.assoc, hfst]
        · show y₀.left ≫ pullback.fst G.hom f = y.left ≫ F
          rw [hy, Category.assoc, hfst]
      rw [Category.assoc, hfst, ← e1, e3, e2]
    · rw [Category.assoc, hsnd, ← Category.assoc, Over.w (x * y)]
      exact Over.w (x₀ * y₀)

end ReciprocityTheory.ChartRestriction.G.Chart
