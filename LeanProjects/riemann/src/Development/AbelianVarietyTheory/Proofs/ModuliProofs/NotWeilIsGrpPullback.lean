import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilPullNoncomm

open GlobalTheory.CommPairing

abbrev oneChart (X : Scheme.{0}) : LB X := ⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩

abbrev manyChart {X : Scheme.{0}} {κ : Type} (v : κ → Γ(X, ⊤)ˣ) : LB X :=
  ⟨κ, fun _ => ⊤, fun i j => res inf_le_left (v i * (v j)⁻¹)⟩

theorem oneChart_isLB (X : Scheme.{0}) : (oneChart X).IsLB where
  cover := top_le_iff.1 fun _ _ => TopologicalSpace.Opens.mem_iSup.2 ⟨PUnit.unit, trivial⟩
  g_self _ := map_one _
  cocycle _ _ _ := by
    show res _ 1 * res _ 1 = res _ 1
    simp only [map_one, _root_.mul_one]

theorem gm_manyChart {X Y : Scheme.{0}} {κ : Type} (v : κ → Γ(X, ⊤)ˣ) (f : Y ⟶ X) (y : Y) (i j : κ) :
    gm f y ((manyChart v).U i ⊓ (manyChart v).U j) ((manyChart v).g i j) = gm f y ⊤ (v i) * (gm f y ⊤ (v j))⁻¹ :=
  (gm_res f y (U := ⊤) (V := ⊤ ⊓ ⊤) inf_le_left ⟨trivial, trivial⟩ _).trans (by rw [map_mul, map_inv])

theorem manyChart_isLB {X : Scheme.{0}} {κ : Type} [Nonempty κ] (v : κ → Γ(X, ⊤)ˣ) : (manyChart v).IsLB where
  cover := top_le_iff.1 fun _ _ => TopologicalSpace.Opens.mem_iSup.2 ⟨Classical.arbitrary κ, trivial⟩
  g_self i := unit_ext fun y hy => by
    rw [gm_res (𝟙 X) y _ hy, map_one, gm_manyChart, mul_inv_cancel]
  cocycle i j k := unit_ext fun y hy => by
    rw [map_mul, gm_res (𝟙 X) y _ hy, gm_res (𝟙 X) y _ hy, gm_res (𝟙 X) y _ hy, gm_manyChart, gm_manyChart,
      gm_manyChart, _root_.mul_assoc, inv_mul_cancel_left]

theorem manyChart_iso {X Y : Scheme.{0}} {κ : Type} (v : κ → Γ(X, ⊤)ˣ) (F : X ⟶ Y) :
    LBIso (manyChart v) ((oneChart Y).pull F) := by
  refine ⟨⟨fun p => res le_top (v p.2)⁻¹⟩, (isGen_iff _).2 fun Z f z j j' k k' hj hj' hk hk' => ?_⟩
  have e : ∀ (j : (oneChart Y).ι) (k : κ), gw (L := oneChart Y) (L' := manyChart v) (F := F)
      ⟨fun p => res le_top (v p.2)⁻¹⟩ f z j k = (gm f z ⊤ (v k))⁻¹ := fun j k =>
    (gm_res f z (V := ((oneChart Y).pull F).U (fun _ => j) ⊓ ⊤) le_top ⟨mem_pull.2 trivial, trivial⟩ _).trans (map_inv _ _)
  rw [e, e, gm_manyChart]
  show _ = gm _ _ _ 1 * _ * _
  rw [map_one, _root_.one_mul, mul_inv_rev, inv_inv, mul_comm (gm f z ⊤ (v k')), mul_inv_cancel_right]

theorem one_isGen {X Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    (⟨fun _ => 1⟩ : LB.Gen (LB.LinComb (oneChart X) φ ε)).IsGen :=
  isGen_of_gm _ fun y j j' _ _ => (map_one _).trans (Eq.symm ((congrArg₂ (· * ·)
    (Finset.prod_eq_one fun k _ => (congrArg (· ^ ε k) (map_one _)).trans (one_zpow _)) (map_one _)).trans
      (_root_.mul_one _)))

variable {S : Scheme.{0}} {G : Over S} [GrpObj G]

theorem weilIs_oneChart (hu : ∀ u : Γ(G.left, ⊤)ˣ, ∃ a : Γ(S, ⊤)ˣ, u = pullU G.hom ⊤ a) {T : Over S} [IsIso T.hom]
    (k : ℤ) (x y : T ⟶ G) : WeilIs G (oneChart _) k x y 1 := by
  intro p
  refine ⟨⊤, trivial, ⟨⟨_, _, one_isGen _ _⟩, ⟨_, _, one_isGen _ _⟩, rfl, rfl⟩, fun θx θy h₁ h₂ => ?_⟩
  have hi : IsIso (overRes (⊤ : T.left.Opens)).hom := by
    show IsIso ((⊤ : T.left.Opens).ι ≫ T.hom)
    have : IsIso (⊤ : T.left.Opens).ι := inferInstanceAs (IsIso T.left.topIso.hom)
    infer_instance
  have e1 : unitRes (⊤ : T.left.Opens) 1 = 1 := map_one _
  rw [e1]
  clear e1 h₁ h₂
  generalize overRes (⊤ : T.left.Opens) = T' at *
  have hs : IsIso (snd T' G).left := inferInstanceAs (IsIso (pullback.snd T'.hom G.hom))
  have key : ∀ θ : ThetaGrp G (oneChart _) k T', ∃ a : Γ(S, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ (T' ⊗ G).left) (z : Z) (J),
      tval θ r z J = gm (r ≫ (T' ⊗ G).hom) z ⊤ a := by
    intro θ
    have le : ⊤ ≤ LB.wchart (oneChart G.left) ![(snd T' G).left, (translPt G θ.pt).left] (fun _ => PUnit.unit) :=
      fun _ _ => Set.mem_iInter.2 fun _ => trivial
    obtain ⟨a, ha⟩ := hu (pullU (inv (snd T' G).left) ⊤ (res le (θ.φ.s fun _ => PUnit.unit)))
    refine ⟨a, fun Z r z J => ?_⟩
    have h := congrArg (gm (r ≫ (snd T' G).left) z ⊤) ha
    have h₁ := gm_pull (r ≫ (snd T' G).left) (inv (snd T' G).left) z ⊤ trivial (res le (θ.φ.s fun _ => PUnit.unit))
    have h₂ := gm_pull (r ≫ (snd T' G).left) G.hom z ⊤ trivial a
    rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id] at h₁
    rw [Category.assoc, Over.w] at h₂
    exact (gm_res r z le trivial _).symm.trans (h₁.symm.trans (h.trans h₂))
  obtain ⟨a, ha⟩ := key θx
  obtain ⟨b, hb⟩ := key θy
  rw [commIsOf_iff (oneChart_isLB _)]
  intro Z r z J _
  rw [ha, ha, hb, hb, Category.assoc, Category.assoc, Over.w, Over.w, map_one, _root_.mul_one, mul_comm]

theorem tval_manyChart {κ : Type} (v : κ → Γ(G.left, ⊤)ˣ) {k : ℤ} {T : Over S} (θ : ThetaGrp G (manyChart v) k T)
    {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ G).left) (z : Z) (J J' : (Z ⟶ G.left) → κ) :
    tval θ r z J = ((gm (r ≫ (snd T G).left) z ⊤ (v (J (r ≫ (snd T G).left))) *
        (gm (r ≫ (snd T G).left) z ⊤ (v (J' (r ≫ (snd T G).left))))⁻¹) ^ k *
      (gm (r ≫ (translPt G θ.pt).left) z ⊤ (v (J (r ≫ (translPt G θ.pt).left))) *
        (gm (r ≫ (translPt G θ.pt).left) z ⊤ (v (J' (r ≫ (translPt G θ.pt).left))))⁻¹) ^ (-k)) * tval θ r z J' := by
  have hJ : ∀ J, Good (manyChart v) z J := fun _ _ => trivial
  refine (gen_trans (φ := ![(snd T G).left, (translPt G θ.pt).left]) (ε := ![k, -k]) θ.isGen r z
    ((hJ J).mem _ r) ((hJ J').mem _ r)).trans ?_
  congr 1
  refine (Finset.prod_congr rfl fun i _ => congrArg (· ^ _) (gm_manyChart v _ z _ _)).trans ?_
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem gm_eq_one_of_commIsOf (u : Γ(G.left, ⊤)ˣ) {T : Over S}
    {θx θy : ThetaGrp G (manyChart (fun b : Bool => if b then u else 1)) 1 T} {c : Γ(T.left, ⊤)ˣ}
    (H : CommIsOf G _ 1 θx θy c) (hn : θx.pt * θy.pt ≠ θy.pt * θx.pt) (z : T.left) :
    ∃ r : T.left ⟶ G.left, gm r z ⊤ u = 1 := by
  classical
  rw [commIsOf_iff (manyChart_isLB _)] at H
  let r : T ⟶ T ⊗ G := lift (𝟙 T) 1
  have s : ∀ x : T ⟶ G, (r.left ≫ (translT G x).left) ≫ (snd T G).left = r.left ≫ (translPt G x).left := fun x => by
    rw [Category.assoc, ← Over.comp_left, translT, lift_snd]
  have q : ∀ x y : T ⟶ G, (r.left ≫ (translT G x).left) ≫ (translPt G y).left = (y * x).left := fun x y => by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    show (r ≫ lift (fst T G) ((fst T G ≫ x) * snd T G)) ≫ ((fst T G ≫ y) * snd T G) = _
    simp [r, MonObj.comp_mul, comp_lift]
  have hPQ : (θy.pt * θx.pt).left ≠ (θx.pt * θy.pt).left := fun h => hn (Over.OverMorphism.ext h.symm)
  let J : (T.left ⟶ G.left) → Bool := fun ψ => decide (ψ = (θx.pt * θy.pt).left)
  have h₁ := H _ r.left z J (fun _ => trivial)
  have h₂ := H _ r.left z (fun _ => false) (fun _ => trivial)
  rw [tval_manyChart _ θx r.left z J (fun _ => false), tval_manyChart _ θy r.left z J (fun _ => false),
    tval_manyChart _ θx _ z J (fun _ => false), tval_manyChart _ θy _ z J (fun _ => false), s, s, q, q] at h₁
  have j₁ : J (θx.pt * θy.pt).left = true := decide_eq_true rfl
  have j₂ : J (θy.pt * θx.pt).left = false := decide_eq_false hPQ
  rw [j₁, j₂] at h₁
  simp only [Bool.false_eq_true, if_false, if_true, map_one, inv_one, _root_.mul_one, zpow_neg, zpow_one] at h₁
  refine ⟨(θx.pt * θy.pt).left, ?_⟩
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul h₁
  have a₂ := congrArg Additive.ofMul h₂
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at a₁ a₂ ⊢
  linear_combination (norm := abel) a₁ - a₂

@[ext] structure Heis (R : Type) where

  a : R

  b : R

  c : R

instance (R : Type) [CommRing R] : Group (Heis R) where
  mul g h := ⟨g.a + h.a, g.b + h.b, g.c + h.c + g.a * h.b⟩
  one := ⟨0, 0, 0⟩
  inv g := ⟨-g.a, -g.b, g.a * g.b - g.c⟩
  mul_assoc g h k := Heis.ext (add_assoc _ _ _) (add_assoc _ _ _) (by
    show g.c + h.c + g.a * h.b + k.c + (g.a + h.a) * k.b = g.c + (h.c + k.c + h.a * k.b) + g.a * (h.b + k.b)
    ring)
  one_mul g := Heis.ext (zero_add _) (zero_add _) (by show 0 + g.c + 0 * g.b = g.c; ring)
  mul_one g := Heis.ext (add_zero _) (add_zero _) (by show g.c + 0 + g.a * 0 = g.c; ring)
  inv_mul_cancel g := Heis.ext (neg_add_cancel _) (neg_add_cancel _) (by
    show g.a * g.b - g.c + g.c + -g.a * g.b = 0; ring)

def Heis.map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') : Heis R →* Heis R' :=
  MonoidHom.mk' (fun g => ⟨f g.a, f g.b, f g.c⟩) fun g h => Heis.ext (map_add f _ _) (map_add f _ _) (by
    show f (g.c + h.c + g.a * h.b) = f g.c + f h.c + f g.a * f h.b
    rw [map_add, map_add, map_mul])

def heisFunctor (S : Scheme.{0}) : (Over S)ᵒᵖ ⥤ GrpCat.{0} where
  obj T := GrpCat.of (Heis Γ(T.unop.left, ⊤))
  map g := GrpCat.ofHom (Heis.map g.unop.left.appTop.hom)
  map_id T := GrpCat.hom_ext (MonoidHom.ext fun x => by
    have e : ∀ a, (𝟙 T : T ⟶ T).unop.left.appTop.hom a = a := fun a =>
      congrArg (fun q => q.hom a) (Scheme.Hom.id_appTop (X := T.unop.left))
    exact Heis.ext (e _) (e _) (e _))
  map_comp g g' := GrpCat.hom_ext (MonoidHom.ext fun x => rfl)

abbrev heisObj (S : Scheme.{0}) : Over S := Over.mk (𝔸(Fin 3; S) ↘ S)

def heisEquiv {S : Scheme.{0}} (T : Over S) : (T ⟶ heisObj S) ≃ Heis Γ(T.left, ⊤) where
  toFun x := ⟨x.left.appTop (AffineSpace.coord S 0), x.left.appTop (AffineSpace.coord S 1),
    x.left.appTop (AffineSpace.coord S 2)⟩
  invFun g := Over.homMk (AffineSpace.homOfVector T.hom ![g.a, g.b, g.c]) (AffineSpace.homOfVector_over _ _)
  left_inv x := Over.OverMorphism.ext (AffineSpace.hom_ext
    ((AffineSpace.homOfVector_over _ _).trans (Over.w x).symm) fun i => by
      refine (AffineSpace.homOfVector_appTop_coord _ _ i).trans ?_
      fin_cases i <;> rfl)
  right_inv g := Heis.ext (AffineSpace.homOfVector_appTop_coord _ _ _) (AffineSpace.homOfVector_appTop_coord _ _ _)
    (AffineSpace.homOfVector_appTop_coord _ _ _)

def heisRep (S : Scheme.{0}) : (heisFunctor S ⋙ forget _).RepresentableBy (heisObj S) where
  homEquiv {T} := heisEquiv T
  homEquiv_comp _ _ := rfl

instance (S : Scheme.{0}) : GrpObj (heisObj S) := GrpObj.ofRepresentableBy _ _ (heisRep S)

theorem heisEquiv_mul {S : Scheme.{0}} {T : Over S} (x y : T ⟶ heisObj S) :
    heisEquiv T (x * y) = heisEquiv T x * heisEquiv T y :=
  ((yonedaGrpObjIsoOfRepresentableBy _ _ (heisRep S)).hom.app (Opposite.op T)).hom.map_mul x y

theorem heisEquiv_comp {S : Scheme.{0}} {T T' : Over S} (g : T' ⟶ T) (x : T ⟶ heisObj S) :
    heisEquiv T' (g ≫ x) = Heis.map g.left.appTop.hom (heisEquiv T x) := rfl

theorem heis_units (S : Scheme.{0}) [IsAffine S] [IsReduced S] (u : Γ((heisObj S).left, ⊤)ˣ) :
    ∃ a : Γ(S, ⊤)ˣ, u = pullU (heisObj S).hom ⊤ a := by
  let e := AffineSpace.isoOfIsAffine (Fin 3) S
  have : IsIso e.hom.appTop := inferInstanceAs (IsIso (e.hom.app ⊤))
  let ψ := (Scheme.ΓSpecIso (.of (MvPolynomial (Fin 3) Γ(S, ⊤)))).inv ≫ e.hom.appTop
  have hψ : ψ = CommRingCat.ofHom (MvPolynomial.eval₂Hom ((𝔸(Fin 3; S) ↘ S).appTop).hom (AffineSpace.coord S)) := by
    show _ ≫ (AffineSpace.isoOfIsAffine (Fin 3) S).hom.appTop = _
    rw [AffineSpace.isoOfIsAffine_hom_appTop, Iso.inv_hom_id_assoc]
  let E := (asIso ψ).commRingCatIsoToRingEquiv
  obtain ⟨a, ha, h⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.1 (u.isUnit.map E.symm)
  refine ⟨ha.unit, Units.ext ?_⟩
  refine (E.apply_symm_apply _).symm.trans ((congrArg E h).trans ?_)
  show ψ.hom (MvPolynomial.C a) = _
  rw [hψ]
  exact MvPolynomial.eval₂Hom_C _ _ _

end GlobalTheory.WeilPullNoncomm

namespace GlobalTheory

open WeilPullNoncomm

theorem not_weilIs_grpPullback : ¬ ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G']
    (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB →
    IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → ∀ (T : Over S') (k : ℤ) (x y : T ⟶ G')
    (x₀ y₀ : Over.mk (T.hom ≫ f) ⟶ G) (c : Γ(T.left, ⊤)ˣ), x₀.left = x.left ≫ φ → y₀.left = y.left ≫ φ →
    (Out.WeilIs G' L' k x y c ↔ Out.WeilIs G L k x₀ y₀ c) := by
  intro H
  let S : Scheme.{0} := Spec (.of ℚ)
  have h2 : IsUnit (2 : Γ(S, ⊤)) := by
    have := (IsUnit.mk0 (2 : ℚ) two_ne_zero).map (Scheme.ΓSpecIso (.of ℚ)).inv.hom
    rwa [map_ofNat] at this
  let G := heisObj S
  let u : Γ(G.left, ⊤)ˣ := pullU G.hom ⊤ h2.unit
  let T : Over S := Over.mk (𝟙 S)
  let x : T ⟶ G := (heisEquiv T).symm ⟨1, 0, 0⟩
  let y : T ⟶ G := (heisEquiv T).symm ⟨0, 1, 0⟩
  have : IsMonHom (Iso.refl G).hom := inferInstanceAs (IsMonHom (𝟙 G))
  have hp := isGrpPullback_of_iso (Iso.refl G)
  have : IsIso (Over.mk (T.hom ≫ 𝟙 S)).hom := inferInstanceAs (IsIso (𝟙 S ≫ 𝟙 S))
  have W := (H S S G G _ _ (oneChart _) (manyChart fun b : Bool => if b then u else 1) (oneChart_isLB _)
    (manyChart_isLB _) hp (manyChart_iso _ _) T 1 x y (pushPt hp.1.w x) (pushPt hp.1.w y) 1 rfl rfl).2
    (weilIs_oneChart (heis_units S) _ _ _)
  obtain ⟨p⟩ : Nonempty S := inferInstance
  obtain ⟨V, hV, ⟨θx, θy, hx, hy⟩, hc⟩ := W p
  have : Nonempty V := ⟨⟨p, hV⟩⟩
  have : Nonempty (⊤ : V.toScheme.Opens) := ⟨⟨⟨p, hV⟩, trivial⟩⟩
  obtain ⟨r, hr⟩ := gm_eq_one_of_commIsOf u (hc θx θy hx hy) (fun h => by
    have e₀ := (heisEquiv_mul θx.pt θy.pt).symm.trans ((congrArg (heisEquiv _) h).trans (heisEquiv_mul θy.pt θx.pt))
    have ex : heisEquiv _ θx.pt = Heis.map V.ι.appTop.hom ⟨1, 0, 0⟩ := (congrArg (heisEquiv _) hx).trans
      ((heisEquiv_comp _ _).trans (congrArg _ ((heisEquiv T).apply_symm_apply _)))
    have ey : heisEquiv _ θy.pt = Heis.map V.ι.appTop.hom ⟨0, 1, 0⟩ := (congrArg (heisEquiv _) hy).trans
      ((heisEquiv_comp _ _).trans (congrArg _ ((heisEquiv T).apply_symm_apply _)))
    rw [ex, ey] at e₀
    have e := congrArg Heis.c e₀
    have e' : V.ι.appTop.hom 0 + V.ι.appTop.hom 0 + V.ι.appTop.hom 1 * V.ι.appTop.hom 1 =
      V.ι.appTop.hom 0 + V.ι.appTop.hom 0 + V.ι.appTop.hom 0 * V.ι.appTop.hom 0 := e
    simp at e') ⟨p, hV⟩
  have e := congrArg Units.val ((gm_pull r G.hom _ ⊤ trivial h2.unit).symm.trans hr)
  replace e := (gm_val (r ≫ G.hom) _ ⊤ trivial h2.unit).symm.trans e
  rw [IsUnit.unit_spec, map_ofNat, map_ofNat, Units.val_one] at e
  have nt : Nontrivial ((overRes V).left.presheaf.stalk (⟨p, hV⟩ : V.toScheme)) :=
    (V.toScheme.toLocallyRingedSpace.isLocalRing ⟨p, hV⟩).toNontrivial
  exact one_ne_zero (α := (overRes V).left.presheaf.stalk (⟨p, hV⟩ : V.toScheme)) (add_left_cancel (a := 1) ((one_add_one_eq_two.trans e).trans (add_zero _).symm))

end GlobalTheory
