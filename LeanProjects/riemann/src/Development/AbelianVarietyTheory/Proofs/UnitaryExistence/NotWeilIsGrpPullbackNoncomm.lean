import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem weilIs_baseChange_of_comm : ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] [IsCommMonObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (_ : IsGrpPullback G' G f φ) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → LBIso L' (L.pull φ) → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ S') (n : ℤ) (x' y' : Over.mk t ⟶ G') (x y : Over.mk (t ≫ f) ⟶ G) (c : Rˣ), x.left = x'.left ≫ φ → y.left = y'.left ≫ φ → (Out.WeilIs G' L' n x' y' (unitOn c) ↔ Out.WeilIs G L n x y (unitOn c)) :=
  fun S S' G G' _ _ _ f φ h L L' hL hL' hw _ _ t n x' y' x y c ex ey =>
    weilIs_grpPullback_of_comm' S S' G G' f φ L L' hL hL' h hw (Over.mk t) n x' y' x y (unitOn c) ex ey

namespace WeilNoncomm

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.H1

def oneChart (X : Scheme.{0}) : LB X := ⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩

def sgn (R : Type) [CommRing R] (b : Bool) : Rˣ := cond b (-1) 1

theorem sgn_xor (R : Type) [CommRing R] (a b : Bool) : sgn R (xor a b) = sgn R a * sgn R b := by
  cases a <;> cases b <;> simp [sgn]

theorem sgn_mul_self (R : Type) [CommRing R] (a : Bool) : sgn R a * sgn R a = 1 := by
  cases a <;> simp [sgn]

def twoCharts (X : Scheme.{0}) : LB X := ⟨Bool, fun _ => ⊤, fun i j => sgn _ (xor i j)⟩

theorem res_sgn {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (b : Bool) : res h (sgn Γ(X, U) b) = sgn _ b := by
  cases b
  · exact map_one _
  · exact Units.ext ((map_neg (X.presheaf.map (homOfLE h).op).hom 1).trans (congrArg Neg.neg (map_one _)))

theorem gm_neg_one {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) :
    gm f y U (-1) = -1 := by
  apply Units.ext
  rw [gm_val f y U h]
  simp

theorem gm_sgn {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (b : Bool) :
    gm f y U (sgn _ b) = sgn _ b := by
  cases b
  · exact map_one _
  · exact gm_neg_one f y U h

theorem oneChart_isLB (X : Scheme.{0}) : (oneChart X).IsLB :=
  ⟨top_unique (le_iSup (oneChart X).U PUnit.unit), fun _ => map_one _, fun _ _ _ =>
    ((congrArg₂ (· * ·) (map_one _) (map_one _)).trans (_root_.one_mul _)).trans (map_one _).symm⟩

theorem twoCharts_isLB (X : Scheme.{0}) : (twoCharts X).IsLB :=
  ⟨top_unique (le_iSup (twoCharts X).U true), fun i => (res_sgn _ _).trans (by cases i <;> rfl), fun (i j k : Bool) =>
    ((congrArg₂ (· * ·) (res_sgn _ _) (res_sgn _ _)).trans (by
      cases i <;> cases j <;> cases k <;> simp [sgn])).trans (res_sgn _ _).symm⟩

theorem twoCharts_iso {X Y : Scheme.{0}} (φ : Y ⟶ X) : LBIso (twoCharts Y) ((oneChart X).pull φ) := by
  refine ⟨⟨fun p => sgn _ p.2⟩, (isGen_iff _).2 fun Z f z j j' (k k' : Bool) hj hj' hk hk' => ?_⟩
  have v : ∀ (j : PUnit) (k : Bool), gw (L := oneChart X) (L' := twoCharts Y) (F := φ)
      ⟨fun p => sgn _ p.2⟩ f z j k = sgn _ k := fun j k =>
    gm_sgn f z (((oneChart X).pull φ).U (fun _ => j) ⊓ ⊤) ⟨mem_pull.2 trivial, trivial⟩ k
  have g : gm f z ((twoCharts Y).U k ⊓ (twoCharts Y).U k') ((twoCharts Y).g k k') = sgn _ (xor k k') :=
    gm_sgn f z (⊤ ⊓ ⊤) ⟨trivial, trivial⟩ _
  have o : gm (f ≫ φ) z ((oneChart X).U j ⊓ (oneChart X).U j') ((oneChart X).g j j') = 1 := map_one _
  refine (v j k).trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg₂ (fun a b => a * b⁻¹) o g) (v j' k')).symm)
  cases k <;> cases k' <;> simp [sgn]

variable {S : Scheme.{0}} (G : Over S) [GrpObj G]

theorem weilIs_oneChart {T : Over S} (k : ℤ) (x y : T ⟶ G)
    (hu : ∀ u : Γ((overRes (T := T) ⊤ ⊗ G).left, ⊤)ˣ, u = 1 ∨ u = -1) : WeilIs G (oneChart G.left) k x y 1 := by
  intro p
  have ex : ∀ a : overRes (T := T) ⊤ ⟶ G, ∃ θ : ThetaGrp G (oneChart G.left) k (overRes (T := T) ⊤), θ.pt = a :=
    fun a => ⟨⟨a, ⟨fun _ => 1⟩, isGen_of_gm _ fun y j j' _ _ => by
      have : trF (L := oneChart G.left) ![(snd (overRes (T := T) ⊤) G).left, (translPt G a).left] ![k, -k] (𝟙 _) y j j' = 1 :=
        Finset.prod_eq_one fun i _ => (congrArg (· ^ _) (map_one _)).trans (one_zpow _)
      exact (map_one _).trans ((congrArg₂ (· * ·) this (map_one _)).trans (_root_.one_mul _)).symm⟩, rfl⟩
  obtain ⟨a, ha⟩ := ex (overResι ⊤ ≫ x)
  obtain ⟨b, hb⟩ := ex (overResι ⊤ ≫ y)
  refine ⟨⊤, trivial, ⟨a, b, ha, hb⟩, fun θx θy _ _ => corr_of_val (oneChart_isLB _) fun z J hJ => ?_⟩
  have sg : ∀ θ : ThetaGrp G (oneChart G.left) k (overRes (T := T) ⊤), ∃ e, ∀ r, val θ.φ r z J = e := fun θ => by
    have le : (⊤ : (overRes (T := T) ⊤ ⊗ G).left.Opens) ≤ LB.wchart (oneChart G.left)
        ![(snd (overRes (T := T) ⊤) G).left, (translPt G θ.pt).left] (fun _ => PUnit.unit) :=
      fun _ _ => Set.mem_iInter.2 fun _ => trivial
    have e : ∀ r, val θ.φ r z J = gm r z ⊤ (res le (θ.φ.s fun _ => PUnit.unit)) := fun r =>
      (gm_res r z le trivial _).symm
    rcases hu (res le (θ.φ.s fun _ => PUnit.unit)) with h | h
    · exact ⟨1, fun r => (e r).trans ((congrArg _ h).trans (map_one _))⟩
    · exact ⟨-1, fun r => (e r).trans ((congrArg _ h).trans (gm_neg_one _ _ _ trivial))⟩
  obtain ⟨e, he⟩ := sg θx
  obtain ⟨e', he'⟩ := sg θy
  refine ((val_mul hJ _ _ _).trans (congrArg (val θx.φ (𝟙 _) z J * ·) (val_pull hJ _ _ _))).trans
    (Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg (val θy.φ (𝟙 _) z J * ·) (val_pull hJ _ _ _))) (val_constGen _ _ _ _ _))).symm)
  have u : unitRes (T := T) ⊤ 1 = 1 := map_one _
  rw [he, he', he, he', u, map_one, _root_.mul_one, mul_comm]

def loc {L : LB G.left} {k : ℤ} {T : Over S} (z : T.left) (θ : ThetaGrp G L k T) (a : T ⟶ G) (i j : L.ι) :
    (T.left.presheaf.stalk z)ˣ :=
  gm (lift (𝟙 T) a).left z (LB.wchart L ![(snd T G).left, (translPt G θ.pt).left] ![i, j]) (θ.φ.s ![i, j])

theorem lift_translPt {T : Over S} (a b : T ⟶ G) : lift (𝟙 T) a ≫ translPt G b = b * a := by
  show lift (𝟙 T) a ≫ ((fst T G ≫ b) * snd T G) = _
  rw [MonObj.comp_mul, lift_snd, lift_fst_assoc, Category.id_comp]

theorem lift_translT {T : Over S} (b : T ⟶ G) :
    (lift (𝟙 T) (1 : T ⟶ G)).left ≫ (translT G b).left = (lift (𝟙 T) b).left := by
  rw [← Over.comp_left, translT, comp_lift, lift_fst, lift_translPt, _root_.mul_one]

theorem val_eq_loc {L : LB G.left} {k : ℤ} {T : Over S} (z : T.left) (θ : ThetaGrp G L k T) (a : T ⟶ G)
    (J : (T.left ⟶ G.left) → L.ι) :
    val θ.φ (lift (𝟙 T) a).left z J = loc G z θ a (J a.left) (J (θ.pt * a).left) :=
  val_of _ _ z J _ fun i => by
    fin_cases i
    · show J ((lift (𝟙 T) a).left ≫ (snd T G).left) = J a.left
      rw [← Over.comp_left, lift_snd]
    · show J ((lift (𝟙 T) a).left ≫ (translPt G θ.pt).left) = J (θ.pt * a).left
      rw [← Over.comp_left, lift_translPt]

theorem loc_comm {L : LB G.left} {k : ℤ} {T : Over S} (z : T.left) {θx θy : ThetaGrp G L k T} {c : Γ(T.left, ⊤)ˣ}
    (H : CommIsOf G L k θx θy c) (J : (T.left ⟶ G.left) → L.ι) (hJ : Good L z J) :
    loc G z θx 1 (J (1 : T ⟶ G).left) (J θx.pt.left) * loc G z θy θx.pt (J θx.pt.left) (J (θy.pt * θx.pt).left) =
      loc G z θy 1 (J (1 : T ⟶ G).left) (J θy.pt.left) * loc G z θx θy.pt (J θy.pt.left) (J (θx.pt * θy.pt).left) *
        gm ((lift (𝟙 T) (1 : T ⟶ G)).left ≫ (fst T G).left) z ⊤ c := by
  have a₁ := val_eq_loc G z θx 1 J
  have a₂ := val_eq_loc G z θy θx.pt J
  have a₃ := val_eq_loc G z θy 1 J
  have a₄ := val_eq_loc G z θx θy.pt J
  rw [_root_.mul_one] at a₁ a₃
  rw [← lift_translT] at a₂ a₄
  rw [← a₁, ← a₂, ← a₃, ← a₄]
  exact ((val_mul hJ _ _ _).trans (congrArg (val θx.φ (lift (𝟙 T) (1 : T ⟶ G)).left z J * ·)
    (val_pull hJ _ _ _))).symm.trans ((val_corr hJ H (lift (𝟙 T) (1 : T ⟶ G)).left).trans
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg (val θy.φ (lift (𝟙 T) (1 : T ⟶ G)).left z J * ·) (val_pull hJ _ _ _))) (val_constGen _ _ _ _ _))))

theorem loc_twoCharts {T : Over S} (z : T.left) (θ : ThetaGrp G (twoCharts G.left) 1 T) (a : T ⟶ G) :
    loc G z θ a false true = -loc G z θ a false false := by
  have k₄ := gen_trans θ.isGen (lift (𝟙 T) a).left z (j := ![false, true]) (j' := ![false, false])
    (Set.mem_iInter.2 fun _ => trivial) (Set.mem_iInter.2 fun _ => trivial)
  refine k₄.trans (Eq.trans (congrArg (· * loc G z θ a false false) ?_) (neg_one_mul _))
  rw [trF, Fin.prod_univ_two]
  refine (congrArg₂ (fun a b => a ^ (1 : ℤ) * b ^ (-1 : ℤ)) (gm_sgn _ z (⊤ ⊓ ⊤) ⟨trivial, trivial⟩ false)
      (gm_sgn _ z (⊤ ⊓ ⊤) ⟨trivial, trivial⟩ true)).trans ?_
  simp [sgn]

theorem not_commIsOf_twoCharts {T : Over S} (θx θy : ThetaGrp G (twoCharts G.left) 1 T) (c : Γ(T.left, ⊤)ˣ)
    (z : T.left) (h2 : IsUnit (2 : Γ(T.left, ⊤))) (h₁ : θy.pt * θx.pt ≠ 1) (hx : θy.pt * θx.pt ≠ θx.pt)
    (hy : θy.pt * θx.pt ≠ θy.pt) (hxy : θy.pt * θx.pt ≠ θx.pt * θy.pt) : ¬ CommIsOf G (twoCharts G.left) 1 θx θy c := by
  intro H
  obtain ⟨J, hJ, hJ'⟩ : ∃ J : (T.left ⟶ G.left) → Bool, J (θy.pt * θx.pt).left = true ∧
      ∀ {a : T ⟶ G}, θy.pt * θx.pt ≠ a → J a.left = false := by
    classical
    exact ⟨fun ψ => decide (ψ = (θy.pt * θx.pt).left), decide_eq_true rfl, fun h => decide_eq_false fun e =>
      h (Over.OverMorphism.ext e.symm)⟩
  have k₁ := loc_comm G z H (fun _ => false) (fun _ => trivial)
  have k₂ := loc_comm G z H J (fun _ => trivial)
  rw [hJ, hJ' h₁, hJ' hx, hJ' hy, hJ' hxy, loc_twoCharts] at k₂
  have k₃ : -loc G z θy θx.pt false false = loc G z θy θx.pt false false := mul_left_cancel (k₂.trans k₁.symm)
  have k₅ : (-1 : (T.left.presheaf.stalk z)ˣ) = 1 := mul_eq_right.1 ((neg_one_mul _).trans k₃)
  have k₇ : (-1 : T.left.presheaf.stalk z) = 1 := congrArg Units.val k₅
  have k₈ := h2.map (T.left.presheaf.germ ⊤ z trivial).hom
  rw [map_ofNat, show (2 : T.left.presheaf.stalk z) = 0 by linear_combination -k₇] at k₈
  exact not_isUnit_zero k₈

@[ext] structure Heis (R : Type) where

  a : R

  b : R

  c : R

namespace Heis

variable {R R' : Type} [CommRing R] [CommRing R']

instance : Mul (Heis R) := ⟨fun g h => ⟨g.a + h.a, g.b + h.b, g.c + h.c + g.a * h.b⟩⟩
instance : One (Heis R) := ⟨⟨0, 0, 0⟩⟩
instance : Inv (Heis R) := ⟨fun g => ⟨-g.a, -g.b, -g.c + g.a * g.b⟩⟩

theorem mul_def (g h : Heis R) : g * h = ⟨g.a + h.a, g.b + h.b, g.c + h.c + g.a * h.b⟩ := rfl
theorem one_def : (1 : Heis R) = ⟨0, 0, 0⟩ := rfl
theorem inv_def (g : Heis R) : g⁻¹ = ⟨-g.a, -g.b, -g.c + g.a * g.b⟩ := rfl

instance : Group (Heis R) := Group.ofLeftAxioms
  (fun g h k => by ext <;> simp only [mul_def] <;> ring)
  (fun g => by ext <;> simp [mul_def, one_def])
  (fun g => by ext <;> simp [mul_def, one_def, inv_def])

def map (f : R →+* R') : Heis R →* Heis R' :=
  MonoidHom.mk' (fun g => ⟨f g.a, f g.b, f g.c⟩) fun g h => by ext <;> simp [mul_def]

end Heis

def heisFunctor (S : Scheme.{0}) : (Over S)ᵒᵖ ⥤ GrpCat.{0} where
  obj T := GrpCat.of (Heis Γ(T.unop.left, ⊤))
  map f := GrpCat.ofHom (Heis.map f.unop.left.appTop.hom)
  map_id T := by
    ext g <;> simp [Heis.map]
  map_comp f g := rfl

abbrev heisScheme (S : Scheme.{0}) : Over S := Over.mk (𝔸(Fin 3; S) ↘ S)

def heisRepr (S : Scheme.{0}) : (heisFunctor S ⋙ forget _).RepresentableBy (heisScheme S) where
  homEquiv {T} :=
    { toFun := fun f => (⟨f.left.appTop (AffineSpace.coord S 0), f.left.appTop (AffineSpace.coord S 1),
        f.left.appTop (AffineSpace.coord S 2)⟩ : Heis Γ(T.left, ⊤))
      invFun := fun g : Heis Γ(T.left, ⊤) => Over.homMk (AffineSpace.homOfVector T.hom ![g.a, g.b, g.c])
        (AffineSpace.homOfVector_over _ _)
      left_inv := fun f => Over.OverMorphism.ext (AffineSpace.hom_ext
        ((AffineSpace.homOfVector_over _ _).trans (Over.w f).symm) fun i =>
          (AffineSpace.homOfVector_appTop_coord _ _ i).trans (by fin_cases i <;> rfl))
      right_inv := fun g => Heis.ext (AffineSpace.homOfVector_appTop_coord _ _ 0)
        (AffineSpace.homOfVector_appTop_coord _ _ 1) (AffineSpace.homOfVector_appTop_coord _ _ 2) }
  homEquiv_comp f g := rfl

@[reducible] def heisGrp (S : Scheme.{0}) : GrpObj (heisScheme S) := GrpObj.ofRepresentableBy _ _ (heisRepr S)

attribute [local instance] heisGrp

def heisPt {S : Scheme.{0}} (T : Over S) : (T ⟶ heisScheme S) →* Heis Γ(T.left, ⊤) :=
  ((yonedaGrpObjIsoOfRepresentableBy _ _ (heisRepr S)).hom.app (Opposite.op T)).hom

theorem heisPt_eq {S : Scheme.{0}} {T : Over S} (f : T ⟶ heisScheme S) :
    heisPt T f = ⟨f.left.appTop (AffineSpace.coord S 0), f.left.appTop (AffineSpace.coord S 1),
      f.left.appTop (AffineSpace.coord S 2)⟩ := rfl

def heisMk {S : Scheme.{0}} (T : Over S) (a b c : Γ(T.left, ⊤)) : T ⟶ heisScheme S :=
  Over.homMk (AffineSpace.homOfVector T.hom ![a, b, c]) (AffineSpace.homOfVector_over _ _)

theorem heisPt_comp_mk {S : Scheme.{0}} {T T' : Over S} (σ : T' ⟶ T) (a b c : Γ(T.left, ⊤)) :
    heisPt T' (σ ≫ heisMk T a b c) = ⟨σ.left.appTop.hom a, σ.left.appTop.hom b, σ.left.appTop.hom c⟩ :=
  Heis.ext (congrArg σ.left.appTop.hom (AffineSpace.homOfVector_appTop_coord T.hom ![a, b, c] 0))
    (congrArg σ.left.appTop.hom (AffineSpace.homOfVector_appTop_coord T.hom ![a, b, c] 1))
    (congrArg σ.left.appTop.hom (AffineSpace.homOfVector_appTop_coord T.hom ![a, b, c] 2))

theorem not_weilIs_heis {S : Scheme.{0}} (T : Over S) (p : T.left) (h2 : IsUnit (2 : Γ(T.left, ⊤)))
    (c : Γ(T.left, ⊤)ˣ) :
    ¬ WeilIs (heisScheme S) (twoCharts _) 1 (heisMk T 1 0 0) (heisMk T 0 1 0) c := by
  intro H
  obtain ⟨V, hV, ⟨θx, θy, hx, hy⟩, H⟩ := H p
  have ex : heisPt _ θx.pt = ⟨1, 0, 0⟩ := by rw [hx, heisPt_comp_mk, map_one, map_zero]
  have ey : heisPt _ θy.pt = ⟨0, 1, 0⟩ := by rw [hy, heisPt_comp_mk, map_one, map_zero]
  have nt : (1 : Γ((overRes V).left, ⊤)) ≠ 0 := by
    let z : (overRes V).left := (⟨p, hV⟩ : V.toScheme)
    exact fun e => one_ne_zero ((map_one _).symm.trans ((congrArg ((overRes V).left.presheaf.germ ⊤ z trivial).hom e).trans
      (map_zero _)))
  have u2 := h2.map (overResι V).left.appTop.hom
  rw [map_ofNat] at u2
  refine not_commIsOf_twoCharts _ θx θy _ (⟨p, hV⟩ : V.toScheme) u2 ?_ ?_ ?_ ?_ (H θx θy hx hy) <;> intro e <;>
    have e' := congrArg (heisPt _) e <;>
    simp [map_mul, ex, ey, Heis.mul_def, Heis.one_def, nt, nt.symm] at e'

theorem unit_heis {T : Over (Sp (ZMod 3))} [IsIso T.hom] (u : Γ((T ⊗ heisScheme (Sp (ZMod 3))).left, ⊤)ˣ) :
    u = 1 ∨ u = -1 := by
  have : IsIso (snd T (heisScheme (Sp (ZMod 3)))).left :=
    inferInstanceAs (IsIso (pullback.snd T.hom (heisScheme (Sp (ZMod 3))).hom))
  let i : (T ⊗ heisScheme (Sp (ZMod 3))).left ≅ Spec (CommRingCat.of (MvPolynomial (Fin 3) (ZMod 3))) :=
    asIso (snd T (heisScheme (Sp (ZMod 3)))).left ≪≫ AffineSpace.SpecIso (Fin 3) (CommRingCat.of (ZMod 3))
  have : IsIso i.hom.appTop := inferInstanceAs (IsIso (i.hom.app ⊤))
  let e : MvPolynomial (Fin 3) (ZMod 3) ≃+* Γ((T ⊗ heisScheme (Sp (ZMod 3))).left, ⊤) :=
    ((Scheme.ΓSpecIso _).symm ≪≫ asIso i.hom.appTop).commRingCatIsoToRingEquiv
  obtain ⟨r, hr, h⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.1 (u.isUnit.map e.symm)
  have h' : u.val = e (MvPolynomial.C r) := by rw [← h, RingEquiv.apply_symm_apply]
  have : r = 1 ∨ r = -1 := by
    have : ∀ r : ZMod 3, r ≠ 0 → r = 1 ∨ r = -1 := by decide
    exact this r hr.ne_zero
  rcases this with rfl | rfl
  · exact Or.inl (Units.ext (by simpa using h'))
  · exact Or.inr (Units.ext (by simpa using h'))

end WeilNoncomm

open WeilNoncomm in

theorem not_weilIs_baseChange_noncomm : ¬ ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (_ : IsGrpPullback G' G f φ) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → LBIso L' (L.pull φ) → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ S') (n : ℤ) (x' y' : Over.mk t ⟶ G') (x y : Over.mk (t ≫ f) ⟶ G) (c : Rˣ), x.left = x'.left ≫ φ → y.left = y'.left ≫ φ → (Out.WeilIs G' L' n x' y' (unitOn c) ↔ Out.WeilIs G L n x y (unitOn c)) := by
  intro H
  let _ := heisGrp (Sp (ZMod 3))
  have : IsMonHom (Iso.refl (heisScheme (Sp (ZMod 3)))).hom := inferInstanceAs (IsMonHom (𝟙 _))
  have hp := isGrpPullback_of_iso (Iso.refl (heisScheme (Sp (ZMod 3))))
  have u1 : unitOn (1 : (ZMod 3)ˣ) = 1 := map_one _
  have h := H _ _ _ _ _ _ hp _ _ (oneChart_isLB _) (twoCharts_isLB _) (twoCharts_iso _) (ZMod 3) (𝟙 _) 1
    (heisMk _ 1 0 0) (heisMk _ 0 1 0) (pushPt hp.1.w (heisMk (Over.mk (𝟙 _)) 1 0 0))
    (pushPt hp.1.w (heisMk (Over.mk (𝟙 _)) 0 1 0)) 1 rfl rfl
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : IsUnit (2 : Γ(Sp (ZMod 3), ⊤)) := by
    have := (show IsUnit (2 : ZMod 3) from IsUnit.of_mul_eq_one 2 rfl).map (Scheme.ΓSpecIso (CommRingCat.of (ZMod 3))).inv.hom
    rwa [map_ofNat] at this
  refine not_weilIs_heis (Over.mk (𝟙 (Sp (ZMod 3)))) (⊥ : PrimeSpectrum (ZMod 3)) h2 _ (h.2 ?_)
  rw [u1]
  have : IsIso (⊤ : (Sp (ZMod 3)).Opens).ι := inferInstanceAs (IsIso (Sp (ZMod 3)).topIso.hom)
  have : IsIso (Out.overRes (T := Over.mk (𝟙 (Sp (ZMod 3)) ≫ 𝟙 _)) ⊤).hom :=
    inferInstanceAs (IsIso ((⊤ : (Sp (ZMod 3)).Opens).ι ≫ 𝟙 _ ≫ 𝟙 _))
  exact weilIs_oneChart _ 1 _ _ unit_heis

theorem not_weilIs_grpPullback_noncomm : ¬ ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → ∀ (T : Over S') (k : ℤ) (x y : T ⟶ G') (x₀ y₀ : Over.mk (T.hom ≫ f) ⟶ G) (c : Γ(T.left, ⊤)ˣ), x₀.left = x.left ≫ φ → y₀.left = y.left ≫ φ → (Out.WeilIs G' L' k x y c ↔ Out.WeilIs G L k x₀ y₀ c) :=
  fun H => not_weilIs_baseChange_noncomm fun S S' G G' _ _ f φ h L L' hL hL' hw _ _ t n x' y' x y c ex ey =>
    H S S' G G' f φ L L' hL hL' h hw (Over.mk t) n x' y' x y (unitOn c) ex ey

end GlobalTheory
