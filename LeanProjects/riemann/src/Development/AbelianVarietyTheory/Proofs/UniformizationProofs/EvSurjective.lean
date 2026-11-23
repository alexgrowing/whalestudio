import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsNilpotentOfRd

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.CubeLift

open SplitTorus (ev univPt ptOf pull bcMap ofVal valHom)
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht (chi torusFst)

section Expand

variable {S S' : Scheme.{0}} {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {R : CommRingCat.{0}}

private theorem app_global_comp_apply {U V W' : Scheme.{0}} (f : U ⟶ V) (g : V ⟶ W') (u : Γ(W', ⊤)) :
    (f ≫ g).appTop.hom u = f.appTop.hom (g.appTop.hom u) := by
  rfl

private theorem splitTorus_pull_comp {B : CommRingCat.{0}} {s : Spec B ⟶ S}
    (g : Over.mk s ⟶ splitTorus S Y) (h : splitTorus S Y ⟶ splitTorus S X) (u : Γ((splitTorus S X).left, ⊤)) :
    pull (g ≫ h) u = pull g (h.left.appTop.hom u) := by
  simp only [SplitTorus.pull, RingHom.comp_apply, Over.comp_left, app_global_comp_apply]

theorem ev_torusMap (t : Spec R ⟶ S) (φ : X →+ Y) (u : Γ((splitTorus S X).left, ⊤)) :
    ev t ((SplitTorus.torusMap S φ).left.appTop.hom u) = mv φ (ev t u) := by
  have key : ∀ hs, univPt Y t ≫ SplitTorus.torusMap S φ =
      ptOf (B := CommRingCat.of (AddMonoidAlgebra R Y)) t (mv φ) hs := by
    intro hs
    refine SplitTorus.pull_ext fun a => ?_
    rw [SplitTorus.pull_ptOf, splitTorus_pull_comp, SplitTorus.torusMap_appTop_chi]
    change ev t _ = _
    rw [SplitTorus.ev_chi, SplitTorus.ev_chi, mv_single]
  have hs : Spec.map (CommRingCat.ofHom ((mv φ : AddMonoidAlgebra R X →+* AddMonoidAlgebra R Y).comp
      (algebraMap R (AddMonoidAlgebra R X)))) ≫ t =
      Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R Y))) ≫ t := by
    congr 3
    ext r
    simp [mv]
  change pull (univPt Y t) _ = _
  rw [← splitTorus_pull_comp, key hs, SplitTorus.pull_ptOf]

theorem ev_bcMap (f : S' ⟶ S) (t : Spec R ⟶ S') (u : Γ((splitTorus S X).left, ⊤)) :
    ev t ((bcMap f X).appTop.hom u) = ev (t ≫ f) u := by
  have e : (univPt X t).left ≫ bcMap f X = (univPt X (t ≫ f)).left := by
    refine splitTorus_left_hom_ext _ _ ?_ fun χ => ?_
    · simp [SplitTorus.bcMap_hom]
    · have h0 : (Scheme.ΓSpecIso _).hom.hom (SplitTorus.val (univPt X t) χ) =
          (Scheme.ΓSpecIso _).hom.hom (SplitTorus.val (univPt X (t ≫ f)) χ) := by
        rw [← SplitTorus.pull_chi, ← SplitTorus.pull_chi]
        exact (SplitTorus.ev_chi t χ).trans (SplitTorus.ev_chi (t ≫ f) χ).symm
      have h1 := congrArg (Scheme.ΓSpecIso _).inv.hom h0
      simp only [Iso.hom_inv_id_apply] at h1
      rw [SplitTorus.val_eq, SplitTorus.val_eq] at h1
      rw [app_global_comp_apply, SplitTorus.charUnit_val, SplitTorus.bcMap_appTop_chi]
      exact h1
  change pull (univPt X t) _ = pull (univPt X (t ≫ f)) u
  simp only [SplitTorus.pull, RingHom.comp_apply, ← e, app_global_comp_apply]

theorem ev_injective : Function.Injective (ev (X := X) (𝟙 (Spec R))) := by
  intro u v h
  refine SplitTorus.eq_of_ev fun B t => ?_
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ ≫ 𝟙 _ = t := ⟨Spec.preimage t, by simp⟩
  rw [SplitTorus.ev_comp, SplitTorus.ev_comp, h]

private theorem ev_base_apply (r : R) :
    ev (X := X) (𝟙 (Spec R)) ((splitTorus (Spec R) X).hom.appTop.hom ((Scheme.ΓSpecIso R).inv.hom r)) =
      AddMonoidAlgebra.single 0 r := by
  change pull (univPt X _) _ = _
  have hw := Over.w (univPt X (𝟙 (Spec R)))
  simp only [SplitTorus.pull, RingHom.comp_apply]
  rw [← app_global_comp_apply, hw]
  erw [Category.comp_id]
  erw [SplitTorus.specMap_appTop_apply, Iso.inv_hom_id_apply]
  rfl

theorem ev_surjective : Function.Surjective (ev (X := X) (𝟙 (Spec R))) := by
  intro w
  induction w using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add p q hp hq =>
    obtain ⟨a, rfl⟩ := hp
    obtain ⟨b, rfl⟩ := hq
    exact ⟨a + b, map_add _ _ _⟩
  | single x r =>
    refine ⟨(splitTorus (Spec R) X).hom.appTop.hom ((Scheme.ΓSpecIso R).inv.hom r) * chi X x, ?_⟩
    rw [map_mul, SplitTorus.ev_chi, ev_base_apply, AddMonoidAlgebra.single_mul_single, zero_add, _root_.mul_one]

end Expand

section Points

variable {S : Scheme.{0}} {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {Z Z' V : Over S}

abbrev app {Z V : Scheme.{0}} (r : Z ⟶ V) : Γ(V, ⊤)ˣ →* Γ(Z, ⊤)ˣ := Units.map r.appTop.hom.toMonoidHom

theorem app_app {Z Z' V : Scheme.{0}} (r : Z' ⟶ Z) (s : Z ⟶ V) (u : Γ(V, ⊤)ˣ) : app r (app s u) = app (r ≫ s) u := by
  ext
  exact (app_global_comp_apply r s u.val).symm

def pt (x y u : Z ⟶ splitTorus S X) : Z ⟶ splitTorus S (X × X × X) :=
  ofVal ((valHom x).coprod ((valHom y).coprod (valHom u)))

theorem pt_p₁ (x y u : Z ⟶ splitTorus S X) : pt x y u ≫ SplitTorus.torusMap S p₁ = x := by
  refine SplitTorus.hom_ext fun a => ?_
  rw [SplitTorus.val_comp_torusMap, pt, SplitTorus.val_ofVal]
  simp

theorem pt_p₂ (x y u : Z ⟶ splitTorus S X) : pt x y u ≫ SplitTorus.torusMap S p₂ = y := by
  refine SplitTorus.hom_ext fun a => ?_
  rw [SplitTorus.val_comp_torusMap, pt, SplitTorus.val_ofVal]
  simp

theorem pt_p₃ (x y u : Z ⟶ splitTorus S X) : pt x y u ≫ SplitTorus.torusMap S p₃ = u := by
  refine SplitTorus.hom_ext fun a => ?_
  rw [SplitTorus.val_comp_torusMap, pt, SplitTorus.val_ofVal]
  simp

theorem pt_torusMap (a b c : X →+ Y) : pt (SplitTorus.torusMap S a) (SplitTorus.torusMap S b) (SplitTorus.torusMap S c) = SplitTorus.torusMap S (tri a b c) := by
  refine SplitTorus.hom_ext fun p => ?_
  obtain ⟨x, y, z⟩ := p
  rw [pt, SplitTorus.val_ofVal, SplitTorus.val_torusMap]
  simp only [AddMonoidHom.coprod_apply, toMul_add, Units.val_mul, SplitTorus.valHom_apply,
    SplitTorus.val_torusMap, tri]
  rw [← SplitTorus.val_id, ← SplitTorus.val_id, ← SplitTorus.val_id, ← SplitTorus.val_id,
    SplitTorus.val_add, SplitTorus.val_add]

def dif [GrpObj V] (g : Γ(V.left, ⊤)ˣ) (x y u : Z ⟶ V) : Γ(Z.left, ⊤)ˣ :=
  app (x * y * u).left g * app x.left g * app y.left g * app u.left g / app (x * y).left g / app (x * u).left g /
    app (y * u).left g

theorem app_dif [GrpObj V] (g : Γ(V.left, ⊤)ˣ) (r : Z' ⟶ Z) (x y u : Z ⟶ V) :
    app r.left (dif g x y u) = dif g (r ≫ x) (r ≫ y) (r ≫ u) := by
  simp only [dif, map_mul, map_div, app_app, ← Over.comp_left, Hom.mul_def, comp_lift_assoc]

end Points

section Affine

variable {A : Type} [CommRing A] {X Y : Type} [AddCommGroup X] [AddCommGroup Y]

abbrev ex : Γ((splitTorus (Spec (CommRingCat.of A)) X).left, ⊤)ˣ →* (AddMonoidAlgebra A X)ˣ :=
  Units.map (ev (X := X) (𝟙 (Spec (CommRingCat.of A)))).toMonoidHom

theorem ex_bijective : Function.Bijective (ex (A := A) (X := X)) := by
  have hi := ev_injective (R := CommRingCat.of A) (X := X)
  have hs := ev_surjective (R := CommRingCat.of A) (X := X)
  refine ⟨fun u v h => Units.ext (hi (congrArg Units.val h)), fun w => ?_⟩
  obtain ⟨a, ha⟩ := hs w.val
  obtain ⟨b, hb⟩ := hs w.inv
  have hab : a * b = 1 := hi (by rw [map_mul, ha, hb, w.val_inv, map_one])
  exact ⟨⟨a, b, hab, by rw [_root_.mul_comm, hab]⟩, Units.ext ha⟩

theorem ex_app (φ : X →+ Y) (u : Γ((splitTorus (Spec (CommRingCat.of A)) X).left, ⊤)ˣ) :
    ex (app (SplitTorus.torusMap _ φ).left u) = um φ (ex u) := Units.ext (ev_torusMap (𝟙 _) φ u.val)

theorem ex_dif (a b c : X →+ Y) (g : Γ((splitTorus (Spec (CommRingCat.of A)) X).left, ⊤)ˣ) :
    ex (dif g (SplitTorus.torusMap _ a) (SplitTorus.torusMap _ b) (SplitTorus.torusMap _ c)) = del (ex g) a b c := by
  simp only [dif, del, map_mul, map_div, ← SplitTorus.torusMap_add, ex_app]

theorem ex_mem_cong (J : Ideal A) (u : Γ((splitTorus (Spec (CommRingCat.of A)) X).left, ⊤)ˣ) :
    ex u ∈ cong J ↔ app (bcMap (red J) X) u = 1 := by
  have key : ev (𝟙 _) ((bcMap (red J) X).appTop.hom u.val) = rd J (ev (𝟙 _) u.val) := by
    rw [ev_bcMap, Category.id_comp,
      show red J = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ 𝟙 _ from (Category.comp_id _).symm,
      SplitTorus.ev_comp]
    rfl
  rw [mem_cong, Units.ext_iff, Units.val_one]
  change rd J (ev (𝟙 _) u.val) = 1 ↔ (bcMap (red J) X).appTop.hom u.val = 1
  constructor
  · intro h
    apply ev_injective
    rw [key, h, map_one]
  · intro h
    rw [← key, h, map_one]

variable {J : Ideal A}

theorem exists_dif (hJ : IsNilpotent J) (D : Γ((splitTorus (Spec (CommRingCat.of A)) (X × X × X)).left, ⊤)ˣ)
    (s₁ : ∀ (Z : Over (Spec (CommRingCat.of A))) (x y u : Z ⟶ splitTorus _ X),
      app (pt x y u).left D = app (pt y x u).left D)
    (s₂ : ∀ (Z : Over (Spec (CommRingCat.of A))) (x y u : Z ⟶ splitTorus _ X),
      app (pt x y u).left D = app (pt x u y).left D)
    (co : ∀ (Z : Over (Spec (CommRingCat.of A))) (x y u v : Z ⟶ splitTorus _ X),
      app (pt (x * y) u v).left D * app (pt x y v).left D = app (pt x (y * u) v).left D * app (pt y u v).left D)
    (h : app (bcMap (red J) _) D = 1) :
    ∃ g : Γ((splitTorus (Spec (CommRingCat.of A)) X).left, ⊤)ˣ, app (bcMap (red J) X) g = 1 ∧
      ∀ (Z : Over (Spec (CommRingCat.of A))) (x y u : Z ⟶ splitTorus _ X), app (pt x y u).left D = dif g x y u := by
  have hcub : Cub (ex (A := A) (X := X × X × X) D) := by
    refine ⟨fun Y _ a b c => ?_, fun Y _ a b c => ?_, fun Y _ a b c d => ?_⟩
    · have h1 := congrArg ex (s₁ (splitTorus _ Y) (SplitTorus.torusMap _ a) (SplitTorus.torusMap _ b)
        (SplitTorus.torusMap _ c))
      simpa only [pt_torusMap, ex_app] using h1
    · have h1 := congrArg ex (s₂ (splitTorus _ Y) (SplitTorus.torusMap _ a) (SplitTorus.torusMap _ b)
        (SplitTorus.torusMap _ c))
      simpa only [pt_torusMap, ex_app] using h1
    · have h1 := congrArg ex (co (splitTorus _ Y) (SplitTorus.torusMap _ a) (SplitTorus.torusMap _ b)
        (SplitTorus.torusMap _ c) (SplitTorus.torusMap _ d))
      simpa only [← SplitTorus.torusMap_add, pt_torusMap, map_mul, ex_app] using h1
  obtain ⟨g', hg', hD⟩ := hcub.exists_del hJ ((ex_mem_cong J D).2 h)
  obtain ⟨g, rfl⟩ := (ex_bijective (A := A) (X := X)).2 g'
  have hD' : D = dif g (SplitTorus.torusMap _ p₁) (SplitTorus.torusMap _ p₂) (SplitTorus.torusMap _ p₃) := by
    apply (ex_bijective (A := A) (X := X × X × X)).1
    rw [hD, ex_dif]
  refine ⟨g, (ex_mem_cong J g).1 hg', fun Z x y u => ?_⟩
  rw [hD', app_dif, pt_p₁, pt_p₂, pt_p₃]

theorem eq_one_of_dif (hJ : IsNilpotent J) (g : Γ((splitTorus (Spec (CommRingCat.of A)) X).left, ⊤)ˣ)
    (h : app (bcMap (red J) X) g = 1)
    (hg : ∀ (Z : Over (Spec (CommRingCat.of A))) (x y u : Z ⟶ splitTorus _ X), dif g x y u = 1) : g = 1 := by
  have h1 : ex g ∈ cong J := (ex_mem_cong J g).2 h
  have h2 : del (ex g) p₁ p₂ p₃ = 1 := by
    rw [← ex_dif, hg, map_one]
  apply (ex_bijective (A := A) (X := X)).1
  rw [eq_one_of_del hJ h1 h2, map_one]

end Affine

end GlobalTheory.CubeLift
