import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.CechAugRow
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.DcColSurj
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.CechDesc
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''
namespace CrystallineSemistableComparison.Auxfi

section Gen
variable {R : Type} [CommRing R]

theorem exact_one {M : Type w} {N : Type w'} {P : Type w''} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P} (h : ExactUpTo (1 : R) f g) (s : R) :
    ExactUpTo s f g := by
  intro y hy
  obtain ⟨x, hx⟩ := h y hy
  exact ⟨s • x, by rw [map_smul, hx, one_smul]⟩

theorem tr_exact {K : Cx.{w} R} {L : Cx.{w'} R} (φ : Cx.Hom K L (RingHom.id R)) (hφ : ∀ n, Function.Bijective (φ.f n))
    (s : R) (m : ℕ) (h : ExactUpTo s (L.d m) (L.d (m + 1))) : ExactUpTo s (K.d m) (K.d (m + 1)) := by
  intro y hy
  have h1 : L.d (m + 1) (φ.f (m + 1) y) = 0 := by rw [φ.comm, hy, map_zero]
  obtain ⟨x', hx'⟩ := h _ h1
  obtain ⟨x, rfl⟩ := (hφ m).2 x'
  refine ⟨x, (hφ (m + 1)).1 ?_⟩
  rw [← φ.comm, hx', LinearMap.map_smulₛₗ]; rfl

theorem tr_aug {K : Cx.{w} R} {L : Cx.{w'} R} (φ : Cx.Hom K L (RingHom.id R)) (hφ : ∀ n, Function.Bijective (φ.f n))
    {M : Type w''} [AddCommGroup M] [Module R M] (ε : M →ₗ[R] K.X 0) (ε' : M →ₗ[R] L.X 0)
    (he : ∀ x, φ.f 0 (ε x) = ε' x) (s : R) :
    (InjUpTo s ε' → InjUpTo s ε) ∧ (ExactUpTo s ε' (L.d 0) → ExactUpTo s ε (K.d 0)) := by
  refine ⟨fun h x hx => h x (by rw [← he, hx, map_zero]), fun h y hy => ?_⟩
  have h1 : L.d 0 (φ.f 0 y) = 0 := by rw [φ.comm, hy, map_zero]
  obtain ⟨x, hx⟩ := h _ h1
  refine ⟨x, (hφ 0).1 ?_⟩
  rw [he, hx, LinearMap.map_smulₛₗ]; rfl

end Gen

end CrystallineSemistableComparison.Auxfi

namespace CrystallineSemistableComparison.Auxfi
section Aug
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C]

theorem d_aug (F : C ⥤ ModuleCat.{w} R) {M : Type w'} [AddCommGroup M] [Module R M] (e : ∀ T : C, M →ₗ[R] F.obj T)
    (he : ∀ {X Y : C} (ψ : X ⟶ Y) (x : M), (F.map ψ).hom (e X x) = e Y x) (x : M) :
    d F 0 (aug F e x) = 0 := by
  funext s
  change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (F.map (GlobalTheory.CatH.toLast i s)).hom (aug F e x (GlobalTheory.CatH.face i s)) = 0
  rw [Fin.sum_univ_two]
  change (-1 : ℤ) ^ 0 • (F.map (GlobalTheory.CatH.toLast 0 s)).hom (e _ x) + (-1 : ℤ) ^ 1 • (F.map (GlobalTheory.CatH.toLast 1 s)).hom (e _ x) = 0
  rw [he, he]; simp

end Aug
end CrystallineSemistableComparison.Auxfi

namespace CrystallineSemistableComparison.Auxfi
section Pw
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
  (F : C ⥤ ModuleCat.{w} R)

theorem el_hom {A : C} {X Y : (pts j A).Elements} (ψ : X ⟶ Y) : (show A ⟶ j.obj X.1 from X.2) ≫ j.map ψ.1 = Y.2 := ψ.2

theorem ptsAug_d (A : C) (x : F.obj A) : d (elF (pts j A) (j ⋙ F)) 0 (ptsAug j F A x) = 0 := by
  refine d_aug _ _ (fun {X Y} ψ x => ?_) x
  change (F.map (j.map ψ.1)).hom ((F.map (show A ⟶ j.obj X.1 from X.2)).hom x) = (F.map (show A ⟶ j.obj Y.1 from Y.2)).hom x
  have h := el_hom j ψ
  refine Eq.trans ?_ (congrArg (fun m => (F.map m).hom x) h)
  rw [F.map_comp]; rfl

def pmap {A : C} (P : Powers j A) : pts j P.B ⟶ pts j A := Functor.whiskerLeft j (coyoneda.map P.f.op)

end Pw
end CrystallineSemistableComparison.Auxfi

namespace CrystallineSemistableComparison.Auxfi
section S0
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
  (F : C ⥤ ModuleCat.{w} R)

theorem map_iso_inj {X Y : C} (f : X ⟶ Y) [IsIso f] : Function.Injective (F.map f).hom := by
  intro y z h
  have := congrArg (F.map (inv f)).hom h
  simpa only [← ModuleCat.comp_apply, ← F.map_comp, IsIso.hom_inv_id, F.map_id, ModuleCat.id_apply] using this

theorem map_iso_surj {X Y : C} (f : X ⟶ Y) [IsIso f] : Function.Surjective (F.map f).hom := by
  intro y
  refine ⟨(F.map (inv f)).hom y, ?_⟩
  simp only [← ModuleCat.comp_apply, ← F.map_comp, IsIso.inv_hom_id, F.map_id, ModuleCat.id_apply]

theorem ptsAug_eval (A : C) (x : F.obj A) (X : (pts j A).Elements) :
    ptsAug j F A x (ComposableArrows.mk₀ X) = (F.map (show A ⟶ j.obj X.1 from X.2)).hom x := rfl

theorem cechDifferential_zero {A : C} (P : Powers j A) (x : F.obj (P.K 0)) : P.dK j F 0 x = (F.map (P.δ 0 0)).hom x := by
  simp [Powers.dK]

theorem s0a (I : Ideal R) {A : C} (P : Powers j A) (hG : P.Good j F I) (a : R) (ha : a ∈ I) :
    InjUpTo (a ^ 2) (ptsAug j F A) := by
  intro x hx
  obtain ⟨-, hex, t0, g, -, halm⟩ := hG
  have h1 : (F.map g).hom ((F.map P.f).hom x) = 0 := by
    have := congrFun hx (ComposableArrows.mk₀ (⟨t0, P.f ≫ g⟩ : (pts j A).Elements))
    rw [ptsAug_eval, F.map_comp] at this
    exact this
  have h2 := (halm a ha).1 _ h1
  have h3 : P.dK j F 0 ((F.map (P.a 0)).hom (a • x)) = 0 := by
    rw [cechDifferential_zero, ← ModuleCat.comp_apply, ← F.map_comp, P.aδ, ← P.w 1 0, F.map_comp, ModuleCat.comp_apply, map_smul, h2,
      map_zero]
  have h4 := (hex a ha).1 _ h3
  rw [← map_smul] at h4
  have := P.iso0
  apply map_iso_inj F (P.a 0)
  rw [pow_two, mul_smul, h4, map_zero]

end S0
end CrystallineSemistableComparison.Auxfi

namespace CrystallineSemistableComparison.Auxfi
section S0b
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
  (F : C ⥤ ModuleCat.{w} R)

noncomputable def initB {B : C} (t0 : T) (g : B ⟶ j.obj t0) (hg : ∀ (t : T) (y : B ⟶ j.obj t), ∃! φ : t0 ⟶ t, g ≫ j.map φ = y) :
    Limits.IsInitial ((pts j B).elementsMk t0 g) :=
  Limits.IsInitial.ofUniqueHom (fun (Y : (pts j B).Elements) => ⟨(hg Y.1 Y.2).exists.choose, (hg Y.1 Y.2).exists.choose_spec⟩)
    (fun (Y : (pts j B).Elements) m => Subtype.ext ((hg Y.1 Y.2).unique m.2 (hg Y.1 Y.2).exists.choose_spec))

theorem cmk (E : T ⥤ Type v) (s : ComposableArrows E.Elements 0) : s = ComposableArrows.mk₀ (s.obj 0) :=
  ComposableArrows.ext₀ rfl

theorem c_eq {A : C} (c : Cn (elF (pts j A) (j ⋙ F)) 0) (t : T) {z z' : A ⟶ j.obj t} (h : z = z') :
    c (ComposableArrows.mk₀ ((pts j A).elementsMk t z)) = c (ComposableArrows.mk₀ ((pts j A).elementsMk t z')) := by
  subst h; rfl

theorem cechDifferential_one_inclusion {A : C} (P : Powers j A) (b : F.obj P.B) :
    P.dK j F 1 ((F.map (P.ι 1 0)).hom b) = (F.map (P.ι 2 1)).hom b - (F.map (P.ι 2 0)).hom b := by
  have e0 : (F.map (P.δ 1 0)).hom ((F.map (P.ι 1 0)).hom b) = (F.map (P.ι 2 1)).hom b := by
    rw [← ModuleCat.comp_apply, ← F.map_comp, P.ιδ]; rfl
  have e1 : (F.map (P.δ 1 1)).hom ((F.map (P.ι 1 0)).hom b) = (F.map (P.ι 2 0)).hom b := by
    rw [← ModuleCat.comp_apply, ← F.map_comp, P.ιδ]; rfl
  simp [Powers.dK, sub_eq_add_neg, e0, e1]

theorem s0b (I : Ideal R) {A : C} (P : Powers j A) (hG : P.Good j F I)
    (h0a : ∀ s ∈ I, InjUpTo s (ptsAug j F (P.K 2))) (a : R) (ha : a ∈ I) :
    ExactUpTo (a ^ 3) (ptsAug j F A) (d (elF (pts j A) (j ⋙ F)) 0) := by
  intro c hc
  obtain ⟨hsurj, hex, t0, g, hg, halm⟩ := hG
  let Φ := (elMor (pmap j P) (j ⋙ F)).hom
  have hc' : d (elF (pts j P.B) (j ⋙ F)) 0 (Φ.f 0 c) = 0 := by
    rw [Φ.comm, show (cx (elF (pts j A) (j ⋙ F))).d 0 c = 0 from hc, map_zero]
  have hI := initB j t0 g hg
  obtain ⟨m, hm⟩ := (CrystallineSemistableComparison.P.initial (elF (pts j P.B) (j ⋙ F)) _ hI).2.2.1 _ hc'
  obtain ⟨b, hb⟩ := (halm a ha).2 (show F.obj (j.obj t0) from m)
  have key : ∀ (t : T) (y : P.B ⟶ j.obj t), (F.map y).hom b =
      a • c (ComposableArrows.mk₀ ((pts j A).elementsMk t (P.f ≫ y))) := by
    intro t y
    let ψ := hI.to ((pts j P.B).elementsMk t y)
    have hψ : g ≫ j.map ψ.1 = y := ψ.2
    have e1 := congrFun hm (ComposableArrows.mk₀ ((pts j P.B).elementsMk t y))
    rw [one_smul] at e1
    change (F.map (j.map ψ.1)).hom m = c (ComposableArrows.mk₀ ((pts j P.B).elementsMk t y) ⋙ CategoryOfElements.map (pmap j P)) at e1
    have e2 : ComposableArrows.mk₀ ((pts j P.B).elementsMk t y) ⋙ CategoryOfElements.map (pmap j P) =
        ComposableArrows.mk₀ ((pts j A).elementsMk t (P.f ≫ y)) := ComposableArrows.ext₀ rfl
    have e3 : HEq (c (ComposableArrows.mk₀ ((pts j P.B).elementsMk t y) ⋙ CategoryOfElements.map (pmap j P)))
        (c (ComposableArrows.mk₀ ((pts j A).elementsMk t (P.f ≫ y)))) := by rw [e2]
    rw [← e1.trans (eq_of_heq e3)]
    have e4 : (F.map y).hom b = (F.map (j.map ψ.1)).hom ((F.map g).hom b) := by
      rw [← ModuleCat.comp_apply, ← F.map_comp, hψ]
    rw [e4, hb]
    exact map_smul _ _ _
  have hb1 : ptsAug j F (P.K 2) (P.dK j F 1 ((F.map (P.ι 1 0)).hom b)) = 0 := by
    rw [cechDifferential_one_inclusion]
    funext s
    rw [cmk _ s]
    change (F.map (s.obj 0).2).hom ((F.map (P.ι 2 1)).hom b - (F.map (P.ι 2 0)).hom b) = 0
    rw [map_sub, ← ModuleCat.comp_apply, ← F.map_comp, ← ModuleCat.comp_apply, ← F.map_comp, key, key,
      c_eq j F c _ (by rw [← Category.assoc, P.w] : P.f ≫ P.ι 2 1 ≫ (s.obj 0).2 = P.a 2 ≫ (s.obj 0).2),
      c_eq j F c _ (by rw [← Category.assoc, P.w] : P.f ≫ P.ι 2 0 ≫ (s.obj 0).2 = P.a 2 ≫ (s.obj 0).2), sub_self]
  have h2 := h0a a ha _ hb1
  rw [← map_smul] at h2
  obtain ⟨x0, hx0⟩ := (hex a ha).2 0 _ h2
  have := P.iso0
  have := P.iso1
  obtain ⟨x, rfl⟩ := map_iso_surj F (P.a 0) x0
  have hfx : (F.map P.f).hom x = a • a • b := by
    apply map_iso_inj F (P.ι 1 0)
    rw [← ModuleCat.comp_apply, ← F.map_comp, P.w, ← P.aδ 0 0, F.map_comp, ModuleCat.comp_apply, ← cechDifferential_zero, hx0,
      map_smul, map_smul]
  refine ⟨x, ?_⟩
  funext s
  rw [cmk _ s]
  obtain ⟨y, hy⟩ := hsurj (s.obj 0).1 (s.obj 0).2
  change (F.map (s.obj 0).2).hom x = a ^ 3 • c (ComposableArrows.mk₀ ((pts j A).elementsMk (s.obj 0).1 (s.obj 0).2))
  rw [← c_eq j F c _ hy, ← hy, F.map_comp, ModuleCat.comp_apply, hfx, map_smul, map_smul, key, smul_smul, smul_smul,
    pow_three, mul_assoc]

end S0b
end CrystallineSemistableComparison.Auxfi

namespace CrystallineSemistableComparison.Auxfi
section Col
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
  (F : C ⥤ ModuleCat.{w} R) {A : C} (P : Powers j A)

theorem cech_compat {n : ℕ} (X : (cech (pmap j P) n).Elements) (i : Fin (n + 1)) :
    P.f ≫ X.2.1 i = P.f ≫ X.2.1 0 := X.2.2 i 0

noncomputable def zz {n : ℕ} (X : (cech (pmap j P) n).Elements) : P.K (n + 1) ⟶ j.obj X.1 :=
  (P.univ (n + 1) X.1 (P.f ≫ X.2.1 0) X.2.1 (cech_compat j P X)).exists.choose

theorem zz_spec {n : ℕ} (X : (cech (pmap j P) n).Elements) :
    P.a (n + 1) ≫ zz j P X = P.f ≫ X.2.1 0 ∧ ∀ i, P.ι (n + 1) i ≫ zz j P X = X.2.1 i :=
  (P.univ (n + 1) X.1 (P.f ≫ X.2.1 0) X.2.1 (cech_compat j P X)).exists.choose_spec

theorem zz_uniq {n : ℕ} (X : (cech (pmap j P) n).Elements) (z : P.K (n + 1) ⟶ j.obj X.1)
    (h1 : P.a (n + 1) ≫ z = P.f ≫ X.2.1 0) (h2 : ∀ i, P.ι (n + 1) i ≫ z = X.2.1 i) : z = zz j P X :=
  (P.univ (n + 1) X.1 (P.f ≫ X.2.1 0) X.2.1 (cech_compat j P X)).unique ⟨h1, h2⟩ (zz_spec j P X)

theorem cech_hom {n : ℕ} {X Y : (cech (pmap j P) n).Elements} (ψ : X ⟶ Y) (i : Fin (n + 1)) :
    X.2.1 i ≫ j.map ψ.1 = Y.2.1 i := congrFun (congrArg Subtype.val ψ.2) i

theorem zz_nat {n : ℕ} {X Y : (cech (pmap j P) n).Elements} (ψ : X ⟶ Y) :
    zz j P X ≫ j.map ψ.1 = zz j P Y := by
  apply zz_uniq
  · rw [← Category.assoc, (zz_spec j P X).1, Category.assoc, cech_hom j P ψ]
  · intro i; rw [← Category.assoc, (zz_spec j P X).2, cech_hom j P ψ]

end Col
end CrystallineSemistableComparison.Auxfi

namespace CrystallineSemistableComparison.Auxfi
section Col2
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
  (F : C ⥤ ModuleCat.{w} R) {A : C} (P : Powers j A)

noncomputable def eta (n : ℕ) : F.obj (P.K (n + 1)) →ₗ[R] Cn (elF (cech (pmap j P) n) (j ⋙ F)) 0 :=
  aug (elF (cech (pmap j P) n) (j ⋙ F)) fun X => (F.map (zz j P X)).hom

theorem eta_d (n : ℕ) (x : F.obj (P.K (n + 1))) : d (elF (cech (pmap j P) n) (j ⋙ F)) 0 (eta j F P n x) = 0 := by
  refine d_aug _ _ (fun {X Y} ψ x => ?_) x
  change (F.map (j.map ψ.1)).hom ((F.map (zz j P X)).hom x) = (F.map (zz j P Y)).hom x
  rw [← zz_nat j P ψ, F.map_comp]; rfl

noncomputable def cosK : Cos.{w} R where
  X n := F.obj (P.K (n + 1))
  δ n i := (F.map (P.δ (n + 1) i)).hom
  rel n k i x := by
    rw [← ModuleCat.comp_apply, ← F.map_comp, P.rel (n + 1) k i, F.map_comp]; rfl

theorem zz_δ (n : ℕ) (i : Fin (n + 2)) (X : (cech (pmap j P) (n + 1)).Elements) :
    zz j P ((CategoryOfElements.map (cechMap (pmap j P) i.succAbove)).obj X) = P.δ (n + 1) i ≫ zz j P X := by
  symm
  refine zz_uniq j P ((CategoryOfElements.map (cechMap (pmap j P) i.succAbove)).obj X) (P.δ (n + 1) i ≫ zz j P X) ?_ ?_
  · change P.a (n + 1) ≫ P.δ (n + 1) i ≫ zz j P X = P.f ≫ X.2.1 (i.succAbove 0)
    rw [← Category.assoc, P.aδ, (zz_spec j P X).1]
    exact (cech_compat j P X _).symm
  · intro k
    change P.ι (n + 1) k ≫ P.δ (n + 1) i ≫ zz j P X = X.2.1 (i.succAbove k)
    rw [← Category.assoc, P.ιδ, (zz_spec j P X).2]

end Col2
end CrystallineSemistableComparison.Auxfi

namespace CrystallineSemistableComparison.Auxfi
section Col3
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
  (F : C ⥤ ModuleCat.{w} R) {A : C} (P : Powers j A)

noncomputable def augc : DCx.AugCol (cosK j F P).cx (cechCos (pmap j P) (j ⋙ F)).dcx where
  η p := eta j F P p
  hη p x := eta_d j F P p x
  comm p x := by
    funext s
    change (Cos.d ((cechCos (pmap j P) (j ⋙ F)).cos 0) p (eta j F P p x)) s =
      (F.map (zz j P (s.obj (Fin.last 0)))).hom (Cos.d (cosK j F P) p x)
    rw [Cos.d_apply, Cos.d_apply, Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, map_zsmul]
    congr 1
    change (F.map (zz j P ((CategoryOfElements.map (cechMap (pmap j P) i.succAbove)).obj (s.obj (Fin.last 0))))).hom x =
      (F.map (zz j P (s.obj (Fin.last 0)))).hom ((F.map (P.δ (p + 1) i)).hom x)
    rw [zz_δ, F.map_comp]; rfl

end Col3
end CrystallineSemistableComparison.Auxfi

namespace CrystallineSemistableComparison.Auxfi
section Col4
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
  (F : C ⥤ ModuleCat.{w} R) {A : C} (P : Powers j A)

def uK (n : ℕ) : pts j (P.K (n + 1)) ⟶ cech (pmap j P) n where
  app t := TypeCat.ofHom fun z => ⟨fun i => P.ι (n + 1) i ≫ z, fun i k => by
    change P.f ≫ P.ι (n + 1) i ≫ z = P.f ≫ P.ι (n + 1) k ≫ z
    rw [← Category.assoc, ← Category.assoc, P.w, P.w]⟩
  naturality X Y φ := by
    ext z
    exact Subtype.ext (funext fun i => (Category.assoc (P.ι (n + 1) i) z (j.map φ)).symm)

theorem uK_bij (n : ℕ) (t : T) : Function.Bijective ((uK j P n).app t) := by
  constructor
  · intro z z' h
    have h' : ∀ i, P.ι (n + 1) i ≫ z = P.ι (n + 1) i ≫ z' := fun i => congrFun (congrArg Subtype.val h) i
    have hx : ∀ i, P.f ≫ P.ι (n + 1) i ≫ z' = P.a (n + 1) ≫ z' := fun i => by rw [← Category.assoc, P.w]
    exact (P.univ (n + 1) t (P.a (n + 1) ≫ z') (fun i => P.ι (n + 1) i ≫ z') hx).unique
      ⟨by rw [← P.w (n + 1) 0, Category.assoc, h' 0, ← Category.assoc], h'⟩ ⟨rfl, fun _ => rfl⟩
  · intro y
    refine ⟨zz j P ((cech (pmap j P) n).elementsMk t y), Subtype.ext (funext fun i => ?_)⟩
    exact (zz_spec j P ((cech (pmap j P) n).elementsMk t y)).2 i

theorem uK_eta (n : ℕ) (x : F.obj (P.K (n + 1))) :
    (elMor (uK j P n) (j ⋙ F)).hom.f 0 (eta j F P n x) = ptsAug j F (P.K (n + 1)) x := by
  funext s
  change (F.map (zz j P ((CategoryOfElements.map (uK j P n)).obj (s.obj (Fin.last 0))))).hom x =
    (F.map (show P.K (n + 1) ⟶ j.obj (s.obj (Fin.last 0)).1 from (s.obj (Fin.last 0)).2)).hom x
  congr 3
  symm
  refine zz_uniq j P ((CategoryOfElements.map (uK j P n)).obj (s.obj (Fin.last 0))) _ ?_ (fun i => rfl)
  change P.a (n + 1) ≫ _ = P.f ≫ P.ι (n + 1) 0 ≫ _
  rw [← Category.assoc, P.w]

end Col4
end CrystallineSemistableComparison.Auxfi

namespace CrystallineSemistableComparison.Auxfi
section Step
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
  (F : C ⥤ ModuleCat.{w} R) {A : C} (P : Powers j A)

noncomputable def init0 (t0 : T) (g : P.B ⟶ j.obj t0) (hg : ∀ (t : T) (y : P.B ⟶ j.obj t), ∃! φ : t0 ⟶ t, g ≫ j.map φ = y) :
    Limits.IsInitial ((cech (pmap j P) 0).elementsMk t0 ⟨fun _ => g, fun _ _ => rfl⟩) :=
  Limits.IsInitial.ofUniqueHom
    (fun (Y : (cech (pmap j P) 0).Elements) => ⟨(hg Y.1 (Y.2.1 0)).exists.choose, Subtype.ext (funext fun i => by
      rw [Fin.fin_one_eq_zero i]; exact (hg Y.1 (Y.2.1 0)).exists.choose_spec)⟩)
    (fun (Y : (cech (pmap j P) 0).Elements) m =>
      Subtype.ext ((hg Y.1 (Y.2.1 0)).unique (cech_hom j P m 0) (hg Y.1 (Y.2.1 0)).exists.choose_spec))

theorem cech_column_zero_exact (t0 : T) (g : P.B ⟶ j.obj t0) (hg : ∀ (t : T) (y : P.B ⟶ j.obj t), ∃! φ : t0 ⟶ t, g ≫ j.map φ = y)
    (q : ℕ) (s : R) :
    ExactUpTo s ((cx (elF (cech (pmap j P) 0) (j ⋙ F))).d q) ((cx (elF (cech (pmap j P) 0) (j ⋙ F))).d (q + 1)) :=
  exact_one ((CrystallineSemistableComparison.P.initial (elF (cech (pmap j P) 0) (j ⋙ F)) _ (init0 j P t0 g hg)).2.2.2 q) s

end Step
end CrystallineSemistableComparison.Auxfi

namespace CrystallineSemistableComparison.Auxfi
section Step2
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
  (F : C ⥤ ModuleCat.{w} R)

theorem sstep (I : Ideal R) {A : C} (P : Powers j A) (hG : P.Good j F I) (n : ℕ)
    (IH : ∀ m < n, ∀ A' : C, ∀ s ∈ I,
      ExactUpTo s ((cx (elF (pts j A') (j ⋙ F))).d m) ((cx (elF (pts j A') (j ⋙ F))).d (m + 1)))
    (h0a : ∀ A' : C, ∀ s ∈ I, InjUpTo s (ptsAug j F A'))
    (h0b : ∀ A' : C, ∀ s ∈ I, ExactUpTo s (ptsAug j F A') ((cx (elF (pts j A') (j ⋙ F))).d 0))
    (a : R) (ha : a ∈ I) :
    ExactUpTo (a ^ (n + 4)) ((cx (elF (pts j A) (j ⋙ F))).d n) ((cx (elF (pts j A) (j ⋙ F))).d (n + 1)) := by
  obtain ⟨hsurj, hex, t0, g, hg, halm⟩ := hG
  have hbφ : ∀ m q, Function.Bijective ((elMor (uK j P m) (j ⋙ F)).hom.f q) :=
    fun m => CrystallineSemistableComparison.P.el_iso (uK j P m) (j ⋙ F) (uK_bij j P m)
  have hcol : ∀ p q, p + q + 1 = n + 1 → ExactUpTo a ((cechCos (pmap j P) (j ⋙ F)).dcx.dv p q)
      ((cechCos (pmap j P) (j ⋙ F)).dcx.dv p (q + 1)) := by
    intro p q hpq
    rcases p with _ | p
    · exact cech_column_zero_exact j F P t0 g hg q a
    · exact tr_exact _ (hbφ (p + 1)) a q (IH q (by omega) (P.K (p + 2)) a ha)
  have hη : ExactUpTo a ((augc j F P).η (n + 1)) ((cechCos (pmap j P) (j ⋙ F)).dcx.dv (n + 1) 0) :=
    (tr_aug _ (hbφ (n + 1)) (eta j F P (n + 1)) (ptsAug j F (P.K (n + 2))) (uK_eta j F P (n + 1)) a).2 (h0b _ a ha)
  have hinj : InjUpTo a ((augc j F P).η (n + 2)) :=
    (tr_aug _ (hbφ (n + 2)) (eta j F P (n + 2)) (ptsAug j F (P.K (n + 3))) (uK_eta j F P (n + 2)) a).1 (h0a _ a ha)
  have hs := CrystallineSemistableComparison.P.dc_col_surj (augc j F P) a (n + 1) hcol hη hinj
  have hps : ∀ t, Function.Surjective ((pmap j P).app t) := fun t x => hsurj t x
  have hbij := CrystallineSemistableComparison.P.cech_desc (pmap j P) (j ⋙ F) hps (n + 1)
  intro y hy
  obtain ⟨xa, hxa⟩ := hs ((cechAugRow (pmap j P) (j ⋙ F)).edge.mapH (n + 1) ((cx (elF (pts j A) (j ⋙ F))).cls y hy))
  obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cosK j F P).cx (n + 1)).1 xa
  obtain ⟨b', hb'⟩ := (hex a ha).2 (n + 1) b hb
  have hab : a • (cosK j F P).cx.cls b hb = 0 := by
    rw [← (CrystallineSemistableComparison.P.cls_surj _ (n + 1)).2.2.2.2 a b hb (by rw [map_smul, hb, smul_zero])]
    rw [(CrystallineSemistableComparison.P.cls_surj _ (n + 1)).2.1]
    exact ⟨b', hb'⟩
  have hy' : (cx (elF (pts j A) (j ⋙ F))).d (n + 1) (a ^ (n + 4) • y) = 0 := by rw [map_smul, hy, smul_zero]
  have h0 : (cechAugRow (pmap j P) (j ⋙ F)).edge.mapH (n + 1) ((cx (elF (pts j A) (j ⋙ F))).cls _ hy') = 0 := by
    rw [(CrystallineSemistableComparison.P.cls_surj _ (n + 1)).2.2.2.2 _ y hy, map_smul, pow_succ', mul_smul, ← hxa, ← map_smul, hab, map_zero]
  have h1 := hbij.1 (h0.trans (map_zero _).symm)
  rw [(CrystallineSemistableComparison.P.cls_surj _ (n + 1)).2.1] at h1
  obtain ⟨x, hx⟩ := h1
  exact ⟨x, hx⟩

end Step2
end CrystallineSemistableComparison.Auxfi

theorem CrystallineSemistableComparison.P.induct : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C) (F : C ⥤ ModuleCat.{w} R) (I : Ideal R), (∀ N : ℕ, I ≤ Ideal.span ((fun a => a ^ N) '' (I : Set R))) → (∀ A : C, ∃ P : Powers j A, P.Good j F I) → ∀ (A : C), ∀ s ∈ I, (cx (elF (pts j A) (j ⋙ F))).ResUpTo s (ptsAug j F A) := by
  intro R _ C _ T _ j F I hI hgood
  choose P hP using hgood
  have h0a : ∀ A : C, ∀ s ∈ I, InjUpTo s (ptsAug j F A) := fun A =>
    (CrystallineSemistableComparison.P.pow_upTo I hI 2 (ptsAug j F A) ((cx (elF (pts j A) (j ⋙ F))).d 0)).1
      (fun a ha => CrystallineSemistableComparison.Auxfi.s0a j F I (P A) (hP A) a ha)
  have h0b : ∀ A : C, ∀ s ∈ I, ExactUpTo s (ptsAug j F A) ((cx (elF (pts j A) (j ⋙ F))).d 0) := fun A =>
    (CrystallineSemistableComparison.P.pow_upTo I hI 3 (ptsAug j F A) ((cx (elF (pts j A) (j ⋙ F))).d 0)).2.2.2
      (fun a ha => CrystallineSemistableComparison.Auxfi.s0b j F I (P A) (hP A) (h0a _) a ha)
  have hn : ∀ n, ∀ A : C, ∀ s ∈ I,
      ExactUpTo s ((cx (elF (pts j A) (j ⋙ F))).d n) ((cx (elF (pts j A) (j ⋙ F))).d (n + 1)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      exact fun A => (CrystallineSemistableComparison.P.pow_upTo I hI (n + 4) ((cx (elF (pts j A) (j ⋙ F))).d n)
        ((cx (elF (pts j A) (j ⋙ F))).d (n + 1))).2.2.2
        (fun a ha => CrystallineSemistableComparison.Auxfi.sstep j F I (P A) (hP A) n ih h0a h0b a ha)
  intro A s hs
  exact ⟨fun x => CrystallineSemistableComparison.Auxfi.ptsAug_d j F A x, h0a A s hs, h0b A s hs, fun n => hn n A s hs⟩
