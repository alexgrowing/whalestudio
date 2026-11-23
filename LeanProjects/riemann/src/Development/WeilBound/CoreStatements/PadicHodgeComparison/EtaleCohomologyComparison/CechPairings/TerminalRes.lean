import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.CechAugRow
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.DcColSurj
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.DoubleComplexMapMemTotal
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

noncomputable section
namespace CrystallineSemistableComparison.RelativeAugmentedComplex
variable {R : Type} [CommRing R]

theorem terminal_res {D : Type u} [Category.{v} D] (Z : D) (hZ : Limits.IsTerminal Z) (M : ModuleCat.{w} R) :
    (cx ((Functor.const D).obj M)).ResUpTo 1 (aug ((Functor.const D).obj M) fun _ => (LinearMap.id : M →ₗ[R] M)) := by
  let P := (Functor.const (Discrete PUnit.{1})).obj M
  let F := (Functor.const D).obj M
  let a : Mor P F (RingHom.id R) := ⟨(Functor.const D).obj ⟨PUnit.unit⟩, fun _ => LinearMap.id, fun _ _ => rfl⟩
  let b : Mor F P (RingHom.id R) := ⟨(Functor.const _).obj Z, fun _ => LinearMap.id, fun _ _ => rfl⟩
  have hi : Limits.IsInitial (⟨PUnit.unit⟩ : Discrete PUnit.{1}) :=
    Limits.IsInitial.ofUniqueHom (fun _ => 𝟙 _) fun _ _ => Subsingleton.elim _ _
  have h0 := CrystallineSemistableComparison.P.initial P _ hi
  have h1 : ∀ n x, a.pull n (b.pull n x) = x := fun n x => by
    rw [← (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) b a n x).1, ← CrystallineSemistableComparison.P.prism (Mor.id F) (b.comp a)
      ⟨fun T => hZ.from T, fun _ _ _ => hZ.hom_ext _ _⟩ (fun _ _ => rfl) n x]
    exact (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) b a n x).2
  have h2 : ∀ n x, b.pull n (a.pull n x) = x := fun n x => by
    rw [← (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) a b n x).1, ← CrystallineSemistableComparison.P.prism (Mor.id P) (a.comp b)
      ⟨fun T => 𝟙 _, fun _ _ _ => Subsingleton.elim _ _⟩ (fun _ _ => rfl) n x]
    exact (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) a b n x).2
  have h3 : ∀ n, UpTo (1 : R) (a.hom.mapH n) := fun n =>
    (CrystallineSemistableComparison.P.upTo_alg _ (LinearMap.id (R := R)) 1 1).2.2.2.2.2 ⟨Function.LeftInverse.injective (h2 n), Function.RightInverse.surjective (h1 n)⟩
  have h4 := (CrystallineSemistableComparison.P.res_transfer a.hom _ 1 1 h3).1 h0
  rw [one_mul] at h4
  exact h4

variable {C : Type u} [Category.{v} C] {I : Type t} [Category.{t'} I] (π : C ⥤ I) (F : C ⥤ ModuleCat.{w} R)

def mkS {j : I} {q : ℕ} (c : ComposableArrows C q) (a : ∀ k, j ⟶ π.obj (c.obj k))
    (h : ∀ {k k' : Fin (q + 1)} (φ : k ⟶ k'), a k ≫ π.map (c.map φ) = a k') : ComposableArrows (StructuredArrow j π) q where
  obj k := StructuredArrow.mk (a k)
  map φ := StructuredArrow.homMk (c.map φ) (h φ)

theorem mkS_congr {j : I} {q : ℕ} (f : Cn (relF π F j) q) (c : ComposableArrows C q) {a a' : ∀ k, j ⟶ π.obj (c.obj k)}
    (h' : ∀ {k k' : Fin (q + 1)} (φ : k ⟶ k'), a' k ≫ π.map (c.map φ) = a' k')
    (e : a = a') : @Eq (F.obj (c.obj (Fin.last q))) (f (mkS π c a (e ▸ h'))) (f (mkS π c a' h')) := by
  subst e; rfl

def relCn (q : ℕ) : I ⥤ ModuleCat.{max u v w t'} R where
  obj i := ModuleCat.of R (Cn (relF π F i) q)
  map a := ModuleCat.ofHom ((relRes π F a).pullC q)
  map_id i := by
    ext f s
    exact mkS_congr π F f (s ⋙ StructuredArrow.proj _ _) (a := fun k => 𝟙 i ≫ (s.obj k).hom) (a' := fun k => (s.obj k).hom)
      (fun φ => StructuredArrow.w (s.map φ)) (funext fun k => Category.id_comp _)
  map_comp {i i' i''} a b := by
    ext f s
    exact mkS_congr π F f (s ⋙ StructuredArrow.proj _ _) (a := fun k => (a ≫ b) ≫ (s.obj k).hom)
      (a' := fun k => a ≫ b ≫ (s.obj k).hom) (fun φ => by
        rw [Category.assoc, Category.assoc]; exact congrArg (fun z => a ≫ b ≫ z) (StructuredArrow.w (s.map φ))) (funext fun k => Category.assoc _ _ _)

def relCx : CxF.{max u v w t'} I R where
  F := relCn π F
  δ q := { app := fun i => ModuleCat.ofHom (d (relF π F i) q)
           naturality := fun i i' a => by
             ext f
             exact (relRes π F a).d_pullC q f }
  dd q i := d_d (relF π F i) q

def relAugRow : DCx.AugRow (cx F) (relCx π F).dcx where
  ε q := aug (relCn π F q) fun i => (relAug π F i).pullC q
  hε q f := by
    funext s
    change ∑ k : Fin 2, (-1 : ℤ) ^ (k : ℕ) • (relAug π F (s.obj (Fin.last 1))).pullC q f = 0
    simp [Fin.sum_univ_two]
  comm q f := funext fun s => (relAug π F _).d_pullC q f

def mkO {Z : I} {p : ℕ} (i : ComposableArrows I p) (a : ∀ k, i.obj k ⟶ Z)
    (h : ∀ {k k' : Fin (p + 1)} (φ : k ⟶ k'), i.map φ ≫ a k' = a k) : ComposableArrows (Over Z) p where
  obj k := Over.mk (a k)
  map φ := Over.homMk (i.map φ) (h φ)

def st {j : I} {q : ℕ} (c : ComposableArrows C q) (a : j ⟶ π.obj (c.obj 0)) : ComposableArrows (StructuredArrow j π) q :=
  mkS π c (fun k => a ≫ π.map (c.map (homOfLE (Fin.zero_le k)))) fun φ => by
    rw [Category.assoc, ← π.map_comp, ← c.map_comp]; rfl

theorem st_w {j : I} {q : ℕ} (c : ComposableArrows C q) (a : j ⟶ π.obj (c.obj 0)) {k k' : Fin (q + 1)} (φ : k ⟶ k') :
    (a ≫ π.map (c.map (homOfLE (Fin.zero_le k)))) ≫ π.map (c.map φ) = a ≫ π.map (c.map (homOfLE (Fin.zero_le k'))) := by
  rw [Category.assoc, ← π.map_comp, ← c.map_comp]; rfl

def ov {Z : I} {p : ℕ} (i : ComposableArrows I p) (a : i.obj (Fin.last p) ⟶ Z) : ComposableArrows (Over Z) p :=
  mkO i (fun k => i.map (homOfLE (Fin.le_last k)) ≫ a) fun φ => by
    rw [← Category.assoc, ← i.map_comp]; rfl

theorem ov_eq {Z : I} {p : ℕ} (s : ComposableArrows (Over Z) p) : ov (s ⋙ Over.forget Z) (s.obj (Fin.last p)).hom = s := by
  have e : ∀ (a : ∀ k, (s ⋙ Over.forget Z).obj k ⟶ Z) h (e : a = fun k => (s.obj k).hom), mkO (s ⋙ Over.forget Z) a h = s := by
    intro a h e; subst e; rfl
  exact e _ _ (funext fun k => Over.w (s.map _))

def cmp {p q : ℕ} (f : Cn (relCn π F q) p) (c : ComposableArrows C q) :
    Cn ((Functor.const (Over (π.obj (c.obj 0)))).obj (F.obj (c.obj (Fin.last q)))) p :=
  fun s => f (s ⋙ Over.forget _) (st π c (s.obj (Fin.last p)).hom)

theorem cmp_inj {p q : ℕ} (f g : Cn (relCn π F q) p) (h : ∀ c, cmp π F f c = cmp π F g c) : f = g := by
  funext i x
  have key : ∀ f : Cn (relCn π F q) p, @Eq (F.obj (x.obj (Fin.last q)).right) (f i x)
      (cmp π F f (x ⋙ StructuredArrow.proj _ _) (ov i (x.obj 0).hom)) := fun f => by
    refine mkS_congr π F (f i) (x ⋙ StructuredArrow.proj _ _) (a := fun k => (x.obj k).hom)
      (a' := fun k => (i.map (𝟙 _) ≫ (x.obj 0).hom) ≫ π.map (x.map (homOfLE (Fin.zero_le k))).right)
      (st_w π (x ⋙ StructuredArrow.proj _ _) _) (funext fun k => ?_)
    rw [i.map_id, Category.id_comp]
    exact (StructuredArrow.w _).symm
  exact (key f).trans ((congrFun (h _) _).trans (key g).symm)

theorem cmp_surj {p q : ℕ} (g : ∀ c : ComposableArrows C q,
    Cn ((Functor.const (Over (π.obj (c.obj 0)))).obj (F.obj (c.obj (Fin.last q)))) p) :
    ∃ f : Cn (relCn π F q) p, ∀ c, cmp π F f c = g c := by
  refine ⟨fun i x => g (x ⋙ StructuredArrow.proj _ _) (ov i (x.obj 0).hom), fun c => funext fun s => ?_⟩
  change g c (ov (s ⋙ Over.forget _) ((s.obj (Fin.last p)).hom ≫ π.map (c.map (𝟙 0)))) = g c s
  rw [c.map_id, π.map_id, Category.comp_id, ov_eq]

theorem cmp_d {p q : ℕ} (f : Cn (relCn π F q) p) (c : ComposableArrows C q) :
    cmp π F (d _ p f) c = d _ p (cmp π F f c) := by
  funext s
  change (∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) • (relRes π F (GlobalTheory.CatH.toLast k (s ⋙ Over.forget _))).pullC q
    (f (GlobalTheory.CatH.face k (s ⋙ Over.forget _)))) (st π c (s.obj (Fin.last (p + 1))).hom) =
    ∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) • cmp π F f c (GlobalTheory.CatH.face k s)
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => congrArg (fun z : F.obj (c.obj (Fin.last q)) => (-1 : ℤ) ^ (k : ℕ) • z) (a₁ := (relRes π F (GlobalTheory.CatH.toLast k (s ⋙ Over.forget _))).pullC q
    (f (GlobalTheory.CatH.face k (s ⋙ Over.forget _))) (st π c (s.obj (Fin.last (p + 1))).hom)) ?_
  refine mkS_congr π F (f (GlobalTheory.CatH.face k (s ⋙ Over.forget _))) c
    (a := fun l => (GlobalTheory.CatH.toLast k s).left ≫ (s.obj (Fin.last (p + 1))).hom ≫ π.map (c.map (homOfLE (Fin.zero_le l))))
    (a' := fun l => ((GlobalTheory.CatH.face k s).obj (Fin.last p)).hom ≫ π.map (c.map (homOfLE (Fin.zero_le l)))) (st_w π c _)
    (funext fun l => ?_)
  rw [← Category.assoc, Over.w]

theorem row_res (q : ℕ) : ((relCx π F).dcx.row q).ResUpTo 1 ((relAugRow π F).ε q) := by
  have T := fun c : ComposableArrows C q => terminal_res (R := R) _ (Over.mkIdTerminal (X := π.obj (c.obj 0))) (F.obj (c.obj (Fin.last q)))
  have he : ∀ (f : Cn F q) c, cmp π F ((relAugRow π F).ε q f) c = aug _ (fun _ => LinearMap.id) (f c) := fun f c => rfl
  refine ⟨(relAugRow π F).hε q, fun f hf => funext fun c => (T c).2.1 _ (by rw [← he, hf]; rfl), fun f hf => ?_, fun n f hf => ?_⟩
  · choose g hg using fun c => (T c).2.2.1 (cmp π F f c) (by
      change d _ 0 _ = 0
      rw [← cmp_d, show d (relCn π F q) 0 f = 0 from hf]; rfl)
    exact ⟨g, cmp_inj π F _ _ fun c => by rw [he, hg, one_smul, one_smul]⟩
  · choose g hg using fun c => (T c).2.2.2 n (cmp π F f c) (by
      change d _ (n + 1) _ = 0
      rw [← cmp_d, show d (relCn π F q) (n + 1) f = 0 from hf]; rfl)
    obtain ⟨g', hg'⟩ := cmp_surj π F g
    refine ⟨g', cmp_inj π F _ _ fun c => ?_⟩
    change cmp π F (d _ n g') c = _
    rw [cmp_d, hg', one_smul]
    exact (hg c).trans (one_smul _ _)

variable {C' : Type u'} [Category.{v'} C'] {F} {F' : C' ⥤ ModuleCat.{w'} R} (m : Mor F F' (RingHom.id R))

def relHom : DCx.Hom (relCx π F).dcx (relCx (m.G ⋙ π) F').dcx (RingHom.id R) where
  f p q :=
    { toFun := fun g i => (relMor π m _).pullC q (g i)
      map_add' := fun g g' => funext fun i => map_add ((relMor π m _).pullC q) _ _
      map_smul' := fun r g => funext fun i => map_smul ((relMor π m _).pullC q) _ _ }
  ch p q g := by
    funext i
    change ∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) • (relRes _ F' (GlobalTheory.CatH.toLast k i)).pullC q ((relMor π m _).pullC q (g (GlobalTheory.CatH.face k i))) =
      (relMor π m _).pullC q (∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) • (relRes π F (GlobalTheory.CatH.toLast k i)).pullC q (g (GlobalTheory.CatH.face k i)))
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_zsmul]; rfl
  cv p q g := funext fun i => (relMor π m _).d_pullC q (g i)

theorem col_upTo (s : R) (p q : ℕ) (h : ∀ i, UpTo s ((relMor π m i).pull q)) : UpTo s (((relHom π m).col p).mapH q) := by
  constructor
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ q).1 x
    have ha' : ∀ i, d (relF π F _) q (a i) = 0 := fun i => congrFun ha i
    have hb := ((CrystallineSemistableComparison.P.cls_surj ((relCx (m.G ⋙ π) F').dcx.col p) q).2.1 (((relHom π m).col p).f q a)
      (by rw [Cx.Hom.comm, ha, map_zero])).1 hx
    have key : ∀ i, s • a i ∈ (cx (relF π F (i.obj (Fin.last p)))).B q := fun i => by
      refine ((CrystallineSemistableComparison.P.cls_surj (cx (relF π F _)) q).2.1 (s • a i) (by rw [map_smul]; exact (congrArg _ (ha' i)).trans (smul_zero _))).1 ?_
      refine (h _).1 ((cx (relF π F _)).cls (a i) (ha' i)) ?_
      refine ((CrystallineSemistableComparison.P.cls_surj (cx (relF (m.G ⋙ π) F' _)) q).2.1 ((relMor π m _).pullC q (a i))
        (by change d _ q _ = 0; rw [Mor.d_pullC, ha', map_zero])).2 ?_
      cases q with
      | zero => exact congrFun (show ((relHom π m).col p).f 0 a = 0 from hb) i
      | succ q => obtain ⟨y, hy⟩ := hb; exact ⟨y i, congrFun hy i⟩
    refine ((CrystallineSemistableComparison.P.cls_surj ((relCx π F).dcx.col p) q).2.1 (s • a) (by rw [map_smul, ha, smul_zero])).2 ?_
    cases q with
    | zero => exact funext fun i => key i
    | succ q => choose y hy using key; exact ⟨y, funext hy⟩
  · intro x
    obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ q).1 x
    have hb' : ∀ i, d (relF (m.G ⋙ π) F' _) q (b i) = 0 := fun i => congrFun hb i
    have key : ∀ i : ComposableArrows I p, ∃ a : Cn (relF π F (i.obj (Fin.last p))) q, d _ q a = 0 ∧
        (relMor π m _).pullC q a - (show Cn (relF (m.G ⋙ π) F' (i.obj (Fin.last p))) q from s • b i) ∈ (cx (relF (m.G ⋙ π) F' (i.obj (Fin.last p)))).B q := fun i => by
      obtain ⟨y, hy⟩ := (h _).2 ((cx (relF (m.G ⋙ π) F' _)).cls (b i) (hb' i))
      obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ q).1 y
      exact ⟨a, ha, ((CrystallineSemistableComparison.P.cls_surj (cx (relF (m.G ⋙ π) F' _)) q).2.2.1 _ (s • b i)
        (by change d _ q ((relMor π m _).pullC q a) = 0; rw [Mor.d_pullC, show d _ q a = 0 from ha, map_zero])
        (by rw [map_smul]; exact (congrArg _ (hb' i)).trans (smul_zero _))).1 hy⟩
    choose a ha hab using key
    refine ⟨((relCx π F).dcx.col p).cls a (funext ha), ?_⟩
    refine ((CrystallineSemistableComparison.P.cls_surj ((relCx (m.G ⋙ π) F').dcx.col p) q).2.2.1 (((relHom π m).col p).f q a) (s • b)
      (by rw [Cx.Hom.comm]; exact (congrArg _ (funext ha)).trans (map_zero _)) (by rw [map_smul, hb, smul_zero])).2 ?_
    cases q with
    | zero => exact funext fun i => hab i
    | succ q => choose y hy using hab; exact ⟨y, funext hy⟩

end CrystallineSemistableComparison.RelativeAugmentedComplex

open CrystallineSemistableComparison.RelativeAugmentedComplex in
theorem CrystallineSemistableComparison.P.rel : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {I : Type t} [Category.{t'} I] {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R} (π : C ⥤ I) (m : Mor F F' (RingHom.id R)) (s : R) (n : ℕ), (∀ i, ∀ q ≤ n + 1, UpTo s ((relMor π m i).pull q)) → UpTo (s ^ (2 * n + 3)) (m.pull n) := by
  intro R _ C _ C' _ I _ F F' π m s n h
  have h1 := CrystallineSemistableComparison.P.dc_row (relAugRow π F) 1 (row_res π F) n
  have h2 := CrystallineSemistableComparison.P.dc_row (relAugRow (m.G ⋙ π) F') 1 (row_res _ F') n
  have h3 := CrystallineSemistableComparison.P.dc_map_col (relHom π m) s n fun p q hpq => col_upTo π m s p q fun i => h i q (by omega)
  rw [one_pow] at h1 h2
  have h4 := (CrystallineSemistableComparison.P.upTo_alg _ _ _ _).1 h1 h3
  have e : (relHom π m).tot.mapH n ∘ₗ (relAugRow π F).edge.mapH n = (relAugRow (m.G ⋙ π) F').edge.mapH n ∘ₗ m.pull n := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ n).1 x
    refine congrArg Submodule.Quotient.mk (Subtype.ext (Subtype.ext (funext fun p => funext fun q => ?_)))
    change (relHom π m).f p q ((relCx π F).dcx.sgl 0 n ((relAugRow π F).ε n a) p q) =
      (relCx (m.G ⋙ π) F').dcx.sgl 0 n ((relAugRow (m.G ⋙ π) F').ε n (m.pullC n a)) p q
    by_cases hpq : p = 0 ∧ q = n
    · obtain ⟨rfl, rfl⟩ := hpq
      rw [DCx.sgl_self, DCx.sgl_self]; rfl
    · rw [DCx.sgl_ne _ _ (by omega), DCx.sgl_ne _ _ (by omega), map_zero]
  rw [e] at h4
  have h5 := (CrystallineSemistableComparison.P.upTo_alg _ _ _ _).2.2.1 h2 h4
  rwa [one_mul, one_mul] at h5
