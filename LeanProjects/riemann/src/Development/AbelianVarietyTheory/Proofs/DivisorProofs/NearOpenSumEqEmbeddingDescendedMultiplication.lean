import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairUOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.DescKP

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}

theorem toS_fst' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    Desc.toS N p hp ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _

theorem toS_snd' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    Desc.toS N p hp ≫ pullback.snd _ _ = pullback.snd _ _ ≫ p := pullback.lift_snd _ _ _

theorem embL_fst' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    (Desc.emb N p hp).left ≫ pullback.fst G.hom p = Desc.toS N p hp ≫ N.u := pullback.lift_fst _ _ _

theorem embL_snd' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    (Desc.emb N p hp).left ≫ pullback.snd G.hom p = pullback.snd _ _ := pullback.lift_snd _ _ _

theorem pairU_fst' (N : Near π G) :
    pairU N ≫ (fst N.U N.U).left = (fst (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst _ _ := by
  show (lift (fstU N) (sndU N) ≫ fst _ _).left = _
  rw [lift_fst]; rfl

theorem pairU_snd' (N : Near π G) :
    pairU N ≫ (snd N.U N.U).left = (snd (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst _ _ := by
  show (lift (fstU N) (sndU N) ≫ snd _ _).left = _
  rw [lift_snd]; rfl

theorem fst_hom' (N : Near π G) :
    (fst (Desc.UT N) (Desc.UT N)).left ≫ pullback.snd N.U.hom (pullback.fst π π ≫ π) = (Desc.UT N ⊗ Desc.UT N).hom :=
  Over.w (fst (Desc.UT N) (Desc.UT N))

theorem snd_hom' (N : Near π G) :
    (snd (Desc.UT N) (Desc.UT N)).left ≫ pullback.snd N.U.hom (pullback.fst π π ≫ π) = (Desc.UT N ⊗ Desc.UT N).hom :=
  Over.w (snd (Desc.UT N) (Desc.UT N))

theorem mT_fst' (N : Near π G) (V : (N.U ⊗ N.U).left.Opens) (m : V.toScheme ⟶ N.U.left)
    (hm : m ≫ N.U.hom = V.ι ≫ (N.U ⊗ N.U).hom) : mT N V m hm ≫ pullback.fst _ _ = (pairU N ∣_ V) ≫ m :=
  pullback.lift_fst _ _ _

theorem mT_snd' (N : Near π G) (V : (N.U ⊗ N.U).left.Opens) (m : V.toScheme ⟶ N.U.left)
    (hm : m ≫ N.U.hom = V.ι ≫ (N.U ⊗ N.U).hom) :
    mT N V m hm ≫ pullback.snd _ _ = (VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom :=
  pullback.lift_snd _ _ _

end GlobalTheory.Mum.DescKP

namespace GlobalTheory.Mum.DescKP

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}

theorem fst_toS_fst' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    ((fst (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp) ≫ pullback.fst _ _ =
      (fst (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst _ _ :=
  (Category.assoc _ _ _).trans (congrArg ((fst (Desc.UT N) (Desc.UT N)).left ≫ ·) (toS_fst' N p hp))

theorem snd_toS_fst' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    ((snd (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp) ≫ pullback.fst _ _ =
      (snd (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst _ _ :=
  (Category.assoc _ _ _).trans (congrArg ((snd (Desc.UT N) (Desc.UT N)).left ≫ ·) (toS_fst' N p hp))

theorem fst_toS_snd' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    ((fst (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp) ≫ pullback.snd _ _ = (Desc.UT N ⊗ Desc.UT N).hom ≫ p :=
  (Category.assoc _ _ _).trans ((congrArg ((fst (Desc.UT N) (Desc.UT N)).left ≫ ·) (toS_snd' N p hp)).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ p) (fst_hom' N))))

theorem snd_toS_snd' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    ((snd (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp) ≫ pullback.snd _ _ = (Desc.UT N ⊗ Desc.UT N).hom ≫ p :=
  (Category.assoc _ _ _).trans ((congrArg ((snd (Desc.UT N) (Desc.UT N)).left ≫ ·) (toS_snd' N p hp)).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ p) (snd_hom' N))))

theorem fst_toS_u' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    ((fst (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp) ≫ N.u =
      (fst (Desc.UT N) (Desc.UT N)).left ≫ (Desc.emb N p hp).left ≫ pullback.fst G.hom p :=
  (Category.assoc _ _ _).trans (congrArg ((fst (Desc.UT N) (Desc.UT N)).left ≫ ·) (embL_fst' N p hp).symm)

theorem snd_toS_u' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    ((snd (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp) ≫ N.u =
      (snd (Desc.UT N) (Desc.UT N)).left ≫ (Desc.emb N p hp).left ≫ pullback.fst G.hom p :=
  (Category.assoc _ _ _).trans (congrArg ((snd (Desc.UT N) (Desc.UT N)).left ≫ ·) (embL_fst' N p hp).symm)

end GlobalTheory.Mum.DescKP

namespace GlobalTheory.Mum.DescKP

theorem sum_eq_mT_emb : ∀ {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S} [GrpObj G] (N : Near π G) (V : (N.U ⊗ N.U).left.Opens) (m : V.toScheme ⟶ N.U.left) (hm : m ≫ N.U.hom = V.ι ≫ (N.U ⊗ N.U).hom), (∀ (T : Scheme.{0}) (v : T ⟶ V.toScheme) (s : T ⟶ S) (x y : Over.mk s ⟶ G), N.Pt s (v ≫ V.ι ≫ (fst N.U N.U).left) x.left → N.Pt s (v ≫ V.ι ≫ (snd N.U N.U).left) y.left → N.Pt s (v ≫ m) (x * y).left) → ∀ (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π), (DescKP.VT N V).ι ≫ (Desc.sum N p hp).left = DescKP.mT N V m hm ≫ (Desc.emb N p hp).left := by
  intro R _ _ S π G _ N V m hm law p hp
  let T0 : Over (pullback π π) := Over.mk ((VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom)
  let ι0 : T0 ⟶ Desc.UT N ⊗ Desc.UT N := Over.homMk (VT N V).ι rfl
  let a : T0 ⟶ (Over.pullback p).obj G := ι0 ≫ fst _ _ ≫ Desc.emb N p hp
  let b : T0 ⟶ (Over.pullback p).obj G := ι0 ≫ snd _ _ ≫ Desc.emb N p hp
  have hab : ι0 ≫ Desc.sum N p hp = a * b := by rw [Desc.sum, comp_mul]
  have wpt : ∀ c : T0 ⟶ (Over.pullback p).obj G, (c.left ≫ pullback.fst G.hom p) ≫ G.hom = T0.hom ≫ p := by
    intro c
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ p) (Over.w c)
  let x : Over.mk (T0.hom ≫ p) ⟶ G := Over.homMk (a.left ≫ pullback.fst G.hom p) (wpt a)
  let y : Over.mk (T0.hom ≫ p) ⟶ G := Over.homMk (b.left ≫ pullback.fst G.hom p) (wpt b)
  have hxy : (x * y).left = (a * b).left ≫ pullback.fst G.hom p :=
    (isGrpPullback_pullback G p).2 T0 a b x y rfl rfl
  have e : (pairU N ∣_ V) ≫ V.ι = (VT N V).ι ≫ pairU N := morphismRestrict_ι _ _
  have e' : ∀ {Z : Scheme.{0}} (h : (N.U ⊗ N.U).left ⟶ Z), (pairU N ∣_ V) ≫ V.ι ≫ h = (VT N V).ι ≫ pairU N ≫ h :=
    fun h => by rw [← Category.assoc, e, Category.assoc]
  have ptx : N.Pt (T0.hom ≫ p) ((pairU N ∣_ V) ≫ V.ι ≫ (fst N.U N.U).left) x.left := by
    refine ⟨(VT N V).ι ≫ (fst (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp, ?_, ?_, ?_⟩
    · exact (Category.assoc _ _ _).trans ((congrArg ((VT N V).ι ≫ ·) ((fst_toS_fst' N p hp).trans (pairU_fst' N).symm)).trans (e' _).symm)
    · exact (Category.assoc _ _ _).trans ((congrArg ((VT N V).ι ≫ ·) (fst_toS_snd' N p hp)).trans (Category.assoc _ _ _).symm)
    · exact (Category.assoc _ _ _).trans ((congrArg ((VT N V).ι ≫ ·) (fst_toS_u' N p hp)).trans (Category.assoc _ _ _).symm)
  have pty : N.Pt (T0.hom ≫ p) ((pairU N ∣_ V) ≫ V.ι ≫ (snd N.U N.U).left) y.left := by
    refine ⟨(VT N V).ι ≫ (snd (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp, ?_, ?_, ?_⟩
    · exact (Category.assoc _ _ _).trans ((congrArg ((VT N V).ι ≫ ·) ((snd_toS_fst' N p hp).trans (pairU_snd' N).symm)).trans (e' _).symm)
    · exact (Category.assoc _ _ _).trans ((congrArg ((VT N V).ι ≫ ·) (snd_toS_snd' N p hp)).trans (Category.assoc _ _ _).symm)
    · exact (Category.assoc _ _ _).trans ((congrArg ((VT N V).ι ≫ ·) (snd_toS_u' N p hp)).trans (Category.assoc _ _ _).symm)
  obtain ⟨x₀, h₁, h₂, h₃⟩ := law (VT N V).toScheme (pairU N ∣_ V) (T0.hom ≫ p) x y ptx pty
  have hx₀ : x₀ = mT N V m hm ≫ Desc.toS N p hp := by
    apply pullback.hom_ext
    · exact h₁.trans (((Category.assoc _ _ _).trans ((congrArg (mT N V m hm ≫ ·) (toS_fst' N p hp)).trans (mT_fst' N V m hm))).symm)
    · exact h₂.trans (((Category.assoc _ _ _).trans ((congrArg (mT N V m hm ≫ ·) (toS_snd' N p hp)).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ p) (mT_snd' N V m hm))))).symm)
  apply pullback.hom_ext
  · rw [Category.assoc (mT N V m hm), embL_fst']
    refine (?_ : _ = (mT N V m hm ≫ Desc.toS N p hp) ≫ N.u).trans (Category.assoc _ _ _)
    rw [← hx₀, h₃, hxy, ← hab]
    rfl
  · have w : (Desc.sum N p hp).left ≫ pullback.snd G.hom p = (Desc.UT N ⊗ Desc.UT N).hom := Over.w _
    rw [Category.assoc, w, Category.assoc, embL_snd', mT_snd']

end GlobalTheory.Mum.DescKP
