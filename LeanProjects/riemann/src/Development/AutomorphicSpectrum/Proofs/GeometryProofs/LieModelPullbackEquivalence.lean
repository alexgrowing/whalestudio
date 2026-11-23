import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LiePull

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
  {φ : G'.left ⟶ G.left}

def push (h : IsGrpPullback G' G f φ) {T : Over S'} {g : T.left ⟶ S} (hg : T.hom ≫ f = g) (v : T ⟶ G') :
    Over.mk g ⟶ G :=
  Over.homMk (v.left ≫ φ) (by
    have e : (v.left ≫ φ) ≫ G.hom = g := by
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w v, hg]
    exact e)

def pull (h : IsGrpPullback G' G f φ) {T : Over S'} {g : T.left ⟶ S} (hg : T.hom ≫ f = g)
    (a : Over.mk g ⟶ G) : T ⟶ G' :=
  Over.homMk (h.1.lift a.left T.hom (by rw [hg]; exact Over.w a)) (h.1.lift_snd _ _ _)

def pts (h : IsGrpPullback G' G f φ) {T : Over S'} {g : T.left ⟶ S} (hg : T.hom ≫ f = g) :
    (T ⟶ G') ≃* (Over.mk g ⟶ G) where
  toFun := push h hg
  invFun := pull h hg
  left_inv v := by
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · exact h.1.lift_fst _ _ _
    · exact (h.1.lift_snd _ _ _).trans (Over.w v).symm
  right_inv a := Over.OverMorphism.ext (h.1.lift_fst _ _ _)
  map_mul' v w := by
    subst hg
    exact Over.OverMorphism.ext (h.2 T v w _ _ rfl rfl).symm

theorem pts_left (h : IsGrpPullback G' G f φ) {T : Over S'} {g : T.left ⟶ S} (hg : T.hom ≫ f = g)
    (v : T ⟶ G') : (pts h hg v).left = v.left ≫ φ := rfl

variable {R : Type} [CommRing R]

theorem one_left (h : IsGrpPullback G' G f φ) (x' : Sp R ⟶ S') :
    (1 : Over.mk x' ⟶ G').left ≫ φ = (1 : Over.mk (x' ≫ f) ⟶ G).left := by
  have e := map_one (pts h (T := Over.mk x') (g := x' ≫ f) rfl)
  exact (pts_left h rfl _).symm.trans (congrArg (fun z => z.left) e)

theorem eps_assoc (x' : Sp R ⟶ S') : (epsAt x').hom ≫ f = (epsAt (x' ≫ f)).hom :=
  Category.assoc _ _ _

abbrev tanPts (h : IsGrpPullback G' G f φ) (x' : Sp R ⟶ S') :
    (epsAt x' ⟶ G') ≃* (epsAt (x' ≫ f) ⟶ G) :=
  pts h (T := epsAt x') (g := (epsAt (x' ≫ f)).hom) (eps_assoc x')

theorem fst_comp_base (x' : Sp R ⟶ S') :
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ (epsAt x').hom = x' := by
  have e : (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫
      CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom = 𝟙 _ := by
    ext r
    simp
  have e' := congrArg Spec.map e
  simp only [Spec.map_comp, Spec.map_id] at e'
  show _ ≫ Spec.map _ ≫ x' = x'
  rw [← Category.assoc, e', Category.id_comp]

theorem epsMul_comp_base (x' : Sp R ⟶ S') (c : R) :
    Spec.map (CommRingCat.ofHom (epsMul c)) ≫ (epsAt x').hom = (epsAt x').hom := by
  have e : (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ CommRingCat.ofHom (epsMul c) =
      CommRingCat.ofHom (algebraMap R (DualNumber R)) := by
    refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
    show epsMul c (algebraMap R (DualNumber R) r) = algebraMap R (DualNumber R) r
    rw [TrivSqZeroExt.algebraMap_eq_inl]
    ext <;> simp [epsMul]
  have e' := congrArg Spec.map e
  simp only [Spec.map_comp] at e'
  show _ ≫ Spec.map _ ≫ x' = Spec.map _ ≫ x'
  rw [← Category.assoc, e']

theorem isTan_iff (h : IsGrpPullback G' G f φ) (x' : Sp R ⟶ S') (v : epsAt x' ⟶ G') :
    IsTanAt G (x' ≫ f) (tanPts h x' v) ↔ IsTanAt G' x' v := by
  unfold IsTanAt
  constructor
  · intro t
    apply h.1.hom_ext
    · rw [Category.assoc, one_left h x', ← pts_left h (eps_assoc x') v]
      exact t
    · rw [Category.assoc, Over.w v, fst_comp_base]
      exact (Over.w (1 : Over.mk x' ⟶ G')).symm
  · intro t
    rw [← one_left h x', ← t, pts_left h (eps_assoc x') v, Category.assoc]

def modelPull (h : IsGrpPullback G' G f φ) (x' : Sp R ⟶ S') {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G (x' ≫ f) E) : LieModel G' x' E where
  pt e := (tanPts h x').symm (M.pt e)
  tan e := (isTan_iff h x' _).1 (by rw [MulEquiv.apply_symm_apply]; exact M.tan e)
  inj e e' w := M.inj ((tanPts h x').symm.injective w)
  onto v t := by
    obtain ⟨e, he⟩ := M.onto _ ((isTan_iff h x' v).2 t)
    exact ⟨e, by rw [he, MulEquiv.symm_apply_apply]⟩
  add e e' := by rw [M.add, map_mul]
  smul c e := by
    apply h.1.hom_ext
    · have a : ∀ e, ((tanPts h x').symm (M.pt e)).left ≫ φ = (M.pt e).left := fun e => by
        rw [← pts_left h (eps_assoc x'), MulEquiv.apply_symm_apply]
      rw [Category.assoc, a, a]
      exact M.smul c e
    · have b : ((tanPts h x').symm (M.pt e)).left ≫ G'.hom = (epsAt x').hom := Over.w _
      rw [Category.assoc, Over.w, b]
      exact (epsMul_comp_base x' c).symm

def modelPush (h : IsGrpPullback G' G f φ) (x' : Sp R ⟶ S') {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G' x' E) : LieModel G (x' ≫ f) E where
  pt e := tanPts h x' (M.pt e)
  tan e := (isTan_iff h x' _).2 (M.tan e)
  inj e e' w := M.inj ((tanPts h x').injective w)
  onto v t := by
    have t' : IsTanAt G (x' ≫ f) (tanPts h x' ((tanPts h x').symm v)) := by
      rw [MulEquiv.apply_symm_apply]; exact t
    obtain ⟨e, he⟩ := M.onto _ ((isTan_iff h x' _).1 t')
    exact ⟨e, by rw [he, MulEquiv.apply_symm_apply]⟩
  add e e' := by rw [M.add, map_mul]
  smul c e := by
    show (M.pt (c • e)).left ≫ φ = _ ≫ (M.pt e).left ≫ φ
    rw [M.smul, Category.assoc]

theorem lieModel_pullback : ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ (R : Type) [CommRing R] (x' : Sp R ⟶ S') (E : Type) [AddCommGroup E] [Module R E], (∀ M : LieModel G (x' ≫ f) E, ∃ M' : LieModel G' x' E, ∀ e, (M'.pt e).left ≫ φ = (M.pt e).left) ∧ ∀ M' : LieModel G' x' E, ∃ M : LieModel G (x' ≫ f) E, ∀ e, (M'.pt e).left ≫ φ = (M.pt e).left := by
  intro S S' G G' _ _ f φ h R _ x' E _ _
  refine ⟨fun M => ⟨modelPull h x' M, fun e => ?_⟩, fun M' => ⟨modelPush h x' M', fun e => rfl⟩⟩
  show ((tanPts h x').symm (M.pt e)).left ≫ φ = _
  rw [← pts_left h (eps_assoc x'), MulEquiv.apply_symm_apply]

end GlobalTheory.CompanionTheory.Ar.LiePull
