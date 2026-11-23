import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LieMove

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
  {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {R : Type} [CommRing R] {x : Sp R ⟶ S'}

theorem fst_comp_alg : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have e : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
    ext r; simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [e]
  exact Spec.map_id _

theorem epsMul_comp_alg (c : R) : Spec.map (CommRingCat.ofHom (epsMul c)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have e : (epsMul c).comp (algebraMap R (DualNumber R)) = algebraMap R (DualNumber R) := by
    ext r <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  rw [e]

def pushEps (h : IsGrpPullback G' G f φ) (p : epsAt x ⟶ G') : epsAt (x ≫ f) ⟶ G :=
  Over.homMk (p.left ≫ φ) (by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w p]
    exact Category.assoc _ _ _)

def liftEps (h : IsGrpPullback G' G f φ) (v : epsAt (x ≫ f) ⟶ G) : epsAt x ⟶ G' :=
  Over.homMk (h.1.lift v.left (epsAt x).hom ((Over.w v).trans (Category.assoc _ _ _).symm)) (h.1.lift_snd _ _ _)

theorem pushEps_left (h : IsGrpPullback G' G f φ) (p : epsAt x ⟶ G') : (pushEps h p).left = p.left ≫ φ := rfl

theorem liftEps_left (h : IsGrpPullback G' G f φ) (v : epsAt (x ≫ f) ⟶ G) : (liftEps h v).left ≫ φ = v.left :=
  h.1.lift_fst _ _ _

theorem push_lift (h : IsGrpPullback G' G f φ) (v : epsAt (x ≫ f) ⟶ G) : pushEps h (liftEps h v) = v :=
  Over.OverMorphism.ext (liftEps_left h v)

theorem pushEps_inj (h : IsGrpPullback G' G f φ) : Function.Injective (pushEps (x := x) h) := fun p q e =>
  Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun z => z.left) e) ((Over.w p).trans (Over.w q).symm))

theorem pushEps_mul (h : IsGrpPullback G' G f φ) (p q : epsAt x ⟶ G') :
    pushEps h (p * q) = pushEps h p * pushEps h q := by
  let U : epsAt (x ≫ f) ⟶ Over.mk ((epsAt x).hom ≫ f) := Over.homMk (𝟙 _) (by simp)
  let V : Over.mk ((epsAt x).hom ≫ f) ⟶ epsAt (x ≫ f) := Over.homMk (𝟙 _) (by simp)
  have UV : U ≫ V = 𝟙 _ := Over.OverMorphism.ext (by simp [U, V])
  have e := h.2 (epsAt x) p q (V ≫ pushEps h p) (V ≫ pushEps h q) (by simp [V, pushEps_left])
    (by simp [V, pushEps_left])
  have e' : U ≫ ((V ≫ pushEps h p) * (V ≫ pushEps h q)) = pushEps h p * pushEps h q := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, UV, Category.id_comp, Category.id_comp]
  rw [← e']
  apply Over.OverMorphism.ext
  rw [pushEps_left, ← e]
  simp [U]

theorem one_left (h : IsGrpPullback G' G f φ) :
    (1 : Over.mk x ⟶ G').left ≫ φ = (1 : Over.mk (x ≫ f) ⟶ G).left :=
  congrArg (fun z => z.left) (map_one (pushHom h (Over.mk x)))

theorem tan_iff (h : IsGrpPullback G' G f φ) (p : epsAt x ⟶ G') :
    IsTanAt G' x p ↔ IsTanAt G (x ≫ f) (pushEps h p) := by
  constructor
  · intro t
    show _ ≫ p.left ≫ φ = _
    rw [← Category.assoc, t, one_left h]
  · intro t
    refine h.1.hom_ext ?_ ?_
    · rw [Category.assoc, one_left h]
      exact t
    · have w := Over.w p
      have w₁ := Over.w (1 : Over.mk x ⟶ G')
      rw [Category.assoc, w, w₁]
      show _ ≫ Spec.map _ ≫ x = x
      rw [← Category.assoc, fst_comp_alg, Category.id_comp]

def pullModel {L : Type} [AddCommGroup L] [Module R L] (h : IsGrpPullback G' G f φ) (M : LieModel G (x ≫ f) L) :
    LieModel G' x L where
  pt e := liftEps h (M.pt e)
  tan e := (tan_iff h _).2 (by rw [push_lift]; exact M.tan e)
  inj a b e := M.inj ((push_lift h _).symm.trans ((congrArg (pushEps h) e).trans (push_lift h _)))
  onto v t := by
    obtain ⟨e, he⟩ := M.onto _ ((tan_iff h v).1 t)
    exact ⟨e, pushEps_inj h (by rw [push_lift, he])⟩
  add a b := pushEps_inj h (by rw [pushEps_mul, push_lift, push_lift, push_lift, M.add])
  smul c e := by
    refine h.1.hom_ext ?_ ?_
    · rw [liftEps_left, Category.assoc, liftEps_left, M.smul]
    · have w := fun v => Over.w (liftEps (x := x) h v)
      rw [Category.assoc, w, w]
      show Spec.map _ ≫ x = _ ≫ Spec.map _ ≫ x
      rw [← Category.assoc, epsMul_comp_alg]

def pushModel {L : Type} [AddCommGroup L] [Module R L] (h : IsGrpPullback G' G f φ) (M : LieModel G' x L) :
    LieModel G (x ≫ f) L where
  pt e := pushEps h (M.pt e)
  tan e := (tan_iff h _).1 (M.tan e)
  inj a b e := M.inj (pushEps_inj h e)
  onto v t := by
    obtain ⟨e, he⟩ := M.onto (liftEps h v) ((tan_iff h _).2 (by rw [push_lift]; exact t))
    exact ⟨e, by rw [he, push_lift]⟩
  add a b := by rw [M.add, pushEps_mul]
  smul c e := by
    show (M.pt (c • e)).left ≫ φ = _ ≫ (M.pt e).left ≫ φ
    rw [M.smul, Category.assoc]

theorem models_correspond (h : IsGrpPullback G' G f φ) (L : Type) [AddCommGroup L] [Module R L] :
    (∀ M : LieModel G (x ≫ f) L, ∃ M' : LieModel G' x L, ∀ e, (M'.pt e).left ≫ φ = (M.pt e).left) ∧
      ∀ M' : LieModel G' x L, ∃ M : LieModel G (x ≫ f) L, ∀ e, (M'.pt e).left ≫ φ = (M.pt e).left :=
  ⟨fun M => ⟨pullModel h M, fun _ => liftEps_left h _⟩, fun M' => ⟨pushModel h M', fun _ => rfl⟩⟩

end GlobalTheory.CompanionTheory.Ar.LieMove

theorem GlobalTheory.CompanionTheory.Ar.LieMove.main : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (x : Sp R ⟶ X) (G : Over X) [GrpObj G]
    (G₀ : Over (Sp R)) [GrpObj G₀] (ψ : G₀.left ⟶ G.left) (L : Type) [AddCommGroup L] [Module R L],
    IsGrpPullback G₀ G x ψ → (∀ M : LieModel G x L, ∃ M₀ : LieModel G₀ (𝟙 _) L, ∀ e, (M₀.pt e).left ≫ ψ = (M.pt e).left) ∧
      ∀ M₀ : LieModel G₀ (𝟙 _) L, ∃ M : LieModel G x L, ∀ e, (M₀.pt e).left ≫ ψ = (M.pt e).left := by
  intro R _ X x G _ G₀ _ ψ L _ _ h
  have key : ∀ y : Sp R ⟶ X, 𝟙 _ ≫ x = y →
      (∀ M : LieModel G y L, ∃ M₀ : LieModel G₀ (𝟙 _) L, ∀ e, (M₀.pt e).left ≫ ψ = (M.pt e).left) ∧
        ∀ M₀ : LieModel G₀ (𝟙 _) L, ∃ M : LieModel G y L, ∀ e, (M₀.pt e).left ≫ ψ = (M.pt e).left := by
    rintro _ rfl
    exact GlobalTheory.CompanionTheory.Ar.LieMove.models_correspond h L
  exact key x (Category.id_comp x)
