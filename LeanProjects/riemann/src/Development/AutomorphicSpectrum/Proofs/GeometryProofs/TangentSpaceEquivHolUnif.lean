import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackEquivalence
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeLin

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {z : Spec (CommRingCat.of ℂ) ⟶ X}
  {A : Over (Sp ℂ)} [GrpObj A] {φ : A.left ⟶ G.left}

abbrev tanEquiv (hp : IsGrpPullback A G z φ) : (epsR ℂ ⟶ A) ≃* (epsAt z ⟶ G) :=
  LiePull.pts hp (T := epsR ℂ) (g := (epsAt z).hom) rfl

theorem unit_left (hp : IsGrpPullback A G z φ) : η[A].left ≫ φ = (1 : Over.mk z ⟶ G).left := by
  have e := map_one (LiePull.pts hp (T := 𝟙_ (Over (Sp ℂ))) (g := z) (Category.id_comp z))
  have e' := congrArg (fun q => q.left) e
  have h1 : (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A) = η[A] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  rw [h1] at e'
  exact e'

theorem isTangent_iff (hp : IsGrpPullback A G z φ) (x : epsR ℂ ⟶ A) :
    IsTangent x ↔ IsTanAt G z (tanEquiv hp x) := by
  unfold IsTangent IsTanAt
  constructor
  · intro t
    rw [← unit_left hp, ← t, Category.assoc]
    rfl
  · intro t
    apply hp.1.hom_ext
    · rw [Category.assoc, unit_left hp, ← t]
      rfl
    · have e : (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))) ≫
          CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom = 𝟙 _ := by
        ext r
        simp
      have e' := congrArg Spec.map e
      simp only [Spec.map_comp, Spec.map_id] at e'
      have hx : x.left ≫ A.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := Over.w x
      have h0 : η[A].left ≫ A.hom = 𝟙 _ := Over.w η[A]
      rw [Category.assoc, hx, h0]
      exact e'

theorem exists_linearEquiv : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (z : Spec (CommRingCat.of ℂ) ⟶ X) (V : Type)
    [AddCommGroup V] [Module ℂ V] (M : LieModel G z V) (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ G.left) (L : LB A.left)
    (g : ℕ) (u : HolUnif A L g), IsGrpPullback A G z φ → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) →
    (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) →
    ∃ D : V ≃ₗ[ℂ] (Fin g → ℂ), ∀ v, ∃ x : epsR ℂ ⟶ A, IsTangent x ∧ x.left ≫ φ = (M.pt v).left ∧ u.IsDiff (D v) x := by
  intro X G _ z V _ _ M A _ φ L g u hp h1 h2
  let Φ := tanEquiv hp
  let x : V → (epsR ℂ ⟶ A) := fun v => Φ.symm (M.pt v)
  have hΦx : ∀ v, Φ (x v) = M.pt v := fun v => Φ.apply_symm_apply _
  have hleft : ∀ v, (x v).left ≫ φ = (M.pt v).left := fun v => congrArg (fun q => q.left) (hΦx v)
  have tx : ∀ v, IsTangent (x v) := fun v => (isTangent_iff hp _).2 (by
    change IsTanAt G z (Φ (x v))
    rw [hΦx]
    exact M.tan v)
  have xadd : ∀ v v', x (v + v') = x v * x v' := fun v v' => by
    simp only [x]
    rw [M.add, map_mul]
  have xsmul : ∀ (c : ℂ) v, x (c • v) = Chart.spMap (Chart.scaleD c) ≫ x v := fun c v => by
    apply Φ.injective
    rw [hΦx]
    apply Over.OverMorphism.ext
    rw [M.smul c v, ← hleft v]
    exact (Category.assoc _ _ _).symm
  have tan' : ∀ {y : epsR ℂ ⟶ A}, IsTangent y → Chart.IsTan y := fun h => (Chart.isTan_iff _).2 h
  choose d hd hu using fun v => h1 (x v) (tx v)
  let Dl : V →ₗ[ℂ] (Fin g → ℂ) :=
    { toFun := d
      map_add' := fun v v' => by
        symm
        apply hu
        rw [xadd]
        exact UnifDifferential.isDiff_mul u (tan' (tx v)) (tan' (tx v')) (hd v) (hd v')
      map_smul' := fun c v => by
        symm
        apply hu
        rw [xsmul]
        exact UnifDifferential.isDiff_scale u (hd v) c }
  have inj : Function.Injective Dl := fun v v' e => by
    have e' : d v = d v' := e
    have h : x v = x v' := (h2 (d v')).unique ⟨tx v, e' ▸ hd v⟩ ⟨tx v', hd v'⟩
    exact M.inj (by rw [← hΦx, ← hΦx, h])
  have surj : Function.Surjective Dl := fun w => by
    obtain ⟨y, ⟨ty, dy⟩, -⟩ := h2 w
    obtain ⟨v, hv⟩ := M.onto _ ((isTangent_iff hp y).1 ty)
    have hy : x v = y := Φ.injective (by rw [hΦx]; exact hv)
    exact ⟨v, (hu v w (hy ▸ dy)).symm⟩
  exact ⟨LinearEquiv.ofBijective Dl ⟨inj, surj⟩, fun v => ⟨x v, tx v, hleft v, hd v⟩⟩

end GlobalTheory.CompanionTheory.Ar.HodgeLin
