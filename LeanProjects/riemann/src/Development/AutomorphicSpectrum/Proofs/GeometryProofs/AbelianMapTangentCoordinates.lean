import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackEquivalence
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PeriodCoord

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {A R : Type} [CommRing A] [CommRing R]

theorem dualMap_comp_base (i : Sp A ⟶ X) (θ : A →+* R) :
    spMap (dualMap θ) ≫ (epsAt i).hom = (epsAt (𝟙 (Sp R) ≫ spMap θ ≫ i)).hom := by
  have e : (CommRingCat.ofHom (algebraMap A (DualNumber A))) ≫ CommRingCat.ofHom (dualMap θ) =
      CommRingCat.ofHom θ ≫ CommRingCat.ofHom (algebraMap R (DualNumber R)) := by
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    show dualMap θ (algebraMap A (DualNumber A) a) = algebraMap R (DualNumber R) (θ a)
    rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl]
    ext <;> simp [dualMap]
  have e' := congrArg Spec.map e
  simp only [Spec.map_comp] at e'
  show spMap (dualMap θ) ≫ Spec.map _ ≫ i = Spec.map _ ≫ 𝟙 (Sp R) ≫ spMap θ ≫ i
  rw [Category.id_comp, ← Category.assoc, e', Category.assoc]

def pushEps (i : Sp A ⟶ X) (θ : A →+* R) (v : epsAt i ⟶ G) : epsAt (𝟙 (Sp R) ≫ spMap θ ≫ i) ⟶ G :=
  Over.homMk (spMap (dualMap θ) ≫ v.left) (by
    have e : (spMap (dualMap θ) ≫ v.left) ≫ G.hom = (epsAt (𝟙 (Sp R) ≫ spMap θ ≫ i)).hom := by
      rw [Category.assoc, Over.w v, dualMap_comp_base]
    exact e)

theorem isTanAt_pushEps (i : Sp A ⟶ X) (θ : A →+* R) {v : epsAt i ⟶ G} (h : IsTanAt G i v) :
    IsTanAt G (𝟙 (Sp R) ≫ spMap θ ≫ i) (pushEps i θ v) := by
  unfold IsTanAt at h ⊢
  have key : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (dualMap θ)) =
      Spec.map (CommRingCat.ofHom θ) ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    simp [dualMap]
  let s : Over.mk (𝟙 (Sp R) ≫ spMap θ ≫ i) ⟶ Over.mk i :=
    Over.homMk (spMap θ) (by simp)
  have h1 : s ≫ (1 : Over.mk i ⟶ G) = 1 := MonObj.comp_one s
  have h2 := congrArg CommaMorphism.left h1
  refine Eq.trans ?_ h2
  change _ = spMap θ ≫ (1 : Over.mk i ⟶ G).left
  rw [← h]
  change Spec.map _ ≫ spMap (dualMap θ) ≫ v.left = _
  rw [← Category.assoc, key, Category.assoc]

theorem exists_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (A : Type) [CommRing A] (i : Sp A ⟶ X) (N : ℕ) (v : Fin N → (epsAt i ⟶ t.G)) (R : Type) [CommRing R] (t' : SAB H (Sp R)) (θ : A →+* R) (m : SABMap t' t (spMap θ ≫ i)) (g : ℕ) (M : LieModel t'.G (𝟙 (Sp R)) (Fin g → R)), (∀ k, IsTanAt t.G i (v k)) → ∃ x : Fin N → Fin g → R, ∀ k, (M.pt (x k)).left ≫ m.φ = spMap (dualMap θ) ≫ (v k).left := by
  intro E _ _ _ H X t A _ i N v R _ t' θ m g M hv
  have hx : ∀ k, ∃ e : Fin g → R, (M.pt e).left ≫ m.φ = spMap (dualMap θ) ≫ (v k).left := fun k => by
    have ht : IsTanAt t'.G (𝟙 (Sp R)) ((LiePull.tanPts m.cart (𝟙 (Sp R))).symm (pushEps i θ (v k))) :=
      (LiePull.isTan_iff m.cart (𝟙 (Sp R)) _).1 (by
        rw [MulEquiv.apply_symm_apply]
        exact isTanAt_pushEps i θ (hv k))
    obtain ⟨e, he⟩ := M.onto _ ht
    refine ⟨e, ?_⟩
    rw [he, ← LiePull.pts_left m.cart (LiePull.eps_assoc (𝟙 (Sp R))), MulEquiv.apply_symm_apply]
    rfl
  choose x hx using hx
  exact ⟨x, hx⟩

end GlobalTheory.CompanionTheory.Ar.PeriodCoord
