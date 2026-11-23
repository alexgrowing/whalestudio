import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModelBaseChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondence
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.CompanionTheory.Ar.LieBc

theorem exists_model_of_eq {S : Scheme.{0}} {R : Type} [CommRing R] (G : Over S) [GrpObj G] {x₁ x₂ : Sp R ⟶ S}
    (hx : x₁ = x₂) {T : Type} [AddCommGroup T] [Module R T] (M₁ : LieModel G x₁ T) :
    ∃ M₂ : LieModel G x₂ T, ∀ t, (M₂.pt t).left = (M₁.pt t).left := by
  subst hx
  exact ⟨M₁, fun _ => rfl⟩

theorem injective_of_isBaseChange {K K' : Type} [Field K] [Field K'] [Algebra K K'] {V T : Type} [AddCommGroup V]
    [Module K V] [AddCommGroup T] [Module K T] [Module K' T] [IsScalarTower K K' T] {j : V →ₗ[K] T}
    (hj : IsBaseChange K' j) : Function.Injective j := by
  have e : ⇑j = hj.equiv ∘ TensorProduct.mk K K' V 1 := by
    funext x
    simp [IsBaseChange.equiv_tmul]
  rw [e]
  exact hj.equiv.injective.comp (Module.FaithfullyFlat.tensorProduct_mk_injective V)

theorem span_range_of_isBaseChange {K K' : Type} [CommRing K] [CommRing K'] [Algebra K K'] {V T : Type}
    [AddCommGroup V] [Module K V] [AddCommGroup T] [Module K T] [Module K' T] [IsScalarTower K K' T]
    {j : V →ₗ[K] T} (hj : IsBaseChange K' j) : Submodule.span K' (Set.range j) = ⊤ := by
  rw [eq_top_iff]
  intro t _
  refine hj.inductionOn t (fun t => t ∈ Submodule.span K' (Set.range j)) (Submodule.zero_mem _)
    (fun m => Submodule.subset_span ⟨m, rfl⟩) (fun s n h => Submodule.smul_mem _ s h)
    (fun a b ha hb => Submodule.add_mem _ ha hb)

end GlobalTheory.CompanionTheory.Ar.LieBc

theorem GlobalTheory.CompanionTheory.Ar.LieBc.main : ∀ (L L' : Type) [Field L] [Field L'] (e : L →+* L') (G : Over (Sp L)) (G' : Over (Sp L')) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G (spMap e) φ → ∀ (V : Type) [AddCommGroup V] [Module L V] (MV : LieModel G (𝟙 (Sp L)) V), ∃ (V' : Type) (_ : AddCommGroup V') (_ : Module L' V') (MV' : LieModel G' (𝟙 (Sp L')) V') (j : V →+ V'), (∀ (c : L) x, j (c • x) = e c • j x) ∧ Function.Injective j ∧ (∀ x, (MV'.pt (j x)).left ≫ φ = spMap (dualMap e) ≫ (MV.pt x).left) ∧ Submodule.span L' (Set.range j) = ⊤ := by
  intro L L' _ _ e G G' _ _ _ _ φ h V _ _ MV
  letI : Algebra L L' := e.toAlgebra
  obtain ⟨T, iT, mT, mR, tower, M', j, hl, hbc⟩ :=
    GlobalTheory.CompanionTheory.Ar.FlagFib.lieModel_liftBaseChange (Sp L) G L L' (𝟙 _) V MV
  have hx : spMap (algebraMap L L') ≫ 𝟙 (Sp L) = 𝟙 (Sp L') ≫ spMap e := by
    rw [Category.comp_id, Category.id_comp]
    rfl
  obtain ⟨M₂, hM₂⟩ := GlobalTheory.CompanionTheory.Ar.LieBc.exists_model_of_eq G hx M'
  refine ⟨T, iT, mT, GlobalTheory.CompanionTheory.Ar.LieMove.pullModel h M₂, j.toAddMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro c x
    change j (c • x) = e c • j x
    rw [map_smul]
    exact (algebraMap_smul L' c (j x)).symm
  · exact GlobalTheory.CompanionTheory.Ar.LieBc.injective_of_isBaseChange hbc
  · intro x
    have e₁ := hl x
    have e₂ : (M'.pt (j x)).left ≫ 𝟙 G.left = spMap (dualMap (algebraMap L L')) ≫ (MV.pt x).left := e₁
    change (GlobalTheory.CompanionTheory.Ar.LieMove.liftEps h (M₂.pt (j x))).left ≫ φ = _
    rw [GlobalTheory.CompanionTheory.Ar.LieMove.liftEps_left, hM₂]
    exact (Category.comp_id _).symm.trans e₂
  · exact GlobalTheory.CompanionTheory.Ar.LieBc.span_range_of_isBaseChange hbc
