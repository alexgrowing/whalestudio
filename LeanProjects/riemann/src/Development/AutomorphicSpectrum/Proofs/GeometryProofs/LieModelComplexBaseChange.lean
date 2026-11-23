import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelIsBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieSigma

variable {S : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

theorem dualMap_comp_algebraMap (φ : R →+* R') :
    (dualMap φ).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp φ := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_comp_dualMap (φ : R →+* R') :
    (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (dualMap φ)
      = φ.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => ?_
  simp [GlobalTheory.CompanionTheory.Ar.dualMap]

theorem dualMap_comp_epsMul (φ : R →+* R') (a : R) :
    (dualMap φ).comp (epsMul a) = (epsMul (φ a)).comp (dualMap φ) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [GlobalTheory.CompanionTheory.Ar.dualMap, GlobalTheory.CompanionTheory.Ar.epsMul, mul_comm]

theorem comp_one_over {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) : u ≫ (1 : X ⟶ M) = 1 := by
  exact comp_one u

theorem comp_mul_over {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) (p q : X ⟶ M) :
    u ≫ (p * q) = (u ≫ p) * (u ≫ q) := by
  exact comp_mul u p q

def pullEps (φ : R →+* R') (x : Sp R ⟶ S) : epsAt (spMap φ ≫ x) ⟶ epsAt x :=
  Over.homMk (spMap (dualMap φ)) (by
    simp only [Over.mk_hom, epsAt]
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      dualMap_comp_algebraMap])

def pullPt (φ : R →+* R') (x : Sp R ⟶ S) : Over.mk (spMap φ ≫ x) ⟶ Over.mk x :=
  Over.homMk (spMap φ) rfl

theorem isTanAt_pull (G : Over S) [GrpObj G] (φ : R →+* R') (x : Sp R ⟶ S) (v : epsAt x ⟶ G)
    (hv : IsTanAt G x v) : IsTanAt G (spMap φ ≫ x) (pullEps φ x ≫ v) := by
  unfold IsTanAt at hv ⊢
  rw [← comp_one_over (pullPt φ x), Over.comp_left, Over.comp_left, ← hv]
  have key : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R' R' R').toRingHom) ≫ spMap (dualMap φ)
      = spMap φ ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, fst_comp_dualMap]
  simp only [pullEps, pullPt, Over.homMk_left]
  rw [reassoc_of% key]

theorem exists_linear (G : Over S) [GrpObj G] (φ : R →+* R') (x : Sp R ⟶ S)
    {E E₀ : Type} [AddCommGroup E] [Module R E] [AddCommGroup E₀] [Module R' E₀] [Module R E₀]
    (hs : ∀ (a : R) (e : E₀), a • e = φ a • e) (M : LieModel G x E)
    (M₀ : LieModel G (spMap φ ≫ x) E₀) :
    ∃ j : E →ₗ[R] E₀, ∀ e, M₀.pt (j e) = pullEps φ x ≫ M.pt e := by
  choose j hj using fun e => M₀.onto _ (isTanAt_pull G φ x (M.pt e) (M.tan e))
  refine ⟨{ toFun := j, map_add' := ?_, map_smul' := ?_ }, hj⟩
  · intro e e'
    apply M₀.inj
    rw [M₀.add, hj, hj, hj, M.add, comp_mul_over]
  · intro c e
    apply M₀.inj
    rw [RingHom.id_apply, hs, hj]
    apply Over.OverMorphism.ext
    rw [M₀.smul, hj, Over.comp_left, Over.comp_left, M.smul]
    simp only [pullEps, Over.homMk_left, ← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, dualMap_comp_epsMul]

def transport {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {E E' : Type} [AddCommGroup E] [Module R E]
    [AddCommGroup E'] [Module R E'] (M : LieModel G x E) (f : E' ≃ₗ[R] E) : LieModel G x E' where
  pt e := M.pt (f e)
  tan e := M.tan _
  inj := M.inj.comp f.injective
  onto v hv := by
    obtain ⟨e, he⟩ := M.onto v hv
    exact ⟨f.symm e, by simpa using he⟩
  add e e' := by simp only [map_add]; exact M.add _ _
  smul c e := by simp only [map_smul]; exact M.smul _ _

open GroundTheory.Heights₂.Heights in

theorem lieModel_fibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ S) (V : Type) [AddCommGroup V] [Module (𝓞 L) V] (M : LieModel G z V) (σ : L →+* ℂ), ∃ Mσ : LieModel G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) (GroundTheory.Heights₂.Heights.Fibre σ V), ∀ e : V, M.Lifts (σ.comp (algebraMap (𝓞 L) L)) (𝟙 G.left) e (Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e)) := by
  intro S G _ _ _ L _ _ z V _ _ M σ
  classical
  let _ : Algebra (𝓞 L) ℂ := (σ.comp (algebraMap (𝓞 L) L)).toAlgebra
  obtain ⟨E₀, i1, i2, ⟨M₀⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists S G ℂ (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z)
  let _ : Module (𝓞 L) E₀ := Module.compHom E₀ (σ.comp (algebraMap (𝓞 L) L))
  have _ : IsScalarTower (𝓞 L) ℂ E₀ := ⟨fun a b e => by
    show ((σ.comp (algebraMap (𝓞 L) L)) a * b) • e = (σ.comp (algebraMap (𝓞 L) L)) a • b • e
    rw [mul_smul]⟩
  obtain ⟨j, hj⟩ := exists_linear G (σ.comp (algebraMap (𝓞 L) L)) z (fun a e => rfl) M M₀
  have hl : ∀ e, M.Lifts (algebraMap (𝓞 L) ℂ) (𝟙 G.left) e (M₀.pt (j e)) := by
    intro e
    unfold GlobalTheory.CompanionTheory.Ar.LieModel.Lifts
    rw [hj e, Over.comp_left, Category.comp_id]
    rfl
  have hb := GlobalTheory.T.lie_model_isBaseChange S G (𝓞 L) ℂ z V E₀ M M₀ j hl
  let f : GroundTheory.Heights₂.Heights.Fibre σ V ≃ₗ[ℂ] E₀ := hb.equiv
  refine ⟨transport M₀ f, fun e => ?_⟩
  have hf : f ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e) = j e := by
    show hb.equiv ((1 : ℂ) ⊗ₜ[𝓞 L] e) = j e
    rw [IsBaseChange.equiv_tmul, one_smul]
  unfold GlobalTheory.CompanionTheory.Ar.LieModel.Lifts
  show (M₀.pt (f ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e))).left ≫ 𝟙 _ = _
  rw [hf, hj e, Over.comp_left, Category.comp_id]
  rfl

end GlobalTheory.CompanionTheory.Ar.LieSigma
