import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGrpSchemeDescendsToFgSubring
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyConnectedDescendsToFinitelyGenerateStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SeparatedPropernessFgSubalgebraStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemeModelBaseChangeSubalgebraStatement
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem prop_snd_of_isPullback (P : MorphismProperty Scheme.{0}) [P.IsStableUnderBaseChange]
    {X Y S' S : Scheme.{0}} {φ : X ⟶ Y} {a : X ⟶ S'} {b : Y ⟶ S} {f : S' ⟶ S}
    (h : IsPullback φ a b f) (ha : P a) : P (pullback.snd b f) := by
  have sq : IsPullback h.isoPullback.inv (pullback.snd b f) a (𝟙 S') :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  exact P.of_isPullback sq ha

theorem isCommMonObj_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G]
    [IsCommMonObj G] {b : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G b φ) : IsCommMonObj G' := by
  have key : ∀ {T : Over S'} (x y : T ⟶ G'), x * y = y * x := by
    intro T x y
    let x₀ : Over.mk (T.hom ≫ b) ⟶ G := Over.homMk (x.left ≫ φ) (by
      simp only [Over.mk_hom, Category.assoc, h.1.w, Over.w_assoc])
    let y₀ : Over.mk (T.hom ≫ b) ⟶ G := Over.homMk (y.left ≫ φ) (by
      simp only [Over.mk_hom, Category.assoc, h.1.w, Over.w_assoc])
    have e₁ := h.2 T x y x₀ y₀ rfl rfl
    have e₂ := h.2 T y x y₀ x₀ rfl rfl
    have c : x₀ * y₀ = y₀ * x₀ := mul_comm _ _
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · rw [← e₁, ← e₂, c]
    · rw [Over.w, Over.w]
  refine ⟨?_⟩
  rw [mul_eq_mul, comp_mul, key]
  simp

theorem abelianScheme_descends_to_fg_subring : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (F : Finset R), IsAbelianScheme A → ∃ (S : Subring R) (B : Over (Sp S)) (_ : GrpObj B) (φ : A.left ⟶ B.left), (F : Set R) ⊆ S ∧ Algebra.FiniteType ℤ S ∧ IsAbelianScheme B ∧ IsGrpPullback A B (spMap S.subtype) φ := by
  intro R _ A _ F hA
  haveI : IsCommMonObj A := hA.comm
  haveI : IsProper A.hom := hA.proper
  obtain ⟨k, A₀, i₀, c₀, φ, hFk, hk, s₀, sep₀, qc₀, hφ⟩ :=
    GlobalTheory.smooth_grpScheme_descends_to_fg_subring R A F hA.smooth inferInstance inferInstance
  haveI : IsNoetherianRing k := Algebra.FiniteType.isNoetherianRing ℤ k
  have hφ' : IsGrpPullback A A₀ (spMap (algebraMap k R)) φ := hφ
  obtain ⟨R₁, hR₁, pr₁⟩ := GlobalTheory.T.separated_properness_fg_subalgebra k R A₀.left A₀.hom sep₀ inferInstance qc₀
    (prop_snd_of_isPullback @IsProper hφ.1 hA.proper)
  obtain ⟨i₁, φ₁, h₁₀, h₁, -⟩ := GlobalTheory.T.abelianScheme_model_baseChange_subalgebra k R A A₀ φ hφ' R₁
  haveI : Algebra.FiniteType k R₁ := (Subalgebra.fg_iff_finiteType R₁).1 hR₁
  haveI : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing k R₁
  haveI : IsCommMonObj (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R₁)))) :=
    isCommMonObj_of_isGrpPullback h₁₀
  have hk₁ : Algebra.FiniteType ℤ R₁ := Algebra.FiniteType.trans hk inferInstance
  have h₁' : IsGrpPullback A (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R₁))))
      (spMap (algebraMap R₁ R)) φ₁ := h₁
  have sm₁ : Smooth (pullback.snd A₀.hom (spMap (algebraMap k R₁))) :=
    by haveI := s₀; infer_instance
  obtain ⟨R₂, hR₂, gc₂⟩ := GlobalTheory.T.geometricallyConnected_descends_to_finitelyGenerated R₁ R (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R₁))))
    sm₁ pr₁ (prop_snd_of_isPullback @GeometricallyConnected h₁.1 hA.geomConnected)
  obtain ⟨i₂, φ₂, h₂₁, h₂, -⟩ := @GlobalTheory.T.abelianScheme_model_baseChange_subalgebra R₁ R _ _ _ A _
    (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R₁)))) i₁ φ₁ h₁' R₂
  haveI : Algebra.FiniteType R₁ R₂ := (Subalgebra.fg_iff_finiteType R₂).1 hR₂
  have hk₂ : Algebra.FiniteType ℤ R₂ := Algebra.FiniteType.trans hk₁ inferInstance
  refine ⟨R₂.toSubring, Over.mk (pullback.snd (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R₁)))).hom
    (spMap (algebraMap R₁ R₂))), i₂, φ₂, ?_, hk₂, ?_, h₂⟩
  · intro x hx
    have hx₁ : x ∈ R₁ := R₁.algebraMap_mem (⟨x, hFk hx⟩ : k)
    exact R₂.algebraMap_mem (⟨x, hx₁⟩ : R₁)
  · haveI := sm₁
    haveI := pr₁
    exact ⟨isCommMonObj_of_isGrpPullback h₂₁, by dsimp only [Over.mk_hom]; infer_instance,
      by dsimp only [Over.mk_hom]; infer_instance, gc₂⟩

end GlobalTheory.CompanionTheory.Ar.Approx
