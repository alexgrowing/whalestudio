import Mathlib
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLie
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueSemilinearStatement

noncomputable section

namespace PositivityTheory.HtPt.Htat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem lie_fin : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R : Type) [CommRing R] (x : Sp R ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G x E), Module.Finite R E ∧ Module.Projective R E := by
  intro S G _ _ R _ x E _ _ M
  obtain ⟨J, hJ, f, hspan, hch⟩ := Lie.exists_cover (G := G) x
  have hloc : ∀ i : J, ∃ (F : Type) (_ : AddCommGroup F) (_ : Module R F) (_ : Module (Localization.Away (f i)) F) (_ : IsScalarTower R (Localization.Away (f i)) F) (_ : Module.Finite (Localization.Away (f i)) F) (_ : Module.Projective (Localization.Away (f i)) F) (r : E →ₗ[R] F), IsLocalizedModule (Submonoid.powers (f i)) r := by
    intro i
    obtain ⟨P, _, _, _, _, hfin, hproj, m, hm⟩ := (hch i).lieChart
    have hC : IsUnit ((algebraMap R (Localization.Away (f i))) (f i)) := IsLocalization.Away.algebraMap_isUnit (f i)
    let Mi := m (Localization.Away (f i)) hC
    obtain ⟨j, hj, -⟩ := LieBaseChange.existsUnique_semilinear_lifts S G R (Localization.Away (f i)) (algebraMap R (Localization.Away (f i))) x E (P →ₗ[R] Localization.Away (f i)) M Mi
    let r : E →ₗ[R] (P →ₗ[R] Localization.Away (f i)) :=
      { toFun := j
        map_add' := j.map_add
        map_smul' := fun a e => by
          rw [j.map_smulₛₗ]
          exact algebraMap_smul (Localization.Away (f i)) a (j e) }
    have e1 : (P →ₗ[R] Localization.Away (f i)) ≃ₗ[Localization.Away (f i)] Module.Dual (Localization.Away (f i)) P :=
      LinearMap.extendScalarsOfIsLocalizationEquiv (Submonoid.powers (f i)) (Localization.Away (f i))
    have hF1 : Module.Finite (Localization.Away (f i)) (P →ₗ[R] Localization.Away (f i)) := Module.Finite.equiv e1.symm
    have hF2 : Module.Projective (Localization.Away (f i)) (P →ₗ[R] Localization.Away (f i)) := Module.Projective.of_equiv e1.symm
    have hb := Lie.isBaseChange_lie x M (Localization.Away (f i)) (P →ₗ[R] Localization.Away (f i)) Mi r (fun e => by
      have := hj e
      simp only [LieModel.Lifts, Category.comp_id] at this
      exact this)
    have hy : IsLocalizedModule (Submonoid.powers (f i)) r :=
      (isLocalizedModule_iff_isBaseChange (Submonoid.powers (f i)) (Localization.Away (f i)) r).mpr hb
    exact ⟨P →ₗ[R] Localization.Away (f i), inferInstance, inferInstance, inferInstance, inferInstance, hF1, hF2, r, hy⟩
  choose F iA iR iL iT hF1 hF2 r hr using hloc
  let s : Set R := Set.range f
  have hidx : ∀ g : s, ∃ i, f i = g.1 := fun g => g.2
  choose idx hidx using hidx
  have hfp : Module.FinitePresentation R E := by
    haveI : ∀ g : s, IsLocalization.Away g.1 (Localization.Away (f (idx g))) := fun g => by
      rw [← hidx g]
      infer_instance
    haveI : ∀ g : s, IsLocalizedModule (Submonoid.powers g.1) (r (idx g)) := fun g => by
      rw [← hidx g]
      exact hr (idx g)
    exact Module.FinitePresentation.of_localizationSpan' s hspan (Rₚ := fun g => Localization.Away (f (idx g))) (Mₚ := fun g => F (idx g)) (fun g => r (idx g)) (fun g => by
      haveI := hF1 (idx g)
      haveI := hF2 (idx g)
      exact Module.finitePresentation_of_projective _ _)
  refine ⟨inferInstance, ?_⟩
  rw [← Module.freeLocus_eq_univ_iff]
  refine Set.eq_univ_of_forall fun p => ?_
  obtain ⟨i, hi⟩ : ∃ i, f i ∉ p.asIdeal := by
    by_contra h
    push_neg at h
    apply p.isPrime.ne_top
    rw [eq_top_iff, ← hspan, Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    exact h k
  have hP : Module.Projective (Localization.Away (f i)) (LocalizedModule.Away (f i) E) := by
    let eq := (IsLocalizedModule.linearEquiv (Submonoid.powers (f i)) (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) E) (r i)).extendScalarsOfIsLocalization (Submonoid.powers (f i)) (Localization.Away (f i))
    exact Module.Projective.of_equiv eq.symm
  exact (Module.basicOpen_subset_freeLocus_iff.mpr hP) ((PrimeSpectrum.mem_basicOpen _ _).mpr hi)

theorem lie_bc : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (x : Spec (CommRingCat.of R) ⟶ S) (E E' : Type) [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R' E'] (M : LieModel G x E) (M' : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) E'), ∃ j : E →+ E', (∀ e, (M'.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) ≫ (M.pt e).left) ∧ (∀ (a : R) e, j (a • e) = algebraMap R R' a • j e) ∧ (Smooth G.hom → ∀ (n : ℕ) (b : Module.Basis (Fin n) R E), LinearIndependent R' (fun k => j (b k)) ∧ Submodule.span R' (Set.range fun k => j (b k)) = ⊤) := by
  intro S G _ R R' _ _ _ x E E' _ _ _ _ M M'
  obtain ⟨j, hj, -⟩ := LieBaseChange.existsUnique_semilinear_lifts S G R R' (algebraMap R R') x E E' M M'
  refine ⟨j.toAddMonoidHom, fun e => ?_, fun a e => j.map_smulₛₗ a e, fun hsm n b => ?_⟩
  · have := hj e
    simp only [LieModel.Lifts, Category.comp_id] at this
    exact this
  · haveI : Smooth G.hom := hsm
    letI : Module R E' := Module.compHom E' (algebraMap R R')
    haveI : IsScalarTower R R' E' := ⟨fun a c v => by
      show (a • c) • v = algebraMap R R' a • c • v
      rw [Algebra.smul_def, mul_smul]⟩
    let β : E →ₗ[R] E' :=
      { toFun := j
        map_add' := j.map_add
        map_smul' := fun a e => j.map_smulₛₗ a e }
    have hb := Lie.isBaseChange_lie x M R' E' M' β (fun e => by
      have := hj e
      simp only [LieModel.Lifts, Category.comp_id] at this
      exact this)
    have hbk : ∀ k, hb.basis b k = j (b k) := fun k => by
      rw [IsBaseChange.basis_apply]
      rfl
    have hfun : (fun k => j.toAddMonoidHom (b k)) = ⇑(hb.basis b) := funext fun k => (hbk k).symm
    refine ⟨?_, ?_⟩
    · rw [hfun]
      exact (hb.basis b).linearIndependent
    · rw [hfun]
      exact (hb.basis b).span_eq

end PositivityTheory.HtPt.Htat
