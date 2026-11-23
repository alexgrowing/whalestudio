import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperFiniteness
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh

set_option maxSynthPendingDepth 1

noncomputable section

private theorem smulHom_eq {X : Scheme.{0}} (F : X.Modules) (r : Γ(X, ⊤)) :
    GlobalTheory.smulHom F r = GroundTheory.Arith.SchemeCoh.smulHom F r := by
  ext U x
  rfl

private def cohEquiv {X : Scheme.{0}} (R : Type) [CommRing R] [Algebra R Γ(X, ⊤)] (F : X.Modules)
    (n : ℕ) : coh F n ≃ₗ[R] Sheaf.H.{0} (GroundTheory.Arith.SchemeCoh.modulesAb F) n :=
  { (coh.toH F n) with
    map_smul' := fun r x => by
      have h := coh.toH_map R (smulHom F (algebraMap R Γ(X, ⊤) r)) n x
      rw [← cohOn.smul_eq_map] at h
      refine h.trans ?_
      rw [smulHom_eq]
      rfl }

private theorem finiteType_sec {Z : Scheme.{0}} (s : Z ⟶ Sp ℂ) [LocallyOfFiniteType s]
    {U : Z.Opens} (hU : IsAffineOpen U) : Algebra.FiniteType ℂ (CechDR.Sec s U) := by
  have h := HasRingHomProperty.appLE @LocallyOfFiniteType s inferInstance
    ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have h2 : (CechDR.secMap s U).hom.FiniteType := by
    change ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ s.appLE ⊤ U le_top).hom.FiniteType
    rw [CommRingCat.hom_comp]
    exact RingHom.FiniteType.comp h (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2)
  exact h2

private theorem isCoherent_Omega {Z : Scheme.{0}} (s : Z ⟶ Sp ℂ) [LocallyOfFiniteType s] (a : ℕ) :
    GroundTheory.Arith.SchemeCoh.IsCoherent (Omega s a) := by
  refine ⟨inferInstance, fun U hU => ?_⟩
  haveI := finiteType_sec s hU
  have h : Module.Finite (CechDR.Sec s U) (CechDR.OmU s U a) := inferInstance
  have h' : Module.Finite (CechDR.Sec s U) Γ(Omega s a, U) := Module.Finite.equiv (toOmEquiv s a hU)
  exact h'

theorem UpperTheory.finiteDimensional_hodgeCohomology_of_smooth_proj :
    ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d s], IsProjOver s → ∀ a b : ℕ, FiniteDimensional ℂ (hodgeH s a b) := by
  intro Z _ s d _ hp a b
  obtain ⟨N, i, hi, his⟩ := hp
  haveI : IsProper (PSpace.str ℂ N) :=
    inferInstanceAs (IsProper (GroundTheory.Arith.SchemeCoh.ProjSpace.toSpecBase ℂ N))
  haveI : IsProper s := by rw [← his]; infer_instance
  letI : Z.Over (Spec (.of ℂ)) := ⟨s⟩
  haveI : IsProper (Z ↘ Spec (.of ℂ)) := inferInstanceAs (IsProper s)
  have hc : GroundTheory.Arith.SchemeCoh.IsCoherent (Omega s a) := isCoherent_Omega s a
  have h := @GroundTheory.Arith.SchemeCoh.finite_H_of_isProper ℂ _ _ Z _ _ (Omega s a) hc b
  letI := algΓ s
  have h' : Module.Finite ℂ (coh (Omega s a) b) := by
    haveI : Module.Finite ℂ (Sheaf.H.{0} (GroundTheory.Arith.SchemeCoh.modulesAb (Omega s a)) b) := h
    exact Module.Finite.equiv (cohEquiv ℂ (Omega s a) b).symm
  exact h'

end
