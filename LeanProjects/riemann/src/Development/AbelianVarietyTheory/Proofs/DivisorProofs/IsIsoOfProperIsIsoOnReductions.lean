import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseIdealSheafOfIdealComapSpecMapSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionOfProperClosedImmersionModIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeQuotientClosedImmersionIdealSheafStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafLeOfLeOnReductionsJacobsonStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem isIso_of_isIso_reductions : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (T X : Scheme.{0}) (φ : T ⟶ X) (f : X ⟶ Spec (CommRingCat.of R)), IsProper φ → IsProper f → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (c : ∀ e, (Y e).left ⟶ T), (∀ e, IsPullback (c e) (Y e).hom (φ ≫ f) (thick R I e)) → (∀ e, IsPullback (c e ≫ φ) (Y e).hom f (thick R I e)) → IsIso φ := by
  intro R _ _ I hI T X φ f hφ hf Y c hpb hpb'
  have hc := fun e => GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R (I ^ (e + 1)) T (Y e).left (φ ≫ f) (c e) (Y e).hom (hpb e)
  have hc' := fun e => GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R (I ^ (e + 1)) X (Y e).left f (c e ≫ φ) (Y e).hom (hpb' e)

  have hK : (baseIdeal f I).comap φ = (c 0).ker := by
    rw [(hc 0).2.1, (GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support).1 R X T f φ I, zero_add, pow_one]
  haveI : IsClosedImmersion (c 0) := (hc 0).1
  haveI : IsClosedImmersion (c 0 ≫ φ) := (hc' 0).1
  have hφc : IsClosedImmersion φ := by
    refine GlobalTheory.T.isClosedImmersion_of_proper_closedImmersion_mod_ideal R I hI T X φ f hφ inferInstance ?_
    rw [hK]
    have he : (c 0).ker.subschemeι ≫ φ = inv (c 0).toImage ≫ (c 0 ≫ φ) := by
      rw [IsIso.eq_inv_comp]
      exact Scheme.Hom.toImage_imageι_assoc _ _
    rw [he]
    infer_instance
  haveI := hφc

  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hker : φ.ker ≤ ⊥ := by
    refine GlobalTheory.T.idealSheaf_le_of_le_on_reductions_jacobson R I hI X f φ.ker ⊥ inferInstance fun e => ?_
    rw [bot_sup_eq, ← (hc' e).2.1]
    exact Scheme.Hom.le_ker_comp (c e) φ
  have hbot : φ.ker = ⊥ := le_bot_iff.1 hker
  haveI : IsIso φ.imageι := by
    change IsIso φ.ker.subschemeι
    rw [hbot]
    infer_instance
  rw [← φ.toImage_imageι]
  infer_instance

end GlobalTheory.FormalAlg
