import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.LiftFactorization
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.MemTwCentConj
import GroundTheory.AutomorphicForms.SmoothRepSchur

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open scoped Classical ENNReal

private theorem exists_eq_smul_id_of_irreducible {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] {n : ℕ} {X : Type} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (GL (Fin n) E) X) (hs : IsSmooth ρ) (hi : ρ.IsIrreducible)
    (φ : X →ₗ[ℂ] X) (hφ : ∀ g x, φ (ρ g x) = ρ g (φ x)) : ∃ c : ℂ, φ = c • LinearMap.id := by
  haveI : ρ.IsIrreducible := hi
  obtain ⟨c, hc⟩ := (GroundTheory.Automorphic.algebraMap_intertwiningMap_bijective_of_isSmooth
      (show GroundTheory.Automorphic.IsSmooth ρ from hs)).2
    (⟨φ, fun g => LinearMap.ext fun x => hφ g x⟩ : Representation.IntertwiningMap ρ ρ)
  exact ⟨c, LinearMap.ext fun x =>
    (congrArg (fun f : Representation.IntertwiningMap ρ ρ => f x) hc).symm⟩

set_option maxHeartbeats 400000 in
theorem UpperTheory.Gal.InertialTypesAlt.L.twScale :
    UpperTheory.Gal.InertialTypesAlt.L.TwScale := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hgen n V _ _ ρ hs hi I hI
  haveI := hi
  set m := Module.finrank k E with hm
  have hmpos : 0 < m := Module.finrank_pos
  have hiter : ∀ j : ℕ, ∀ g x, ((I : V →ₗ[ℂ] V) ^ j) (ρ g x) =
      ρ (GlobalTheory.LBC.galAct (σ ^ j) n g) (((I : V →ₗ[ℂ] V) ^ j) x) := by
    intro j
    induction j with
    | zero =>
      intro g x
      rw [pow_zero, pow_zero, GlobalTheory.LBC.galAct_one]
      rfl
    | succ j ih =>
      intro g x
      rw [pow_succ', pow_succ', GlobalTheory.LBC.galAct_mul, Module.End.mul_apply, Module.End.mul_apply, ih]
      exact hI _ _
  have hσm : σ ^ m = 1 := by
    rw [hm, ← IsGalois.card_aut_eq_finrank]
    exact pow_card_eq_one'
  obtain ⟨c, hc⟩ := exists_eq_smul_id_of_irreducible ρ hs hi ((I : V →ₗ[ℂ] V) ^ m) (by
    intro g x
    rw [hiter m g x, hσm, GlobalTheory.LBC.galAct_one]
    rfl)
  have hinj : Function.Injective ((I : V →ₗ[ℂ] V) ^ m) := by
    rw [Module.End.coe_pow]
    exact I.injective.iterate m
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := GroundTheory.Automorphic.exists_ne_zero_of_isIrreducible (ρ := ρ)
    apply hv
    apply hinj
    rw [hc, zero_smul, map_zero]
    rfl
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq c⁻¹ hmpos
  refine ⟨a, ?_, ?_, hmpos, ?_⟩
  · rintro rfl
    rw [zero_pow hmpos.ne'] at ha
    exact inv_ne_zero hc0 ha.symm
  · intro g
    ext x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, LinearEquiv.coe_coe]
    rw [hI]
  · rw [smul_pow, hc, ha, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rfl
