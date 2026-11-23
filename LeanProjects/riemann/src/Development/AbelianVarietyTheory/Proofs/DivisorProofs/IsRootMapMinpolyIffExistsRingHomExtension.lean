import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomCompAlgebraMapEq
open Polynomial
namespace GlobalTheory

theorem exists_ringHom_extension_algClosed_of_isIntegral_injective {R S K : Type*} [CommRing R] [CommRing S] [Field K] [IsAlgClosed K]
    [Algebra R S] [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S))
    (ψ : R →+* K) : ∃ x : S →+* K, x.comp (algebraMap R S) = ψ := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq
  | exact @_root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq
  | exact _root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq
  | (apply _root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq ..)

theorem isRoot_map_minpoly_iff_exists_ringHom : ∀ (A B : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [IsDomain B] [Algebra A B] [Algebra.IsIntegral A B], Function.Injective (algebraMap A B) → ∀ (g : B) (φ : A →+* ℂ) (z : ℂ), ((minpoly A g).map φ).IsRoot z ↔ ∃ x : B →+* ℂ, x.comp (algebraMap A B) = φ ∧ x g = z := by
  intro A B _ _ _ _ _ _ _ hinj g φ z
  constructor
  · intro h
    haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
    have hg : IsIntegral A g := Algebra.IsIntegral.isIntegral g
    have h' : (minpoly A g).eval₂ φ z = 0 := by rwa [IsRoot, eval_map] at h
    let e := minpoly.equivAdjoin hg
    let ψ : Algebra.adjoin A {g} →+* ℂ := (AdjoinRoot.lift φ z h').comp (e.symm : _ →+* _)
    haveI : Algebra.IsIntegral (Algebra.adjoin A {g}) B := Algebra.IsIntegral.tower_top A
    obtain ⟨x, hx⟩ := exists_ringHom_extension_algClosed_of_isIntegral_injective (S := B) Subtype.val_injective ψ
    have hx' : ∀ r : Algebra.adjoin A {g}, x r = ψ r := fun r => RingHom.congr_fun hx r
    refine ⟨x, ?_, ?_⟩
    · ext a
      have := hx' (algebraMap A _ a)
      simp only [ψ, RingHom.comp_apply, RingHom.coe_coe, AlgEquiv.commutes, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of] at this
      exact this
    · have h1 : (e (AdjoinRoot.root _) : B) = g := by
        change ((AdjoinRoot.Minpoly.toAdjoin A g (AdjoinRoot.root _) : Algebra.adjoin A {g}) : B) = g
        simp [AdjoinRoot.Minpoly.toAdjoin]
      have := hx' (e (AdjoinRoot.root _))
      simp only [ψ, RingHom.comp_apply, RingHom.coe_coe, AlgEquiv.symm_apply_apply, AdjoinRoot.lift_root] at this
      rwa [h1] at this
  · rintro ⟨x, rfl, rfl⟩
    rw [IsRoot, eval_map, ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]

end GlobalTheory
