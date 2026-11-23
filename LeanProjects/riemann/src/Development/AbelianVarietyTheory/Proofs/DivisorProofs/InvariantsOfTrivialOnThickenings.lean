import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeInvariantsFiniteGroupAndFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitApproximationAdicCompletionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletionGaloisInvariantsAgreeModMaxIdealPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorQuotientOntoAndInjectiveModIdealPowStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.InvAlg

theorem invariants_of_trivial_on_thickenings : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → IsGal (algebraMap R R') → ∀ (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] [Algebra.FiniteType R' C'] (act : Gal (algebraMap R R') →* (C' ≃ₐ[R] C')), (∀ σ r, act σ (algebraMap R' C' r) = algebraMap R' C' (σ.1 r)) → ∀ (O : Type) [CommRing O] [Algebra R O] [Module.Flat R O] [Algebra.FiniteType R O] (i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C')), (∀ e x y, Ideal.Quotient.mk _ y = i (e + 1) x → Ideal.Quotient.mk _ y = i e x) → (∀ e σ x y, Ideal.Quotient.mk _ y = i e x → Ideal.Quotient.mk _ (act σ y) = i e x) → (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (maximalIdeal R ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))) → ∀ C : Subalgebra R C', (∀ x, x ∈ C ↔ ∀ σ, act σ x = x) → Algebra.FiniteType R C ∧ Module.Finite C C' ∧ ∃ f : C, f - 1 ∈ (maximalIdeal R).map (algebraMap R C) ∧ (∀ x : C', ∃ n : ℕ, (f : C') ^ n * x ∈ Set.range (Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') fun _ _ => Commute.all _ _)) ∧ (∀ t : TensorProduct R C R', Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') (fun _ _ => Commute.all _ _) t = 0 → ∃ n : ℕ, ((f ^ n) ⊗ₜ[R] (1 : R')) * t = 0) ∧ ∀ e, Nonempty ((O ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R O)) ≃ₐ[R] (C ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C))) := by
  intro R _ _ _ hR R' _ _ _ _ hinj hGal C' _ _ _ _ _ act hact O _ _ _ _ i hi1 hi2 hi3 C hC
  haveI : IsNoetherianRing R := hR.1
  haveI : Finite (Gal (algebraMap R R')) := hGal.1
  haveI : Algebra.FiniteType R C' := Algebra.FiniteType.trans (S := R') inferInstance inferInstance
  obtain ⟨hft, hfin⟩ := GlobalTheory.T.finiteType_invariants_finite_group_and_finite R C' (Gal (algebraMap R R')) act C hC
  have hg := GlobalTheory.T.completion_galoisInvariants_agree_mod_maxIdeal_pow R hR R' hinj hGal C' act hact O i hi1 hi2 hi3 C hC hft hfin
  choose gm hgc using hg
  obtain ⟨hs, hinj'⟩ := GlobalTheory.T.tensor_quotient_onto_and_injective_mod_ideal_pow R (maximalIdeal R) R' C' O i hi3 C gm hgc
  haveI : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing R C
  obtain ⟨f, hf1, hf2, hf3⟩ := GlobalTheory.T.exists_unit_approximation_adic_completion C ((maximalIdeal R).map (algebraMap R C)) (TensorProduct R C R') C' _ hs hinj'
  have hL : ∀ t, Algebra.TensorProduct.lift (Algebra.ofId C C') (IsScalarTower.toAlgHom R R' C') (fun _ _ => Commute.all _ _) t = Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') (fun _ _ => Commute.all _ _) t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add a b ha hb => simp only [map_add, ha, hb]
  refine ⟨hft, hfin, f, hf1, fun x => ⟨1, ?_⟩, fun t ht => ⟨1, ?_⟩, fun e => ⟨gm e⟩⟩
  · obtain ⟨t, ht⟩ := hf2 x
    exact ⟨t, by rw [← hL]; simpa using ht⟩
  · have := hf3 t (by rw [hL]; exact ht)
    rw [pow_one]
    rwa [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at this

end GlobalTheory.InvAlg
