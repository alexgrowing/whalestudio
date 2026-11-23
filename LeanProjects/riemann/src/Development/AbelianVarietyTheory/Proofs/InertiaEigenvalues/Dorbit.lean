import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.LocalExtField

open Polynomial

theorem dorbit : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (β : Ω), ∃ S : Finset Ω, (∀ x, x ∈ S ↔ ∃ d ∈ Dec (F := E) A, d β = x) ∧ ∃ f : Polynomial Ω, f.Monic ∧ f.natDegree = S.card ∧ (∀ d ∈ Dec (F := E) A, ∀ i, d (f.coeff i) = f.coeff i) ∧ f.eval β = 0 := by
  intro E Ω _ _ _ _ _ A β
  classical
  have hint : IsIntegral E β := Algebra.IsIntegral.isIntegral β
  have hfin : {x : Ω | ∃ d ∈ Dec (F := E) A, d β = x}.Finite := by
    refine (Polynomial.rootSet_finite (minpoly E β) Ω).subset ?_
    rintro x ⟨d, -, rfl⟩
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    rw [show d β = (d : Ω →ₐ[E] Ω) β from rfl, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hS : ∀ x, x ∈ hfin.toFinset ↔ ∃ d ∈ Dec (F := E) A, d β = x := fun x => hfin.mem_toFinset
  refine ⟨hfin.toFinset, hS, ∏ x ∈ hfin.toFinset, (X - C x),
    monic_prod_of_monic _ _ (fun x _ => monic_X_sub_C x), ?_, ?_, ?_⟩
  · rw [natDegree_prod_of_monic _ _ (fun x _ => monic_X_sub_C x)]; simp
  · intro d hd i
    have hperm : hfin.toFinset.image d = hfin.toFinset := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        rw [Finset.mem_image] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        obtain ⟨d', hd', rfl⟩ := (hS y).1 hy
        exact (hS _).2 ⟨d * d', mul_mem hd hd', rfl⟩
      · rw [Finset.card_image_of_injective _ d.injective]
    have key : (∏ x ∈ hfin.toFinset, (X - C x)).map (d : Ω →+* Ω) = ∏ x ∈ hfin.toFinset, (X - C x) := by
      rw [Polynomial.map_prod]
      simp only [Polynomial.map_sub, map_X, map_C]
      conv_rhs => rw [← hperm]
      rw [Finset.prod_image (fun x _ y _ h => d.injective h)]
      rfl
    have := congrArg (fun p => p.coeff i) key
    simpa [Polynomial.coeff_map] using this
  · rw [eval_prod]
    exact Finset.prod_eq_zero ((hS β).2 ⟨1, one_mem _, rfl⟩) (by simp)

end GlobalTheory.LocalExtField
