import Formalism.LocalToGlobal.CharacterGerms.RowTiePHaDefs

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.HaP

open MvPolynomial Formalism.L2.Pj

theorem satRetr : SatRetrSt := by
  intro ι _ W hW
  haveI : NoZeroSMulDivisors ℤ ((ι → ℤ) ⧸ W) := by
    refine ⟨fun {z x} h => ?_⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective W x
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
    by_cases hz : z = 0
    · exact Or.inl hz
    · right
      rw [Submodule.Quotient.mk_eq_zero]
      exact hW z x hz h
  haveI : Module.Free ℤ ((ι → ℤ) ⧸ W) := Module.free_of_finite_type_torsion_free'
  obtain ⟨s, hs⟩ := Module.projective_lifting_property W.mkQ LinearMap.id (Submodule.mkQ_surjective W)
  have hs' : ∀ y, W.mkQ (s y) = y := fun y => by rw [← LinearMap.comp_apply, hs, LinearMap.id_apply]
  refine ⟨(LinearMap.id - s ∘ₗ W.mkQ : (ι → ℤ) →ₗ[ℤ] (ι → ℤ)), fun x => ?_, fun x hx => ?_⟩
  · have h1 : W.mkQ ((LinearMap.id - s ∘ₗ W.mkQ : (ι → ℤ) →ₗ[ℤ] (ι → ℤ)) x) = 0 := by
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, hs', sub_self]
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
  · have h0 : W.mkQ x = 0 := by rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hx
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h0, map_zero, sub_zero]

theorem rowInvUp : RowInvUpSt := by
  unfold RowInvUpSt RowInv
  intro Ty r n K _ _ P hP σ i i' hii t
  classical
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : MvPolynomial (Letter Ty r n) K →ₐ[K] Polynomial (MvPolynomial (Letter Ty r n) K),
      ∀ ℓ : Letter Ty r n, Φ (X ℓ) = if ∃ b, ℓ = ⟨σ, (i, b)⟩ then
        Polynomial.C (X ℓ) + Polynomial.X * Polynomial.C (X ⟨σ, (i', ℓ.snd.2)⟩) else Polynomial.C (X ℓ) :=
    ⟨aeval _, fun ℓ => aeval_X _ _⟩
  have key : ∀ (s : K) (Q : MvPolynomial (Letter Ty r n) K),
      rowShift r n K σ i i' s Q = Polynomial.eval (C s) (Φ Q) := by
    intro s Q
    induction Q using MvPolynomial.induction_on with
    | C a =>
      have h1 := (rowShift r n K σ i i' s).commutes a
      have h2 := Φ.commutes a
      rw [MvPolynomial.algebraMap_eq] at h1 h2
      rw [h1, h2, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq, Polynomial.eval_C]
    | add p q hp hq =>
      rw [map_add, map_add, Polynomial.eval_add, hp, hq]
    | mul_X p ℓ hp =>
      rw [map_mul, map_mul, Polynomial.eval_mul, hp, hΦ]
      congr 1
      have hx : rowShift r n K σ i i' s (X ℓ) = (aeval (R := K) fun ℓ : Letter Ty r n =>
          if ∃ b, ℓ = ⟨σ, (i, b)⟩ then (X ℓ + C s * X ⟨σ, (i', ℓ.snd.2)⟩ : MvPolynomial (Letter Ty r n) K)
          else (X ℓ : MvPolynomial (Letter Ty r n) K)) (X ℓ) := by
        unfold rowShift
        rfl
      rw [hx, aeval_X]
      split_ifs <;> simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] <;> ring
  have hQ : Φ P - Polynomial.C P = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono (s := Set.range (fun q : ℚ => (C (q : K) : MvPolynomial (Letter Ty r n) K)))
    · rintro _ ⟨q, rfl⟩
      simp only [Set.mem_setOf_eq, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_C]
      rw [← key, hP σ i i' hii q, sub_self]
    · exact Set.infinite_range_of_injective fun a b h => Rat.cast_injective (MvPolynomial.C_injective _ _ h)
  rw [key t]
  have h := congrArg (Polynomial.eval (C t)) hQ
  rw [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_zero] at h
  exact sub_eq_zero.mp h

end Formalism.L2.FormalSeriesBounds.HaP
