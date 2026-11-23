import Mathlib
import Formalism.PeriodIntegrals.LocBasisSemi
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemilocalBasis.SmulMemOfMemSpan

open NumberField

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocBasisSemi

theorem isPID (K : Type) [Field K] [NumberField K] (p : ℕ) [hp : Fact p.Prime] :
    IsPrincipalIdealRing (A K p) := by
  have : IsDedekindDomain (A K p) := IsLocalization.isDedekindDomain (𝓞 K) (T_le K p) (A K p)
  have : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp.out)
  have hP0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.out.ne_zero
  exact IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 K)
    (Ideal.span {(p : ℤ)}) hP0

theorem main : PI.LocBasisSemi := by
  intro K _ _ V _ _ _ _ p hp Y hY
  have : Fact p.Prime := ⟨hp⟩
  have := isPID K p
  set Y' : Submodule (A K p) V := Submodule.span (A K p) (Y : Set V) with hY'
  have : Module.Finite (A K p) Y' := by
    obtain ⟨S, hS⟩ := hY
    rw [Module.Finite.iff_fg]
    refine ⟨S, ?_⟩
    rw [hY', ← hS, Submodule.span_span_of_tower]
  have : Module.IsTorsionFree (A K p) Y' := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun a m h => ?_
    have hV : (a : K) • (m : V) = 0 := congrArg Subtype.val h
    rcases smul_eq_zero.mp hV with h0 | h0
    · exact Or.inl (Subtype.ext h0)
    · exact Or.inr (Subtype.ext h0)
  obtain ⟨r, B⟩ := Module.basisOfFiniteTypeTorsionFree' (R := A K p) (M := Y')
  refine ⟨r, fun i => (B i : V), ?_, fun i => smul_mem_of_mem_span Y (B i).2, ?_⟩
  · have h1 : LinearIndependent (A K p) (fun i => (B i : V)) :=
      B.linearIndependent.map' Y'.subtype Y'.ker_subtype
    exact (LinearIndependent.iff_fractionRing (A K p) K).mp h1
  · intro y hy
    have hy' : y ∈ Y' := Submodule.subset_span hy
    obtain ⟨s, hs, x, hx⟩ := common_denom (fun i => B.repr ⟨y, hy'⟩ i)
    refine ⟨s, hs, x, ?_⟩
    have hsum : (∑ i, B.repr ⟨y, hy'⟩ i • (B i : V)) = y := by
      have := congrArg Subtype.val (B.sum_repr ⟨y, hy'⟩)
      rw [Submodule.coe_sum] at this
      exact this
    conv_lhs => rw [← hsum]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Subalgebra.smul_def, smul_smul, hx i]

end PI.UnitaryGroupMassFormula.LocBasisSemi
