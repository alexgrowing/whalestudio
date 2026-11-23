import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
open Matrix NumberField IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.LocIntPrincipal

variable (L : Type) [Field L] [NumberField L] (v : HeightOneSpectrum ℤ)

abbrev locS : Submonoid (𝓞 L) := Algebra.algebraMapSubmonoid (𝓞 L) v.asIdeal.primeCompl

theorem locS_le : locS L v ≤ nonZeroDivisors (𝓞 L) :=
  algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _ v.asIdeal.primeCompl_le_nonZeroDivisors

abbrev locR : Subalgebra (𝓞 L) L := Localization.subalgebra.ofField L (locS L v) (locS_le L v)

instance : IsDedekindDomain (locR L v) :=
  IsLocalization.isDedekindDomain (𝓞 L) (locS_le L v) _

instance : IsPrincipalIdealRing (locR L v) :=
  IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 L) v.asIdeal v.ne_bot

theorem intCast_ne_zero {s : ℤ} (hs : s ∉ v.asIdeal) : (s : L) ≠ 0 := by
  intro h
  apply hs
  rw [show s = 0 by exact_mod_cast h]
  exact zero_mem _

theorem mem_locR_iff (c : L) :
    c ∈ locR L v ↔ ∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * c) := by
  constructor
  · rintro ⟨a, _, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨t, ht, ?_⟩
    have h0 := intCast_ne_zero L v ht
    have e : algebraMap (𝓞 L) L (algebraMap ℤ (𝓞 L) t) = (t : L) := by simp
    rw [e, mul_comm, mul_assoc, inv_mul_cancel₀ h0, mul_one]
    exact RingOfIntegers.isIntegral_coe a
  · rintro ⟨s, hs, hi⟩
    have h0 := intCast_ne_zero L v hs
    refine ⟨⟨(s : L) * c, hi⟩, algebraMap ℤ (𝓞 L) s, ⟨s, hs, rfl⟩, ?_⟩
    have e : algebraMap (𝓞 L) L (algebraMap ℤ (𝓞 L) s) = (s : L) := by simp
    rw [e]
    change c = (s : L) * c * (s : L)⁻¹
    field_simp

end GlobalTheory.LocIntPrincipal

open GlobalTheory.LocIntPrincipal in

theorem GlobalTheory.LocIntPrincipal.exists_generator : ∀ (L : Type) [Field L] [NumberField L] (v : HeightOneSpectrum ℤ) (K : Set L), 0 ∈ K →
    (∀ a ∈ K, ∀ b ∈ K, a + b ∈ K) →
    (∀ c : L, (∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * c)) → ∀ a ∈ K, c * a ∈ K) →
    (∀ a ∈ K, ∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * a)) →
    ∃ g ∈ K, ∀ a ∈ K, ∃ c : L, (∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * c)) ∧ a = c * g := by
  intro L _ _ v K h0 hadd hmul hint
  let J : Ideal (locR L v) :=
    { carrier := {a | (a : L) ∈ K}
      zero_mem' := h0
      add_mem' := fun {a b} ha hb => hadd _ ha _ hb
      smul_mem' := fun c a ha => by
        change (c : L) * (a : L) ∈ K
        exact hmul _ ((mem_locR_iff L v c).1 c.2) _ ha }
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal J).principal
  have hgJ : g ∈ J := by rw [hg]; exact Submodule.mem_span_singleton_self g
  refine ⟨g, hgJ, fun a ha => ?_⟩
  have haR : a ∈ locR L v := (mem_locR_iff L v a).2 (hint a ha)
  have hJ : (⟨a, haR⟩ : locR L v) ∈ J := ha
  rw [hg, Submodule.mem_span_singleton] at hJ
  obtain ⟨c, hc⟩ := hJ
  refine ⟨c, (mem_locR_iff L v c).1 c.2, ?_⟩
  have := congrArg Subtype.val hc
  exact this.symm
