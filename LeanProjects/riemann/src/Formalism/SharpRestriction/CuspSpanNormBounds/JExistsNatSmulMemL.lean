import Mathlib
import Formalism.LocalRingCardinality.DataSpaces

namespace Formalism.MainNotions.LatticeGluingRadicals

open NumberField
open scoped nonZeroDivisors

theorem common_int_denomL {E : Type} [Field E] [NumberField E] {k : ℕ} (f : Fin k → E) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ i, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = (m : E) * f i := by
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) E :=
    IsIntegralClosure.isLocalization ℤ ℚ E (𝓞 E)
  obtain ⟨⟨b, hb⟩, hf⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) f
  obtain ⟨m, hm, rfl⟩ := hb
  refine ⟨m, nonZeroDivisors.ne_zero hm, fun i => ?_⟩
  obtain ⟨r, hr⟩ := hf i
  refine ⟨r, ?_⟩
  rw [hr, Algebra.smul_def]
  simp

theorem j_exists_nat_smul_memL {E : Type} [Field E] [NumberField E] {V : Type}
    [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (M : Submodule (𝓞 E) V) {x : V} (hx : x ∈ Submodule.span E (M : Set V)) :
    ∃ n : ℕ, 0 < n ∧ n • x ∈ M := by
  obtain ⟨k, f, g, hsum⟩ := Submodule.mem_span_set'.mp hx
  obtain ⟨m, hm0, hr⟩ := common_int_denomL f
  choose r hr using hr
  have hmx : m • x ∈ M := by
    have hcomb : m • x = ∑ i, r i • (g i : V) := by
      rw [← hsum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← algebraMap_smul E (r i) (g i : V), hr i, mul_smul, Int.cast_smul_eq_zsmul]
    rw [hcomb]
    exact Submodule.sum_mem _ fun i _ => M.smul_mem _ (g i).2
  have key : ((m.natAbs : ℤ)) • x ∈ M := by
    rcases Int.natAbs_eq m with h | h
    · rwa [← h]
    · rw [h, neg_smul] at hmx
      exact M.neg_mem_iff.mp hmx
  refine ⟨m.natAbs, Int.natAbs_pos.mpr hm0, ?_⟩
  rwa [natCast_zsmul] at key

theorem m_exists_smul_memL {E : Type} [Field E] [NumberField E] [StarRing E]
    {S : Formalism.BasicNotions.HSpace E} (M : Submodule (𝓞 E) S.V) {x : S.V}
    (hx : x ∈ Submodule.span E (M : Set S.V)) : ∃ d : 𝓞 E, d ≠ 0 ∧ d • x ∈ M := by
  obtain ⟨n, hn, hnx⟩ := j_exists_nat_smul_memL M hx
  refine ⟨(n : 𝓞 E), Nat.cast_ne_zero.mpr hn.ne', ?_⟩
  rwa [Nat.cast_smul_eq_nsmul]

theorem c_lat_multL {E : Type} [Field E] [NumberField E] [StarRing E]
    {S : Formalism.BasicNotions.HSpace E} {Λ : Submodule (𝓞 E) S.V} (hΛ : Submodule.IsLattice E Λ)
    (v : S.V) : ∃ n : 𝓞 E, n ≠ 0 ∧ n • v ∈ Λ :=
  m_exists_smul_memL Λ (by rw [hΛ.span_eq_top]; exact Submodule.mem_top)

theorem a_exists_smul_memL {E : Type} [Field E] [NumberField E] [StarRing E]
    {S : Formalism.BasicNotions.HSpace E} (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ)
    (x : S.V) : ∃ c : 𝓞 E, c ≠ 0 ∧ c • x ∈ Λ :=
  c_lat_multL hΛ x

end Formalism.MainNotions.LatticeGluingRadicals
