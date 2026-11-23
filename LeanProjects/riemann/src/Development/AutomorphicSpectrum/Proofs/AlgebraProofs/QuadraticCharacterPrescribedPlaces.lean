import Mathlib
import GroundTheory.ArithmeticGeometry.ToricVarieties.KrullDomain

open NumberField TensorProduct

namespace GlobalTheory.CompanionTheory.HeightOneFrame

theorem integral_of_integral_at_height_one :
    ∀ (A Ω : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field Ω]
      [Algebra A Ω] [IsFractionRing A Ω] (E : Type) [AddCommGroup E] [Module Ω E] (r : ℕ)
      (b b' : Fin r → E), LinearIndependent Ω b →
      (∀ P : PrimeSpectrum A, P.asIdeal.height = 1 → ∀ i, ∃ (s : A) (c : Fin r → A),
        s ∉ P.asIdeal ∧ algebraMap A Ω s • b' i = ∑ k, algebraMap A Ω (c k) • b k) →
      (∀ i, b' i ∈ Submodule.span Ω (Set.range b)) →
      ∀ i, ∃ c : Fin r → A, b' i = ∑ k, algebraMap A Ω (c k) • b k := by
  intro A Ω _ _ _ _ _ _ _ E _ _ r b b' hb hP hspan i
  obtain ⟨x, hx⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).mp (hspan i)
  have key : ∀ k, x k ∈ Set.range (algebraMap A Ω) := by
    intro k
    refine GroundTheory.Arith.Toric.mem_range_of_forall_height_one (A := A) (K := Ω) (x k) ?_
    intro p hp h1
    obtain ⟨s, c, hs, hc⟩ := hP ⟨p, hp⟩ h1 i
    refine ⟨c k, s, hs, ?_⟩
    have h0 : ∑ j, (algebraMap A Ω s * x j - algebraMap A Ω (c j)) • b j = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum]
      rw [hx, hc, sub_self]
    have h2 := (Fintype.linearIndependent_iff.mp hb) _ h0 k
    have h3 : algebraMap A Ω s * x k = algebraMap A Ω (c k) := sub_eq_zero.mp h2
    rw [← h3, mul_comm]
  choose c hc using key
  refine ⟨c, ?_⟩
  rw [← hx]
  simp only [hc]

end GlobalTheory.CompanionTheory.HeightOneFrame
