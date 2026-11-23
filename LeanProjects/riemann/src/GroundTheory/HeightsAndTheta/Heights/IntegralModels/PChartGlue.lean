import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.ChartGlueFrameP
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open ReciprocityTheory.ChartRestriction.G.Geo

theorem glueLat_frame {Ω : Type} [Field Ω] [CharZero Ω] {τ : Type} {x : τ → Ω} {r : ℕ}
    {E : Type} [AddCommGroup E] [Module Ω E] {S : Finset Nat.Primes}
    {o₀ : Type} [CommRing o₀] [Algebra ℤ o₀] [IsLocalization.Away (primeProd S) o₀] [Algebra o₀ Ω]
    {o : S → Type} [∀ p, CommRing (o p)] [∀ p, Algebra ℤ (o p)]
    [∀ p : S, IsLocalization.AtPrime (o p) (Ideal.span {(((p : Nat.Primes) : ℕ) : ℤ)})]
    [∀ p, Algebra (o p) Ω] {B₀ : ChartBundle o₀ x r E} {Bp : ∀ p, ChartBundle (o p) x r E}
    {i : τ} (hi : x i ≠ 0) (hSR : ∀ p, SameRationalSpan (B₀.lat i) ((Bp p).lat i)) :
    ∃ (k : ℕ) (f c : Fin k → Ω), (∀ l, f l ∈ chartRing ℤ x i) ∧ (∀ l, c l ∈ chartRing ℤ x i) ∧
      ∑ l, c l * f l = 1 ∧ ∀ l, IsFrameAt (chartRing ℤ x i) r (glueLat B₀ Bp i) (f l) := by
  refine exists_frame_cover _ r _ fun Q hQ => ?_
  by_cases hmQ : ((primeProd S : ℤ) : chartRing ℤ x i) ∈ Q
  · rw [primeProd, Int.cast_prod] at hmQ
    obtain ⟨p, hp, hpQ⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hQ.isPrime)).1 hmQ
    exact frame_at_prime hi hSR Q hQ.isPrime ⟨p, hp⟩ hpQ
  · exact frame_away hi hSR Q hQ.isPrime hmQ

theorem ChartGlue.proof : ChartGlue.Statement := by
  intro Ω _ _ τ _ x r E _ _ S o₀ _ _ _ _ o _ _ _ _ B₀ Bp hSR
  refine ⟨{ lat := glueLat B₀ Bp
            stable := glueLat_stable
            frame := fun i hi => glueLat_frame hi fun p => hSR p i hi
            overlap := glueLat_overlap }, fun i hi => ⟨mem_B₀_iff fun p => hSR p i hi,
              fun p v => mem_Bp_iff (fun p => hSR p i hi) p v⟩⟩

end GroundTheory.Heights₂.Heights.Model
