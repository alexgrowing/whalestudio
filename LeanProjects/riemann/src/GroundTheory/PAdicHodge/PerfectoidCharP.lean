import Mathlib
import GroundTheory.PAdicHodge.PerfectoidField
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace IsPerfectoidField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

theorem charZero_or_charP (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p] :
    CharZero K ∨ CharP K p := by
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hq | hq
  · right
    have hq' : Fact (ringChar K).Prime := ⟨hq⟩
    by_contra hne
    have hpq : p ≠ ringChar K := fun h => hne (h ▸ ringChar.charP K)

    have hpz : ((p : ZMod (ringChar K))) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      exact hpq ((Nat.prime_dvd_prime_iff_eq hq (Fact.out : p.Prime)).1 hdvd).symm
    have hferm := ZMod.pow_card_sub_one_eq_one hpz
    have hK : (p : K) ^ (ringChar K - 1) = 1 := by
      have := congrArg (ZMod.castHom (dvd_refl (ringChar K)) K) hferm
      simpa using this
    have hn := congrArg norm hK
    rw [norm_pow, norm_one] at hn
    have hlt := IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p)
    have hpos : ringChar K - 1 ≠ 0 := by have := hq.two_le; omega
    have : ‖(p : K)‖ = 1 :=
      (pow_eq_one_iff_of_nonneg (norm_nonneg _) hpos).1 hn
    linarith
  · left
    have : CharP K 0 := by rw [← hq]; exact ringChar.charP K
    exact CharP.charP_to_charZero K

theorem of_finiteDimensional_of_charP (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p] [CharP K p]
    (L : Type*) [NontriviallyNormedField L] [IsUltrametricDist L] [NormedAlgebra K L]
    [FiniteDimensional K L] : IsPerfectoidField L p := by
  have := IsPerfectoidField.completeSpace (K := K) p
  have : CompleteSpace L := FiniteDimensional.complete K L
  have : PerfectRing K p := IsPerfectoidField.perfectRing p
  have : PerfectField K := PerfectRing.toPerfectField K p
  have : PerfectField L := Algebra.IsAlgebraic.perfectField (K := K)
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have : PerfectRing L p := PerfectField.toPerfectRing p
  refine IsPerfectoidField.of_perfectRing p fun r hr => ?_
  obtain ⟨x, hx1, hx2⟩ := IsPerfectoidField.exists_norm_mem_Ioo (K := K) (p := p) r hr
  exact ⟨algebraMap K L x, by rwa [norm_algebraMap'], by rwa [norm_algebraMap']⟩

end IsPerfectoidField

end GroundTheory.PAdicHodge
