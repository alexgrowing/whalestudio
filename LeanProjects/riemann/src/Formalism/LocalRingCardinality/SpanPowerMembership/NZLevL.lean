import Formalism.LocalRingCardinality.SpanPowerMembership.NZLevK
import Formalism.SharpRestriction.InertJacobiLevels.ExtraGatC

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LevelValuationRings Formalism.MainNotions.G Formalism.FrobeniusOrbits NumberField Formalism.MainNotions.Inhab

theorem charZero_of_setting {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} (h : HidaSetting p n' W Qq O Kf ι σ j w) : CharZero Kf := by
  haveI := h.frac_alt
  have hW : CharZero W := by
    rcases CharP.char_is_prime_or_zero W (ringChar W) with hl | hl
    · exfalso
      have hz : ((ringChar W : ℕ) : W) = 0 := CharP.cast_eq_zero W _
      by_cases he : ringChar W = p
      · rw [he] at hz; exact h.p_unif.ne_zero hz
      · have hc : IsCoprime ((ringChar W : ℕ) : ℤ) ((p : ℕ) : ℤ) :=
          Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hl h.prime).mpr he)
        have hc' := hc.map (Int.castRingHom W)
        simp only [map_natCast, hz] at hc'
        exact h.p_unif.not_isUnit (isCoprime_zero_left.mp hc')
    · haveI : CharP W 0 := by rw [← hl]; exact ringChar.charP W
      exact CharP.charP_to_charZero W
  have hQ : CharZero Qq := (RingHom.charZero_iff (IsFractionRing.injective W Qq)).mp hW
  exact (RingHom.charZero_iff ι.injective).mp hQ

end Formalism.BasicNotions.Examples₂.NZ
