import Mathlib
import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Development.AutomorphicArithmetic.OrbitLabellings.GalEArithFrobEqIotaHP
import Development.AutomorphicArithmetic.FrobeniusLocalisation.FrobHOrder

open UpperTheory.HF

open scoped BigOperators
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Classical

theorem UpperTheory.two_pow_dvd_sub_or_add_one_of_odd_addOrderOf_hP :
    ∀ (D : D7) (p : ℕ), p.Prime → IsResidueClassZero D p → Odd (addOrderOf (hP D p)) →
    ((2 ^ (D.R.e + 2) : ℤ) ∣ (p : ℤ) - 1 ∨ (2 ^ (D.R.e + 2) : ℤ) ∣ (p : ℤ) + 1) ∧ 2 ^ (D.R.e + 2) ≤ p + 1 := by
  intro D p hp hc ho
  have hcl : primeClass D.host.toHostRaw p = PrimeClass.inertClass := hc
  obtain ⟨hN, -, -⟩ := (primeClass_eq_inert_iff_symbols hp).1 hcl
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)
  obtain ⟨⟨P, hP1, hP2⟩⟩ := (Ideal.span {(p : ℤ)}).nonempty_primesOver (S := 𝓞 D.host.E)
  obtain ⟨σ, hσ⟩ : ∃ σ, D.host.galE σ = D.host.toHostAx.frobG p :=
    ⟨D.host.gal.symm _, D.host.gal.apply_symm_apply _⟩
  have hfr : IsArithFrobAt ℤ σ P :=
    ((UpperTheory.HF.frobG_spec _ D.host.toHostAx p hN).1 P σ).2 hσ
  have hord := (UpperTheory.galE_arithFrob_eq_iota_hP D p hp hc P σ hfr).2
  rw [hσ] at hord
  have h1 : D.R.toFrame.hH (D.host.toHostAx.frobG p).2 = 1 := by
    by_contra hne
    have he := D.R.toFrame.even_orderOf_of_hH_ne_one hne
    rw [hord] at he
    exact Nat.not_even_iff_odd.2 ho he
  obtain ⟨-, -, h3, h4⟩ := UpperTheory.HF.frob_h_order _ D.host.toHostAx p hp hN
  refine ⟨?_, ?_⟩
  · rcases h4.1 h1 with h | h
    · left
      have : (((p : ℤ) - 1 : ℤ) : ZMod (2 ^ (D.R.e + 2))) = 0 := by
        push_cast; exact sub_eq_zero.2 h
      exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
    · right
      have : (((p : ℤ) + 1 : ℤ) : ZMod (2 ^ (D.R.e + 2))) = 0 := by
        push_cast; exact add_eq_zero_iff_eq_neg.2 h
      exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
  · rw [h1, orderOf_one, mul_one] at h3
    exact h3
