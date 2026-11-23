import Mathlib
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValIotaLeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitsInCMFieldTwoPrimesDegreeOne

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.Euler.SplitPair

variable {E : Type} [Field E] [NumberField E]

theorem eq_exp_of_le {x : WithZero (Multiplicative ℤ)} {m : ℤ} (h : x ≤ WithZero.exp m) (h' : ¬ x ≤ WithZero.exp (m - 1)) :
    x = WithZero.exp m := by
  refine le_antisymm h (not_lt.1 fun h1 => h' ?_)
  rw [← WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero, ← WithZero.exp_add, sub_add_cancel]
  exact h1

theorem exists_int_cong (P : HeightOneSpectrum (𝓞 E)) (z : P.adicCompletion E) (hz : Valued.v z ≤ 1) :
    ∃ b : 𝓞 E, Valued.v (algebraMap E (Af E) (algebraMap (𝓞 E) E b) P - z) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap E P).mem_nhds (OrderUnits.ball_mem_nhds P 1 z)
  have hk' : Valued.v (algebraMap E (P.adicCompletion E) k - z) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := hk
  have hval : ∀ x : E, Valued.v (algebraMap E (P.adicCompletion E) x) = P.valuation E x := fun x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P x
  have h1 : P.valuation E k ≤ 1 := by
    have h2 : WithZero.exp (-((1 : ℕ) : ℤ)) ≤ 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
    have := Valuation.map_add_le _ (hk'.trans h2) hz
    rwa [sub_add_cancel, hval] at this
  obtain ⟨b, hb⟩ := P.exists_valuation_sub_lt_of_integer h1 (Units.mk0 (WithZero.exp (-((1 : ℕ) : ℤ))) WithZero.exp_ne_zero)
  refine ⟨b, ?_⟩
  rw [← hval, map_sub] at hb
  have := Valuation.map_add_le _ hb.le hk'
  rw [sub_add_sub_cancel] at this
  exact this

def unitF (a : OF E) (ha : a ≠ 0) : (maximalRealSubfield E)ˣ :=
  Units.mk0 (a : maximalRealSubfield E) (fun h => ha (RingOfIntegers.ext h))

def locF (P : HeightOneSpectrum (𝓞 E)) (a : OF E) (ha : a ≠ 0) : (P.adicCompletion E)ˣ :=
  Formalism.L2.Host.atFin P (Formalism.L2.Host.upF (maximalRealSubfield E) (unitF a ha))

theorem coe_locF (P : HeightOneSpectrum (𝓞 E)) (a : OF E) (ha : a ≠ 0) : (locF P a ha : P.adicCompletion E) = iota a P := rfl

theorem loc_mul_loc {χ : HChar E} (hF : TrivOnF χ) {v : HeightOneSpectrum (OF E)} {P P' : HeightOneSpectrum (𝓞 E)}
    (hP : Over P v) (hP' : Over P' v) (hne : P ≠ P') (h2 : ∀ R, Over R v → R = P ∨ R = P') (a : OF E) (ha : a ≠ 0) :
    χ.loc P (locF P a ha) * χ.loc P' (locF P' a ha) = 1 := by
  classical
  have hS : Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v = {P, P'} := by
    ext R
    rw [mem_aboveF, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨h2 R, ?_⟩
    rintro (rfl | rfl)
    · exact hP
    · exact hP'
  have h := hF.1 v (unitF a ha)
  unfold Formalism.L2.Host.HChar.resFin at h
  rw [MonoidHom.finsetProd_apply, hS, Finset.prod_pair hne] at h
  exact h

theorem unrAt_and_val : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar E) (v : HeightOneSpectrum (OF E))
    (P P' : HeightOneSpectrum (𝓞 E)), TrivOnF χ → Splits v → Over P v → Over P' v → P ≠ P' → LevelLe χ P' 1 → UnrAt χ P →
    UnrAt χ P' ∧ val χ P' = (val χ P)⁻¹ := by
  intro E _ _ _ χ v P P' hF hs hP hP' hne hlev hun
  obtain ⟨h2, hef⟩ := GlobalTheory.CMVal.Euler.SplitPlace.split_place E v hs
  have hmul := loc_mul_loc hF hP hP' hne (h2 P P' hP hP' hne)
  have hval : ∀ R, Over R v → ∀ (n : ℕ) (a : OF E), a ∈ v.asIdeal ^ n → a ∉ v.asIdeal ^ (n + 1) →
      Valued.v (iota a R) = WithZero.exp (-(n : ℤ)) := fun R hR n a h h' => by
    refine eq_exp_of_le (val_iota_le_of_mem hR n h) fun h3 => h' ?_
    rw [← (hef R hR).2.1, ← val_iota_le_iff]
    convert h3 using 2
    push_cast; ring
  have hun' : UnrAt χ P' := by
    intro u hu
    have hu1 : Valued.v (u : P'.adicCompletion E) = 1 := hu
    obtain ⟨b, hb⟩ := exists_int_cong P' u hu1.le
    obtain ⟨a, ha⟩ := (hef P' hP').2.2 b
    have h3 := OrderUnits.val_int_le P' 1 _ (by simpa using ha)
    have h4 : Valued.v (iota a P' - u) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
      rw [map_sub (algebraMap (𝓞 E) E), map_sub (algebraMap E (Af E)), sub_coord] at h3
      have := Valuation.map_sub_le _ hb h3
      rw [sub_sub_sub_cancel_left] at this
      exact this
    have hlt : WithZero.exp (-((1 : ℕ) : ℤ)) < 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    have h5 : Valued.v (iota a P') = 1 := by
      rw [Valuation.map_eq_of_sub_lt _ (hu1 ▸ h4.trans_lt hlt), hu1]
    have hav : a ∉ v.asIdeal ^ (0 + 1) := fun h => (h5 ▸ val_iota_le_of_mem hP' 1 h).not_gt hlt
    have ha0 : a ≠ 0 := fun h => hav (h ▸ zero_mem _)
    have h6 : χ.loc P (locF P a ha0) = 1 := hun _ (by
      show Valued.v (iota a P) = 1
      simpa using hval P hP 0 a (by simp) hav)
    have h7 := hmul a ha0
    rw [h6, one_mul] at h7
    have h8 : χ.loc P' (locF P' a ha0 / u) = 1 := by
      refine hlev _ ?_ ?_
      · show Valued.v ((locF P' a ha0 / u : (P'.adicCompletion E)ˣ) : P'.adicCompletion E) = 1
        rw [Units.val_div_eq_div_val, map_div₀, coe_locF, h5, hu1, div_one]
      · rw [Units.val_div_eq_div_val, div_sub_one u.ne_zero, map_div₀, hu1, div_one, coe_locF]
        exact h4
    rw [map_div, div_eq_one, h7] at h8
    exact h8.symm
  refine ⟨hun', ?_⟩
  obtain ⟨a, ha, ha'⟩ := Ideal.exists_mem_pow_notMem_pow_succ v.asIdeal v.ne_bot v.isPrime.ne_top 1
  have ha0 : a ≠ 0 := fun h => ha' (h ▸ zero_mem _)
  have h7 := hmul a ha0
  have hunif : ∀ R, Over R v → Formalism.L2.Host.IsUnifAt R (locF R a ha0) := fun R hR => by
    show Valued.v (iota a R) = WithZero.exp (-1 : ℤ)
    simpa using hval R hR 1 a ha ha'
  rw [χ.val_eq hun _ (hunif P hP), χ.val_eq hun' _ (hunif P' hP')] at h7
  exact eq_inv_of_mul_eq_one_right h7

end GlobalTheory.CMVal.Euler.SplitPair
