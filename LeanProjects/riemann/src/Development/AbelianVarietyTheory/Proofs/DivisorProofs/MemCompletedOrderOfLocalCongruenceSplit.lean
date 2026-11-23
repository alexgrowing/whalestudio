import Mathlib
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValIotaLeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingClassGroupOfConductorNeZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitsInCMFieldTwoPrimesDegreeOne

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.Euler.HatLoc

variable {E : Type} [Field E] [NumberField E]

theorem finMult {R : Type} [CommRing R] [IsDedekindDomain R] {c : Ideal R} (hc : c ≠ ⊥) (v : HeightOneSpectrum R) :
    FiniteMultiplicity v.asIdeal c :=
  FiniteMultiplicity.of_prime_left v.prime hc

omit [NumberField E] in
theorem expIn_eq_zero {c : Ideal (OF E)} {v : HeightOneSpectrum (OF E)} (h : ¬ v.asIdeal ∣ c) : expIn c v = 0 :=
  multiplicity_eq_zero.2 h

theorem exists_global {c : Ideal (OF E)} (hc : c ≠ ⊥) {z : Af E} (hz : ∀ v, LocIn (expIn c v) v z) :
    ∃ a : OF E, ∀ P : HeightOneSpectrum (𝓞 E),
      Valued.v (z P - iota a P) ≤ WithZero.exp (-(expIn c (P.under (OF E)) : ℤ)) := by
  classical
  choose b hb using hz
  have hfin := Ideal.finite_factors (R := OF E) hc
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := hfin.toFinset) (fun v => v.asIdeal) (expIn c)
    (fun v _ => v.prime) (fun v _ w _ h h' => h (HeightOneSpectrum.ext h')) (fun v => b v)
  refine ⟨a, fun P => ?_⟩
  have h1 : a - b (P.under (OF E)) ∈ (P.under (OF E)).asIdeal ^ expIn c (P.under (OF E)) := by
    by_cases h : (P.under (OF E)).asIdeal ∣ c
    · exact ha _ (hfin.mem_toFinset.2 h)
    · simp [expIn_eq_zero h]
  have h2 := val_iota_le_of_mem (over_under P) _ h1
  have h3 : z P - iota a P = (z P - iota (b (P.under (OF E))) P) - iota (a - b (P.under (OF E))) P := by
    rw [iota_sub, sub_coord]; ring
  rw [h3]
  exact Valuation.map_sub_le _ (hb _ P (over_under P)) h2

theorem multiplicity_map_le [IsCMField E] {c : Ideal (OF E)} (hc : c ≠ ⊥)
    (hs : ∀ v : HeightOneSpectrum (OF E), v.asIdeal ∣ c → Splits v) (P : HeightOneSpectrum (𝓞 E)) :
    multiplicity P.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) ≤ expIn c (P.under (OF E)) := by
  set k := multiplicity P.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) with hk
  have h1 : Ideal.map (algebraMap (OF E) (𝓞 E)) c ≤ P.asIdeal ^ k := Ideal.le_of_dvd (pow_multiplicity_dvd _ _)
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  have h2 : (P.under (OF E)).asIdeal ∣ c :=
    Ideal.dvd_iff_le.2 (Ideal.map_le_iff_le_comap.1 (h1.trans (Ideal.pow_le_self hpos.ne')))
  refine (finMult hc _).le_multiplicity_of_pow_dvd (Ideal.dvd_iff_le.2 fun a ha => ?_)
  exact (((GlobalTheory.CMVal.Euler.SplitPlace.split_place E _ (hs _ h2)).2 P (over_under P)).2.1 a k).1 (h1 (Ideal.mem_map_of_mem _ ha))

theorem mem_hatO_of_locIn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ →
    (∀ v : HeightOneSpectrum (OF E), v.asIdeal ∣ c → Splits v) → ∀ z : Af E, (∀ v, LocIn (expIn c v) v z) →
      z ∈ hatO c := by
  intro E _ _ _ c hc hs z hz
  obtain ⟨a, ha⟩ := exists_global hc hz
  have hN : 0 < Ideal.absNorm c := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  obtain ⟨x, y, hy, hxy⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat E _ hN).2 z
    (fun P => (hz _).val_le (over_under P))
  have hny : Ideal.absNorm c • y = iota ((Ideal.absNorm c : ℕ) : OF E) * y := by
    rw [nsmul_eq_mul, iota, map_natCast, map_natCast]
  rw [hny] at hxy
  have hc' : Ideal.map (algebraMap (OF E) (𝓞 E)) c ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hc
  have hx : x - algebraMap (OF E) (𝓞 E) a ∈ Ideal.map (algebraMap (OF E) (𝓞 E)) c := by
    rw [← Ideal.iInf_maxPowDividing_eq hc', Ideal.mem_iInf]
    intro P
    rw [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity hc']
    refine Ideal.pow_le_pow_right (multiplicity_map_le hc hs P) ?_
    rw [← P.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := E),
      ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← FiniteAdeleRing.algebraMap_apply]
    have h1 : algebraMap E (Af E) (algebraMap (𝓞 E) E (x - algebraMap (OF E) (𝓞 E) a)) =
        (z - iota a) - iota ((Ideal.absNorm c : ℕ) : OF E) * y := by
      rw [map_sub, map_sub, hxy]
      change algebraMap E (Af E) (x : E) - iota a = _
      ring
    rw [h1, sub_coord, sub_coord, mul_coord]
    refine Valuation.map_sub_le _ (ha P) ?_
    rw [map_mul]
    exact (mul_le_mul' (val_iota_le_of_mem (over_under P) _
      (Ideal.le_of_dvd (pow_multiplicity_dvd _ _) (Ideal.absNorm_mem c))) (hy P)).trans_eq (mul_one _)
  rw [hxy]
  refine add_mem (algebraMap_mem_hatO (mem_orderC.2 ⟨a, _, hx, ?_⟩)) (PicFin.mul_mem_hatO (Ideal.absNorm_mem c) hy)
  rw [map_sub]
  change (x : E) = algebraMap (OF E) E a + ((x : E) - algebraMap (OF E) E a)
  ring

end GlobalTheory.CMVal.Euler.HatLoc
