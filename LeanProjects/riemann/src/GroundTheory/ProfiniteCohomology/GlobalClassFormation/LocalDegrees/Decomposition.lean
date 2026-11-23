import Mathlib
import GroundTheory.GlobalFields.CyclotomicCharacters.DegreeDecomposition
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalDegrees.Layers
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IntermediateField GroundTheory.Global GroundTheory.Global.Cyclotomic GroundTheory.LocalField.Abstract

open scoped GroundTheory.LocalField.Abstract Pointwise

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

namespace CyclotomicLayer

section Component

theorem exists_toZModPow_degreeComponent_ne_zero (q : Nat.Primes) (w : ℤ_[q]ˣ)
    (hw : padicUnitsLog q w ≠ 1) :
    ∃ n, ∀ σ : Gal(ℚ̄/ℚ),
      (modCharacter ((q : ℕ) ^ (n + unitsLevel q)) σ : ZMod ((q : ℕ) ^ (n + unitsLevel q))) =
        PadicInt.toZModPow (n + unitsLevel q) (w : ℤ_[q]) →
      PadicInt.toZModPow n (Multiplicative.toAdd (degreeComponent q σ)) ≠ 0 := by
  obtain ⟨n, hn⟩ : ∃ n, PadicInt.toZModPow n (Multiplicative.toAdd (padicUnitsLog q w)) ≠ 0 := by
    by_contra! hcon
    apply hw
    have h0 : Multiplicative.toAdd (padicUnitsLog q w) = 0 :=
      PadicInt.ext_of_toZModPow.mp fun n => by rw [hcon n, map_zero]
    rw [← ofAdd_toAdd (padicUnitsLog q w), h0, ofAdd_zero]
  refine ⟨n, fun σ hσ => ?_⟩
  have hred : redUnits q (n + unitsLevel q) (Units.map (toPadicInt q).toMonoidHom (character σ)) =
      redUnits q (n + unitsLevel q) w :=
    Units.ext (by rw [redUnits_character, hσ, coe_redUnits])
  rwa [degreeComponent_apply, toZModPow_padicUnitsLog, hred, ← toZModPow_padicUnitsLog]

theorem exists_unit_modCharacter (q : Nat.Primes) (p : ℕ) [hp : Fact p.Prime] :
    ∃ u : ℤ_[q]ˣ, padicUnitsLog q u ≠ 1 ∧
      ∀ (P : Ideal (𝓞 ℚ̄)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] (N : ℕ), 0 < N →
        ∃ σ ∈ MulAction.stabilizer Gal(ℚ̄/ℚ) P, modCharacter ((q : ℕ) ^ N) σ = redUnits q N u := by
  by_cases hpq : p = q
  · refine ⟨genPadicUnit q, ?_, fun P _ _ N hN => ?_⟩
    · intro h
      have := padicUnitsLog_genPadicUnit (q : ℕ)
      rw [h, toAdd_one] at this
      exact genLog_ne_zero q (Nat.cast_eq_zero.1 this.symm)
    · obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
      subst hpq
      exact exists_mem_stabilizer_modCharacter_eq_of_prime_pow P k _
  · have hcop : Nat.Coprime q p := (Nat.coprime_primes q.2 hp.out).2 (Ne.symm hpq)
    refine ⟨(isUnit_natCast_of_coprime (q : ℕ) hcop).unit, ?_, fun P _ _ N _ => ?_⟩
    · intro h
      rw [padicUnitsLog_eq_one_iff] at h
      have h2 := congrArg (fun u : ℤ_[q]ˣ => (u : ℤ_[q])) h
      simp only [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one] at h2
      rw [← Nat.cast_pow, ← Nat.cast_one, Nat.cast_inj, Nat.pow_eq_one] at h2
      rcases h2 with h2 | h2
      · exact hp.out.one_lt.ne' h2
      · exact (torsionExponent_pos q).ne' h2
    · have hM : ¬ p ∣ (q : ℕ) ^ N := fun h =>
        hpq ((Nat.prime_dvd_prime_iff_eq hp.out q.2).1 (hp.out.dvd_of_dvd_pow h))
      obtain ⟨σ, hσP, hσp⟩ := exists_mem_stabilizer_modCharacter_eq_prime P hM
      refine ⟨σ, hσP, Units.ext ?_⟩
      rw [hσp, coe_redUnits, IsUnit.unit_spec, map_natCast]

theorem exists_toZModPow_degreeComponent_pow_ne_zero (q : Nat.Primes) (p : ℕ) [Fact p.Prime]
    {c : ℕ} (hc : c ≠ 0) :
    ∃ n, ∀ (P : Ideal (𝓞 ℚ̄)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})],
      ∃ σ ∈ MulAction.stabilizer Gal(ℚ̄/ℚ) P,
        PadicInt.toZModPow n (Multiplicative.toAdd (degreeComponent q (σ ^ c))) ≠ 0 := by
  obtain ⟨u, hu, hP⟩ := exists_unit_modCharacter q p
  have hw : padicUnitsLog q (u ^ c) ≠ 1 := by
    rw [map_pow]
    intro h
    apply hu
    have h' : c • Multiplicative.toAdd (padicUnitsLog q u) = 0 := by
      rw [← toAdd_pow, h, toAdd_one]
    rw [← ofAdd_toAdd (padicUnitsLog q u), (smul_eq_zero.1 h').resolve_left hc, ofAdd_zero]
  obtain ⟨n, hn⟩ := exists_toZModPow_degreeComponent_ne_zero q (u ^ c) hw
  refine ⟨n, fun P _ _ => ?_⟩
  obtain ⟨σ, hσ, hσu⟩ := hP P (n + unitsLevel q) (by have := unitsLevel_ne_zero (q : ℕ); omega)
  refine ⟨σ, hσ, hn _ ?_⟩
  rw [map_pow, hσu, ← map_pow, coe_redUnits]

end Component

section Places

theorem exists_prime_eq_span (J : Ideal ℤ) [hJ : J.IsPrime] (h0 : J ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ J = Ideal.span {(p : ℤ)} := by
  have h := Int.ideal_span_absNorm_eq_self J
  refine ⟨Ideal.absNorm J, ?_, h.symm⟩
  have hne : ((Ideal.absNorm J : ℕ) : ℤ) ≠ 0 := by
    intro h'
    rw [h', Ideal.span_singleton_eq_bot.2 rfl] at h
    exact h0 h.symm
  rw [← h] at hJ
  exact Nat.prime_iff_prime_int.2 ((Ideal.span_singleton_prime hne).1 hJ)

theorem finiteIndex_fixingSubgroup (K : FiniteSubfield) : K.1.fixingSubgroup.FiniteIndex := by
  have : IsGalois ℚ ℚ̄ := IsAlgClosure.isGalois ℚ ℚ̄
  refine ⟨?_⟩
  rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
  exact Module.finrank_pos.ne'

theorem exists_pow_mem_fixingSubgroup (K : FiniteSubfield) :
    ∃ c ≠ 0, ∀ σ : Gal(ℚ̄/ℚ), σ ^ c ∈ K.1.fixingSubgroup := by
  have := finiteIndex_fixingSubgroup K
  have := K.1.fixingSubgroup.normalCore_normal
  exact ⟨K.1.fixingSubgroup.normalCore.index, Subgroup.FiniteIndex.index_ne_zero,
    fun σ => Subgroup.normalCore_le _ (Subgroup.pow_index_mem _ σ)⟩

variable {K : FiniteSubfield} (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K.1))

theorem exists_prime_liesOver :
    ∃ p : ℕ, p.Prime ∧ ∀ P : Ideal (𝓞 ℚ̄), P.comap (ringOfIntegersIncl K.1) = v.asIdeal →
      P.LiesOver (Ideal.span {(p : ℤ)}) := by
  have hne : v.asIdeal.comap (algebraMap ℤ (𝓞 K.1)) ≠ ⊥ := by
    have : v.asIdeal.LiesOver (v.asIdeal.under ℤ) := ⟨rfl⟩
    exact Ideal.under_ne_bot ℤ v.ne_bot
  obtain ⟨p, hp, hJ⟩ := exists_prime_eq_span _ hne
  refine ⟨p, hp, fun P hP => ⟨?_⟩⟩
  rw [← hJ, ← hP, Ideal.under, Ideal.comap_comap]
  congr 1

theorem exists_mem_stabilizer_toZModPow_degreeComponent_ne_zero (q : Nat.Primes) :
    ∃ n, ∀ P : Ideal (𝓞 ℚ̄), P.IsPrime → P.comap (ringOfIntegersIncl K.1) = v.asIdeal →
      ∃ σ ∈ MulAction.stabilizer Gal(ℚ̄/ℚ) P, σ ∈ K.1.fixingSubgroup ∧
        PadicInt.toZModPow n (Multiplicative.toAdd (degreeComponent q σ)) ≠ 0 := by
  obtain ⟨p, hp, hover⟩ := exists_prime_liesOver v
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, hc, hcK⟩ := exists_pow_mem_fixingSubgroup K
  obtain ⟨n, hn⟩ := exists_toZModPow_degreeComponent_pow_ne_zero q p hc
  refine ⟨n, fun P hPp hPv => ?_⟩
  have := hover P hPv
  obtain ⟨σ, hσP, hσ⟩ := hn P
  exact ⟨σ ^ c, Subgroup.pow_mem _ hσP c, hcK σ, hσ⟩

end Places

end CyclotomicLayer

end

end GroundTheory.ProfCoh
