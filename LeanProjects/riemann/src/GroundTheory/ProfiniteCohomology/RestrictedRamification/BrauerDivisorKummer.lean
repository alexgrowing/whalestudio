import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.MemMaxUnramifiedOutsideOfMemLevelOfField
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

namespace PicInf

open CategoryTheory NumberField IsDedekindDomain IntermediateField GroundTheory.Global FiniteSubfield

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} {S : Set (HeightOneSpectrum (𝓞 K.1))}

variable (L : IntermediateField K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) [FiniteDimensional K.1 L]

omit [FiniteDimensional K.1 L] in

theorem exists_mem_pow_eq_of_dvd_log_valuation (Lq : IntermediateField K.1 ℚ̄) [FiniteDimensional K.1 Lq]
    [NumberField Lq]
    (hLqle : Lq ≤ maxUnramifiedOutside K.1 ℚ̄ S) (M : ℕ) (hM : M ≠ 0)
    (hMS : ∀ v ∉ S, ((M : ℕ) : 𝓞 K.1) ∉ v.asIdeal) (π : Lqˣ)
    (hπ : ∀ W : HeightOneSpectrum (𝓞 Lq), (M : ℤ) ∣ WithZero.log (W.valuation Lq (π : Lq))) :
    ∃ α : ℚ̄, α ∈ maxUnramifiedOutside K.1 ℚ̄ S ∧ α ^ M = ((π : Lq) : ℚ̄) := by
  have hLu : IsUnramifiedOutside S Lq := (isUnramifiedOutside_iff_le_maxUnramifiedOutside S).2 hLqle
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq ((π : Lq) : ℚ̄) (Nat.pos_of_ne_zero hM)
  have hαint : IsIntegral Lq α := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hM) ?_
    rw [hα]
    exact isIntegral_algebraMap (x := (π : Lq))
  let E : IntermediateField Lq ℚ̄ := IntermediateField.adjoin Lq {α}
  have : FiniteDimensional Lq E := IntermediateField.adjoin.finiteDimensional hαint
  have : NumberField E := NumberField.of_module_finite Lq E
  have hβ : IntermediateField.AdjoinSimple.gen Lq α ^ M = algebraMap Lq E (π : Lq) := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, IntermediateField.AdjoinSimple.coe_gen, hα]
    rfl
  have hEu : IsUnramifiedOutside (placesOver S) E := by
    intro w hw
    refine Global.Kummer.isUnramifiedIn_of_pow_eq π hβ (adjoin_gen_eq_top Lq α) w ?_ (hπ w)
    intro hmem
    have hv : underPlace (F := K.1) w ∉ S := fun h => hw (mem_placesOver_iff.2 h)
    apply hMS _ hv
    change ((M : ℕ) : 𝓞 K.1) ∈ Ideal.comap (algebraMap (𝓞 K.1) (𝓞 Lq)) w.asIdeal
    rw [Ideal.mem_comap, map_natCast]
    exact hmem
  have hEF := (isUnramifiedOutside_restrictScalars_iff S hLu E).2 hEu
  have : FiniteDimensional K.1 (E.restrictScalars K.1) := FiniteDimensional.trans K.1 Lq E
  exact ⟨α, le_maxUnramifiedOutside S hEF (IntermediateField.mem_adjoin_simple_self Lq α), hα⟩

theorem exists_pow_eq_of_dvd_log_valuation (M : ℕ) (hM : M ≠ 0)
    (hMS : ∀ v ∉ S, ((M : ℕ) : 𝓞 K.1) ∉ v.asIdeal) (π : (levelOfField L).1ˣ)
    (hπ : ∀ W : HeightOneSpectrum (𝓞 (levelOfField L).1),
      (M : ℤ) ∣ WithZero.log (W.valuation (levelOfField L).1 (π : (levelOfField L).1))) :
    ∃ α : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ,
      ((α : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) ^ M = ((π : (levelOfField L).1) : ℚ̄) := by
  have hLqf : FiniteDimensional K.1 (L.map (maxUnramifiedOutside K.1 ℚ̄ S).val) :=
    LinearEquiv.finiteDimensional (L.equivMap (maxUnramifiedOutside K.1 ℚ̄ S).val).toLinearEquiv
  have hLqle : L.map (maxUnramifiedOutside K.1 ℚ̄ S).val ≤ maxUnramifiedOutside K.1 ℚ̄ S := by
    rintro z ⟨w, -, rfl⟩
    exact w.2
  have : NumberField (L.map (maxUnramifiedOutside K.1 ℚ̄ S).val) := NumberField.of_module_finite K.1 _
  obtain ⟨α, hαS, hα⟩ := exists_mem_pow_eq_of_dvd_log_valuation
    (L.map (maxUnramifiedOutside K.1 ℚ̄ S).val) hLqle M hM hMS π hπ
  have hα0 : (⟨α, hαS⟩ : maxUnramifiedOutside K.1 ℚ̄ S) ≠ 0 := by
    intro h
    have h' : α = 0 := congrArg Subtype.val h
    rw [h', zero_pow hM] at hα
    exact (π : (levelOfField L).1ˣ).ne_zero (Subtype.ext hα.symm)
  exact ⟨Units.mk0 _ hα0, hα⟩

end

end PicInf

end GroundTheory.ProfCoh
