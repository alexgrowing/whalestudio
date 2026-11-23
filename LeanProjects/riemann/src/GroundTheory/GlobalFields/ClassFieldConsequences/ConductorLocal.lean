import Mathlib
import GroundTheory.GlobalFields.ClassFieldConsequences.RayClassField
import GroundTheory.GlobalFields.IdeleGroups.LocalConditionIndex
import GroundTheory.GlobalFields.TateThesis.LocalConductor
import GroundTheory.GlobalFields.TateThesis.ConductorIdeal

namespace GroundTheory.Global

open IsDedekindDomain NumberField IdeleGroup SemiLocal WithZero Function Topology Filter

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

namespace Modulus

omit [NumberField K] in

theorem ext' {𝔪 𝔫 : Modulus K} (hi : 𝔪.ideal = 𝔫.ideal) (hr : 𝔪.real = 𝔫.real) : 𝔪 = 𝔫 := by
  cases 𝔪
  cases 𝔫
  cases hi
  cases hr
  rfl

instance : Dvd (Modulus K) :=
  ⟨fun 𝔪 𝔫 ↦ 𝔪.ideal ∣ 𝔫.ideal ∧ 𝔪.real ⊆ 𝔫.real⟩

omit [NumberField K] in
theorem dvd_iff {𝔪 𝔫 : Modulus K} : 𝔪 ∣ 𝔫 ↔ 𝔪.ideal ∣ 𝔫.ideal ∧ 𝔪.real ⊆ 𝔫.real :=
  Iff.rfl

omit [NumberField K] in
theorem dvd_refl' (𝔪 : Modulus K) : 𝔪 ∣ 𝔪 :=
  ⟨dvd_rfl, subset_rfl⟩

theorem ideal_dvd_ideal_iff {𝔪 𝔫 : Modulus K} :
    𝔪.ideal ∣ 𝔫.ideal ↔ ∀ v, 𝔪.exponent v ≤ 𝔫.exponent v := by
  rw [← Ideal.finprod_heightOneSpectrum_pow_multiplicity 𝔪.ideal_ne_bot]
  exact finprod_asIdeal_pow_dvd_iff 𝔪.finite_support_exponent 𝔫.ideal_ne_bot

end Modulus

theorem multiplicity_finprod_asIdeal_pow_eq {a : HeightOneSpectrum (𝓞 K) → ℕ}
    (ha : (support a).Finite) (v : HeightOneSpectrum (𝓞 K)) :
    multiplicity v.asIdeal (∏ᶠ w, w.asIdeal ^ a w) = a v := by
  classical
  set I := ∏ᶠ w : HeightOneSpectrum (𝓞 K), w.asIdeal ^ a w
  have hI : I ≠ ⊥ := finprod_asIdeal_pow_ne_bot a
  have h1 : a v ≤ multiplicity v.asIdeal I := (finprod_asIdeal_pow_dvd_iff ha hI).1 dvd_rfl v
  refine le_antisymm ?_ h1
  by_contra h2
  push Not at h2
  set b : HeightOneSpectrum (𝓞 K) → ℕ := fun w ↦ a w + if w = v then 1 else 0
  have hb : (support b).Finite := (ha.union (Set.finite_singleton v)).subset fun w hw ↦ by
    by_contra hw'
    simp only [Set.mem_union, mem_support, Set.mem_singleton_iff, not_or, not_not] at hw'
    exact hw (by simp [b, hw'.1, hw'.2])
  have hdvd : (∏ᶠ w, w.asIdeal ^ b w) ∣ I := by
    refine (finprod_asIdeal_pow_dvd_iff hb hI).2 fun w ↦ ?_
    by_cases hw : w = v
    · subst hw
      simp only [b, if_true]
      omega
    · simp only [b, if_neg hw, add_zero]
      exact (finprod_asIdeal_pow_dvd_iff ha hI).1 dvd_rfl w
  have hfa : HasFiniteMulSupport fun w : HeightOneSpectrum (𝓞 K) ↦ w.asIdeal ^ a w := by
    rw [HasFiniteMulSupport, mulSupport_asIdeal_pow]; exact ha
  have hfv : HasFiniteMulSupport fun w : HeightOneSpectrum (𝓞 K) ↦
      w.asIdeal ^ (if w = v then 1 else 0) := by
    refine (Set.finite_singleton v).subset fun w hw ↦ ?_
    by_contra hw'
    exact hw (by simp [Set.mem_singleton_iff.not.1 hw'])
  have hsplit : (∏ᶠ w, w.asIdeal ^ b w) = I * v.asIdeal := by
    simp only [b, pow_add]
    rw [finprod_mul_distrib hfa hfv]
    congr 1
    rw [finprod_eq_single _ v fun w hw ↦ by simp [hw], if_pos rfl, pow_one]
  rw [hsplit] at hdvd
  have h1' : I * v.asIdeal ∣ I * 1 := by rwa [mul_one]
  have hv1 := (mul_dvd_mul_iff_left (show I ≠ 0 from hI)).1 h1'
  rw [Ideal.dvd_iff_le, Ideal.one_eq_top, top_le_iff] at hv1
  exact v.isPrime.ne_top hv1

section Local

variable (L : Type*) [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  [IsMulCommutative (L ≃ₐ[K] L)]

theorem isOpen_ker_localSymbol (v : HeightOneSpectrum (𝓞 K)) :
    IsOpen ((localSymbol L v).ker : Set (v.adicCompletion K)ˣ) := by
  obtain ⟨w⟩ := nonempty_placesOver L v
  rw [ker_localSymbol L v w]
  exact LocalField.isOpen_range_normUnits _ _

theorem exists_unitsLevel_le_ker_localSymbol (v : HeightOneSpectrum (𝓞 K)) :
    ∃ n : ℕ, unitsLevel v n ≤ (localSymbol L v).ker := by
  obtain ⟨n, -, hn⟩ := exists_unitsLevel_subset (K := K) v
    ((isOpen_ker_localSymbol L v).mem_nhds (localSymbol L v).ker.one_mem)
  exact ⟨n, hn⟩

def localConductorExponent (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  sInf {n : ℕ | unitsLevel v n ≤ (localSymbol L v).ker}

theorem unitsLevel_le_ker_localSymbol_iff (v : HeightOneSpectrum (𝓞 K)) {n : ℕ} :
    unitsLevel v n ≤ (localSymbol L v).ker ↔ localConductorExponent L v ≤ n := by
  have hne : {n : ℕ | unitsLevel v n ≤ (localSymbol L v).ker}.Nonempty :=
    exists_unitsLevel_le_ker_localSymbol L v
  exact ⟨fun h ↦ Nat.sInf_le h,
    fun h ↦ (unitsLevel_antitone v h).trans (Nat.sInf_mem hne)⟩

theorem unitFiltrationUnits_zero_eq_unitsLevel_zero (v : HeightOneSpectrum (𝓞 K)) :
    LocalField.unitFiltrationUnits (v.adicCompletion K) 0 = unitsLevel v 0 := by
  ext x
  rw [mem_unitFiltrationUnits_zero_iff_valued, mem_unitsLevel]
  refine ⟨fun h ↦ ⟨h, ?_⟩, fun h ↦ h.1⟩
  rw [Nat.cast_zero, neg_zero, exp_zero]
  exact Valuation.map_sub_le _ h.le (by simp)

theorem localConductorExponent_eq_zero_iff (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] :
    localConductorExponent L v = 0 ↔ w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  rw [← Nat.le_zero, ← unitsLevel_le_ker_localSymbol_iff]
  constructor
  · intro h
    exact ramificationIdx_eq_one_of_units_le_ker_localSymbol v
      (by rw [unitFiltrationUnits_zero_eq_unitsLevel_zero]; exact h) w
  · intro he
    rw [unitsLevel_zero]
    exact units_le_ker_localSymbol L v ⟨w, inferInstance⟩ he

theorem finite_support_localConductorExponent :
    (support (localConductorExponent (K := K) L)).Finite := by
  have h := eventually_units_le_ker_localSymbol (K := K) L
  refine (Filter.eventually_cofinite.1 h).subset fun v hv ↦ ?_
  intro hu
  apply hv
  rw [← Nat.le_zero, ← unitsLevel_le_ker_localSymbol_iff, unitsLevel_zero]
  exact hu

end Local

end

end GroundTheory.Global
