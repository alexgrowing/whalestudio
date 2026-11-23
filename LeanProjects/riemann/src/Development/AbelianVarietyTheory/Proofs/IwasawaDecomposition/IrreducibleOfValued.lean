import Mathlib
open IsDedekindDomain NumberField
namespace GlobalTheory
namespace DegreeOneUniformiser

open IsDedekindDomain NumberField in
private theorem adicCompletionIntegers_integers {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Integers
      (v.adicCompletionIntegers F) :=
  ⟨Subtype.val_injective, fun x => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mp x.2,
    fun x hx => ⟨⟨x, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mpr hx⟩, rfl⟩⟩

open IsDedekindDomain NumberField in

theorem _root_.GlobalTheory.DegreeOneUniformiser.irreducible_of_valued {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (π : v.adicCompletionIntegers F)
    (h : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) : Irreducible π := by
  have hI := adicCompletionIntegers_integers v
  have hunit : ∀ x : v.adicCompletionIntegers F, IsUnit x ↔ Valued.v (x : v.adicCompletion F) = 1 :=
    fun x => hI.isUnit_iff_valuation_eq_one
  have hle : ∀ x : v.adicCompletionIntegers F, Valued.v (x : v.adicCompletion F) ≤ 1 :=
    fun x => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mp x.2
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · have := (hunit π).mp hu
    rw [h] at this
    exact absurd this (by decide)
  · have hv : Valued.v (a : v.adicCompletion F) * Valued.v (b : v.adicCompletion F) =
        WithZero.exp (-1 : ℤ) := by
      rw [← h, hab, Subring.coe_mul, map_mul]
    have ha0 : Valued.v (a : v.adicCompletion F) ≠ 0 := fun h0 => by
      rw [h0, zero_mul] at hv; exact WithZero.exp_ne_zero hv.symm
    have hb0 : Valued.v (b : v.adicCompletion F) ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at hv; exact WithZero.exp_ne_zero hv.symm
    obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (a : v.adicCompletion F) = WithZero.exp m :=
      ⟨_, (WithZero.exp_log ha0).symm⟩
    obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v (b : v.adicCompletion F) = WithZero.exp n :=
      ⟨_, (WithZero.exp_log hb0).symm⟩
    have ha := hle a
    have hb := hle b
    rw [hm, hn, ← WithZero.exp_add, WithZero.exp_inj] at hv
    rw [hm, ← WithZero.exp_zero, WithZero.exp_le_exp] at ha
    rw [hn, ← WithZero.exp_zero, WithZero.exp_le_exp] at hb
    rw [hunit, hunit, hm, hn, ← WithZero.exp_zero, WithZero.exp_inj, WithZero.exp_inj]
    omega

open IsDedekindDomain NumberField in

theorem _root_.GlobalTheory.DegreeOneUniformiser.exists_irreducible_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)) (ψ : E →+* v.adicCompletion F), (∀ a : F, ψ (algebraMap F E a) = algebraMap F (v.adicCompletion F) a) → (∀ x : 𝓞 E, ψ (x : E) ∈ v.adicCompletionIntegers F) → (∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ ψ ((x : E)⁻¹) ∉ v.adicCompletionIntegers F)) → ∀ ϖ : 𝓞 E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ∃ π : v.adicCompletionIntegers F, Irreducible π ∧ (π : v.adicCompletion F) = ψ (ϖ : E) := by
  intro F E _ _ _ _ _ v P ψ hψ hint hP ϖ hϖP hϖP2
  have hle : ∀ x : 𝓞 E, Valued.v (ψ (x : E)) ≤ 1 := fun x =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mp (hint x)
  have hne : ∀ x : 𝓞 E, x ≠ 0 → Valued.v (ψ (x : E)) ≠ 0 := by
    intro x hx
    rw [Valuation.ne_zero_iff, map_ne_zero_iff _ ψ.injective]
    exact_mod_cast hx
  have hone : ∀ x : 𝓞 E, x ∉ P.asIdeal → Valued.v (ψ (x : E)) = 1 := by
    intro x hx
    have hx0 : x ≠ 0 := fun h => hx (h ▸ P.asIdeal.zero_mem)
    have h1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mp
      (not_not.mp (mt (hP x hx0).mpr hx))
    rw [map_inv₀, map_inv₀] at h1
    exact le_antisymm (hle x) ((inv_le_one₀ (zero_lt_iff.mpr (hne x hx0))).mp h1)
  have hϖ0 : ϖ ≠ 0 := fun h => hϖP2 (h ▸ Ideal.zero_mem _)
  have hlt : Valued.v (ψ (ϖ : E)) < 1 := by
    have h1 := (hP ϖ hϖ0).mp hϖP
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, not_le, map_inv₀, map_inv₀] at h1
    exact (one_lt_inv₀ (zero_lt_iff.mpr (hne ϖ hϖ0))).mp h1
  obtain ⟨u, hu⟩ := v.intValuation_exists_uniformizer
  let f : 𝓞 E := ⟨algebraMap F E (u : F), (RingOfIntegers.isIntegral_coe u).algebraMap⟩
  have hf : Valued.v (ψ (f : E)) = WithZero.exp (-1 : ℤ) := by
    show Valued.v (ψ (algebraMap F E (u : F))) = _
    rw [hψ, ← hu, ← HeightOneSpectrum.valuation_of_algebraMap (K := F)]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (u : F)
  have hf0 : f ≠ 0 := fun h => by
    rw [h] at hf
    simp only [ZeroMemClass.coe_zero, map_zero] at hf
    exact WithZero.exp_ne_zero hf.symm
  have hfP : f ∈ P.asIdeal := by
    rw [hP f hf0, HeightOneSpectrum.mem_adicCompletionIntegers, not_le, map_inv₀, map_inv₀, hf,
      ← WithZero.exp_neg, neg_neg, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr
    ((Ideal.span_singleton_le_iff_mem _).mpr hϖP : Ideal.span {ϖ} ≤ P.asIdeal)
  have hJP : ¬ J ≤ P.asIdeal := fun hJP => hϖP2 (by
    have hmem : ϖ ∈ Ideal.span {ϖ} := Ideal.mem_span_singleton_self ϖ
    rw [hJ] at hmem
    rw [pow_two]
    exact Ideal.mul_mono_right hJP hmem)
  obtain ⟨t, htJ, htP⟩ := Set.not_subset.mp hJP
  have hft : f * t ∈ Ideal.span {ϖ} := by
    rw [hJ]
    exact Ideal.mul_mem_mul hfP htJ
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hft
  have hval := congrArg (fun x : 𝓞 E => Valued.v (ψ (x : E))) hs
  simp only [MulMemClass.coe_mul, map_mul] at hval
  rw [hone t htP, mul_one, hf] at hval
  have hge : WithZero.exp (-1 : ℤ) ≤ Valued.v (ψ (ϖ : E)) := by
    rw [← hval]
    calc Valued.v (ψ (s : E)) * Valued.v (ψ (ϖ : E)) ≤ 1 * Valued.v (ψ (ϖ : E)) :=
          mul_le_mul' (hle s) le_rfl
      _ = Valued.v (ψ (ϖ : E)) := one_mul _
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (ψ (ϖ : E)) = WithZero.exp m :=
    ⟨_, (WithZero.exp_log (hne ϖ hϖ0)).symm⟩
  rw [hm, WithZero.exp_le_exp] at hge
  rw [hm, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  have hm1 : m = -1 := by omega
  refine ⟨⟨ψ (ϖ : E), hint ϖ⟩, _root_.GlobalTheory.DegreeOneUniformiser.irreducible_of_valued v _ ?_, rfl⟩
  rw [← hm1]
  exact hm

end DegreeOneUniformiser
end GlobalTheory
