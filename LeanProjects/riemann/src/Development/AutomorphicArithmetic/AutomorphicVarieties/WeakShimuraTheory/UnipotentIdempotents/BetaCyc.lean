import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.ExistsResQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk
open scoped Pointwise

namespace UpperTheory.V.Ws.Lk.BetaCyclotomicPlace

variable (l : ℕ) [hl : Fact l.Prime]

private theorem prime_l : Prime ((l : ℕ) : 𝓞 ℚ) := by
  have h : Prime ((l : ℤ)) := Nat.prime_iff_prime_int.1 hl.out
  have h2 := (MulEquiv.prime_iff (Rat.ringOfIntegersEquiv.symm : ℤ ≃* 𝓞 ℚ)).2 h
  simpa using h2

private noncomputable def vQ : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (prime_l l).ne_zero).mpr (prime_l l)
  ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact (prime_l l).ne_zero

variable {l} {Ω : Type} [Field Ω]

private theorem isPlaceOver_vQ [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω)
    (hA : A.valuation ((l : ℕ) : Ω) < 1) : IsPlaceOver (F := ℚ) A (vQ l) := by
  intro x
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, x = (n : 𝓞 ℚ) :=
    ⟨Rat.ringOfIntegersEquiv x, by rw [← map_intCast Rat.ringOfIntegersEquiv.symm, Int.cast_id, RingEquiv.symm_apply_apply]⟩
  have hcast : algebraMap ℚ Ω (((n : 𝓞 ℚ)) : ℚ) = (n : Ω) := by simp
  rw [hcast]
  show _ ↔ (n : 𝓞 ℚ) ∈ Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  rw [Ideal.mem_span_singleton]
  have hle : ∀ m : ℤ, A.valuation (m : Ω) ≤ 1 := fun m => (A.valuation_le_one_iff _).2 (intCast_mem A m)
  have hdvd : ((l : ℕ) : 𝓞 ℚ) ∣ (n : 𝓞 ℚ) ↔ (l : ℤ) ∣ n := by
    rw [show ((l : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm (l : ℤ) by simp,
      show (n : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm n by simp, map_dvd_iff]
  rw [hdvd]
  constructor
  · intro hv
    by_contra hnd
    have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl.out
    obtain ⟨a, b, hab⟩ := (Irreducible.coprime_iff_not_dvd hp.irreducible).2 hnd
    have h1 : A.valuation ((a * l + b * n : ℤ) : Ω) < 1 := by
      push_cast
      apply lt_of_le_of_lt (A.valuation.map_add _ _)
      apply max_lt
      · rw [map_mul]
        calc A.valuation (a : Ω) * A.valuation ((l : ℕ) : Ω) ≤ 1 * A.valuation ((l : ℕ) : Ω) :=
              mul_le_mul' (hle a) le_rfl
          _ < 1 := by rw [one_mul]; exact hA
      · rw [map_mul]
        calc A.valuation (b : Ω) * A.valuation (n : Ω) ≤ 1 * A.valuation (n : Ω) := mul_le_mul' (hle b) le_rfl
          _ < 1 := by rw [one_mul]; exact hv
    rw [hab] at h1
    simp at h1
  · rintro ⟨y, rfl⟩
    push_cast
    rw [map_mul]
    calc A.valuation ((l : ℕ) : Ω) * A.valuation (y : Ω) ≤ A.valuation ((l : ℕ) : Ω) * 1 :=
          mul_le_mul' le_rfl (hle y)
      _ < 1 := by rw [mul_one]; exact hA

end UpperTheory.V.Ws.Lk.BetaCyclotomicPlace

open UpperTheory.V.Ws.Lk.BetaCyclotomicPlace in
theorem UpperTheory.V.Ws.Lk.betaCyc :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ Ω) [NumberField K], Module.finrank ℚ K = 2 → ∀ A₀ : ValuationSubring Ω, A₀.valuation (l : Ω) < 1 → ∀ β : G K Ω →* (PadicAlgCl l)ˣ, (∀ σ ∉ K.fixingSubgroup, ∀ s s' : G K Ω, resQ K s' = σ * resQ K s * σ⁻¹ → β s * β s' = 1) → ∀ U : Subgroup (G K Ω), IsOpen (U : Set (G K Ω)) → (∀ B : ValuationSubring Ω, (∀ x ∈ K, x ∈ B ↔ x ∈ A₀) → ∀ s ∈ U ⊓ Ine (F := K) B, (β s : PadicAlgCl l) ^ 2 = algebraMap ℤ_[l] (PadicAlgCl l) (cycZ K Ω l s : ℤ_[l])) → ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ (b : ℤ) (k : ℕ), 0 < k ∧ Odd b ∧ ∀ s ∈ Ine (F := K) A, (β s ^ 2 * cycBar K Ω l s ^ (-b)) ^ k = 1 := by
  intro Ω _ _ _ l _ K _ hK A₀ hA₀ β hconj U hU hcyc A hA
  have hn : U.index ≠ 0 := by
    haveI : Finite (G K Ω ⧸ U) := U.quotient_finite_of_isOpen hU
    exact Subgroup.index_ne_zero_of_finite
  have hpow : ∀ s : G K Ω, s ^ U.index.factorial ∈ U := fun s =>
    Subgroup.pow_mem_of_index_ne_zero_of_dvd hn s (fun m h1 h2 => Nat.dvd_factorial h1 h2)
  have hkpos : 0 < U.index.factorial := Nat.factorial_pos _
  have hval : ∀ t : G K Ω, ((cycBar K Ω l t : (Qbar l)ˣ) : PadicAlgCl l) =
      algebraMap ℤ_[l] (PadicAlgCl l) (cycZ K Ω l t : ℤ_[l]) := fun t => rfl
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (isPlaceOver_vQ A₀ hA₀) (isPlaceOver_vQ A hA)
  by_cases hσK : σ ∈ K.fixingSubgroup
  · refine ⟨1, U.index.factorial, hkpos, odd_one, ?_⟩
    have hB : ∀ x ∈ K, x ∈ A ↔ x ∈ A₀ := by
      intro x hx
      rw [← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      have hfix : σ⁻¹ • x = x := (K.fixingSubgroup.inv_mem hσK) ⟨x, hx⟩
      rw [hfix]
    intro s hs
    have ht : s ^ U.index.factorial ∈ U ⊓ Ine (F := K) A := ⟨hpow s, pow_mem hs _⟩
    have h1 : β (s ^ U.index.factorial) ^ 2 = cycBar K Ω l (s ^ U.index.factorial) :=
      Units.ext (by push_cast; rw [hcyc A hB _ ht, hval])
    have e1 : (β s ^ 2 * cycBar K Ω l s ^ (-1 : ℤ)) ^ U.index.factorial =
        β (s ^ U.index.factorial) ^ 2 * (cycBar K Ω l (s ^ U.index.factorial))⁻¹ := by
      rw [map_pow, map_pow, zpow_neg, zpow_one]
      simp only [mul_pow, inv_pow, ← pow_mul]
      rw [mul_comm 2]
    rw [e1, h1, mul_inv_cancel]
  · refine ⟨-1, U.index.factorial, hkpos, ⟨-1, by norm_num⟩, ?_⟩
    haveI hN : K.fixingSubgroup.Normal := by
      refine (InfiniteGalois.normal_iff_isGalois K).2 ?_
      haveI : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
      exact isGalois_iff.2 ⟨Algebra.IsSeparable.of_integral _ _, Algebra.IsQuadraticExtension.normal ℚ K⟩
    intro s hs
    have hg : resQ K s ∈ Ine (F := ℚ) A := (resQ_Ine K A s).1 hs
    have hlift : IsLift (RingEquiv.refl ℚ) (σ : Ω ≃+* Ω) := fun y => by simp
    have hg' : conjGal hlift (resQ K s) ∈ Ine (F := ℚ) A₀ := by
      refine conjGal_mem_Ine hlift (fun x => ?_) hg
      rw [← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      show σ⁻¹ • σ • x ∈ A₀ ↔ x ∈ A₀
      rw [inv_smul_smul]
    have heq : conjGal hlift (resQ K s) = σ⁻¹ * resQ K s * σ := by
      ext x
      rfl
    have hmem : σ⁻¹ * resQ K s * σ ∈ K.fixingSubgroup := by
      have h' := hN.conj_mem _ (resQ_mem K s) σ⁻¹
      rwa [inv_inv] at h'
    obtain ⟨s', hs'⟩ := exists_resQ hmem
    have hs'I : s' ∈ Ine (F := K) A₀ := (resQ_Ine K A₀ s').2 (by rw [hs', ← heq]; exact hg')
    have hσ' : σ⁻¹ ∉ K.fixingSubgroup := fun h' => hσK (by simpa using K.fixingSubgroup.inv_mem h')
    have hbb : β s * β s' = 1 := hconj σ⁻¹ hσ' s s' (by rw [hs', inv_inv])
    have hcy : cycBar K Ω l s' = cycBar K Ω l s := by
      show Units.map _ (cycZ K Ω l s') = Units.map _ (cycZ K Ω l s)
      have hz : cycZ ℚ Ω l (σ⁻¹ * resQ K s * σ) = cycZ ℚ Ω l (resQ K s) := by
        rw [map_mul, map_mul, map_inv, mul_comm (cycZ ℚ Ω l σ)⁻¹, inv_mul_cancel_right]
      rw [← resQ_cyc, ← resQ_cyc, hs', hz]
    have ht' : s' ^ U.index.factorial ∈ U ⊓ Ine (F := K) A₀ := ⟨hpow s', pow_mem hs'I _⟩
    have h1 : β (s' ^ U.index.factorial) ^ 2 = cycBar K Ω l (s' ^ U.index.factorial) :=
      Units.ext (by push_cast; rw [hcyc A₀ (fun _ _ => Iff.rfl) _ ht', hval])
    have hbs : β s = (β s')⁻¹ := eq_inv_of_mul_eq_one_left hbb
    have e2 : (β s ^ 2 * cycBar K Ω l s ^ (-(-1) : ℤ)) ^ U.index.factorial =
        (β (s' ^ U.index.factorial) ^ 2)⁻¹ * cycBar K Ω l (s' ^ U.index.factorial) := by
      rw [neg_neg, zpow_one, hbs, ← hcy, map_pow, map_pow]
      simp only [mul_pow, inv_pow, ← pow_mul]
      rw [mul_comm 2]
    rw [e2, h1, inv_mul_cancel]
