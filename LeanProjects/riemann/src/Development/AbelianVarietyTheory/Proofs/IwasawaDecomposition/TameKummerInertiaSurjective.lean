import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EmbeddingMemCoefficientField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValSubOneLtOfRed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteGaloisInertiaLiftsAbsoluteInertiaRat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompositumIntermediateFieldExistsPlaceValuationE
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsInertiaLift
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting

noncomputable section

namespace GlobalTheory.TameKummerInertia

theorem unram_of_fixed : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (L : IntermediateField E Ω) [FiniteDimensional E L] [IsGalois E L] [NumberField L] (K : IntermediateField E L) [NumberField K] (Q : Ideal (𝓞 L)) [Q.IsPrime], (∀ x : 𝓞 L, x ∈ Q ↔ A.valuation (((x : L) : Ω)) < 1) → (∀ σ ∈ Ine (F := E) A, ∀ y : K, σ (((y : L) : Ω)) = ((y : L) : Ω)) → (Q.under (𝓞 K)).ramificationIdx (𝓞 E) = 1 := by
  intro E Ω _ _ _ _ _ A L _ _ _ K _ Q _ hQ hfix
  rw [GlobalTheory.UnramCompositum.ramificationIdx_eq_one_iff_fix E K L Q]
  intro τ hτ y
  have hint : ∀ a : 𝓞 L, A.valuation (algebraMap L Ω (a : L)) ≤ 1 := fun a =>
    GlobalTheory.CMRam.val_int_le (algebraMap L Ω) A a
  have hsm : ∀ a : 𝓞 L, ((τ • a : 𝓞 L) : L) = τ (a : L) := fun a => rfl
  have hτ' : ∀ a : 𝓞 L, A.valuation (algebraMap L Ω (τ (a : L)) - algebraMap L Ω (a : L)) < 1 := by
    intro a
    have := (hQ _).1 (hτ a)
    simpa [hsm] using this
  have hlift : ∀ x : L, A.valuation (algebraMap L Ω x) ≤ 1 →
      A.valuation (algebraMap L Ω (τ x) - algebraMap L Ω x) < 1 := by
    intro x hx
    obtain ⟨s, t, hs, e⟩ := GlobalTheory.CMRam.exists_den_field (algebraMap L Ω) A hx
    have hτs : A.valuation (algebraMap L Ω (τ (s : L))) = 1 := by
      refine le_antisymm ?_ ?_
      · have := hint (τ • s); rwa [hsm] at this
      · by_contra hlt
        push Not at hlt
        have h2 : A.valuation (algebraMap L Ω (s : L)) < 1 := by
          have e2 : algebraMap L Ω (s : L) = algebraMap L Ω (τ (s : L)) - (algebraMap L Ω (τ (s : L)) - algebraMap L Ω (s : L)) := by ring
          rw [e2]; exact Valuation.map_sub_lt _ hlt (hτ' s)
        rw [hs] at h2; exact lt_irrefl _ h2
    have he' : τ (s : L) * τ x = τ (t : L) := by rw [← map_mul, e]
    have key : algebraMap L Ω (τ (s : L)) * (algebraMap L Ω (τ x) - algebraMap L Ω x) =
        (algebraMap L Ω (τ (t : L)) - algebraMap L Ω (t : L)) + algebraMap L Ω x * (algebraMap L Ω (s : L) - algebraMap L Ω (τ (s : L))) := by
      rw [← he', ← e]; simp only [map_mul]; ring
    have hv : A.valuation (algebraMap L Ω (τ (s : L)) * (algebraMap L Ω (τ x) - algebraMap L Ω x)) < 1 := by
      rw [key]
      refine Valuation.map_add_lt _ (hτ' t) ?_
      rw [Valuation.map_mul, Valuation.map_sub_swap]
      calc A.valuation (algebraMap L Ω x) * A.valuation (algebraMap L Ω (τ (s : L)) - algebraMap L Ω (s : L))
          ≤ 1 * A.valuation (algebraMap L Ω (τ (s : L)) - algebraMap L Ω (s : L)) := mul_le_mul_left hx _
        _ < 1 := by rw [one_mul]; exact hτ' s
    rwa [Valuation.map_mul, hτs, one_mul] at hv
  obtain ⟨σ, hσ, hσx⟩ := GlobalTheory.InertiaLift.exists_mem_Ine_lift A L τ hlift
  apply Subtype.ext
  have h1 := hσx (algebraMap K L y)
  have h2 := hfix σ hσ y
  exact (h1.symm.trans h2 : _)

theorem index_one_root : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (v : HeightOneSpectrum (𝓞 E)) (P : Ideal (𝓞 K)) [P.IsPrime], P.under (𝓞 E) = v.asIdeal → P.ramificationIdx (𝓞 E) = 1 → ∀ (g : ℕ), ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ((g : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2 → ∀ (k : ℕ) (Z : K), Z ^ k = ((g : ℕ) : K) → k ≤ 1 := by
  intro E K _ _ _ _ _ v P _ hPv he g hgv hgv2 k Z hZ
  by_contra hk
  push Not at hk
  haveI : P.LiesOver v.asIdeal := ⟨hPv.symm⟩
  have he' : Ideal.ramificationIdx' v.asIdeal P = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal P v.ne_bot]; exact he
  have hmap : Ideal.map (algebraMap (𝓞 E) (𝓞 K)) v.asIdeal ≤ P :=
    Ideal.map_le_iff_le_comap.2 (le_of_eq hPv.symm)
  have hnot : ¬ Ideal.map (algebraMap (𝓞 E) (𝓞 K)) v.asIdeal ≤ P ^ 2 := fun h =>
    (Ideal.ramificationIdx'_ne_one_iff hmap).2 h he'
  have hZi : IsIntegral ℤ Z := by
    refine IsIntegral.of_pow (n := k) (by omega) ?_
    rw [hZ, ← map_natCast (algebraMap ℤ K) g]
    exact isIntegral_algebraMap
  set z : 𝓞 K := ⟨Z, hZi⟩ with hzdef
  have hz : z ^ k = ((g : ℕ) : 𝓞 K) := by
    apply NumberField.RingOfIntegers.ext
    simp only [RingOfIntegers.coe_eq_algebraMap, map_pow, map_natCast]
    exact hZ
  have hgP : ((g : ℕ) : 𝓞 K) ∈ P := by
    have h0 : ((g : ℕ) : 𝓞 E) ∈ P.under (𝓞 E) := hPv ▸ hgv
    rw [Ideal.under, Ideal.mem_comap, map_natCast] at h0
    exact h0
  have hzP : z ∈ P := Ideal.IsPrime.mem_of_pow_mem ‹_› k (hz ▸ hgP)
  have hgP2 : ((g : ℕ) : 𝓞 K) ∈ P ^ 2 := by
    rw [← hz, show k = 2 + (k - 2) by omega, pow_add]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hzP 2)
  obtain ⟨J, hJ⟩ : v.asIdeal ∣ Ideal.span {((g : ℕ) : 𝓞 E)} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hgv)
  have hJv : ¬ J ≤ v.asIdeal := by
    intro hle; apply hgv2
    have : Ideal.span {((g : ℕ) : 𝓞 E)} ≤ v.asIdeal ^ 2 := by
      rw [hJ, pow_two]; exact Ideal.mul_mono_right hle
    exact this (Ideal.mem_span_singleton_self _)
  obtain ⟨j, hjJ, hjv⟩ := Set.not_subset.1 hJv
  have hjP : algebraMap (𝓞 E) (𝓞 K) j ∉ P := by
    intro h; apply hjv; rw [← hPv]; exact h
  haveI hPmax : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P
    (by rw [show Ideal.comap (algebraMap (𝓞 E) (𝓞 K)) P = v.asIdeal from hPv]; exact v.isMaximal)
  have hrad : (P ^ 2).radical = P := by rw [Ideal.radical_pow _ two_ne_zero, hPmax.isPrime.radical]
  have hprim : (P ^ 2).IsPrimary := Ideal.isPrimary_of_isMaximal_radical (by rw [hrad]; exact hPmax)
  apply hnot
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  have hxj : x * j ∈ Ideal.span {((g : ℕ) : 𝓞 E)} := by rw [hJ]; exact Ideal.mul_mem_mul hx hjJ
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hxj
  have h1 : algebraMap (𝓞 E) (𝓞 K) j * algebraMap (𝓞 E) (𝓞 K) x ∈ P ^ 2 := by
    rw [← map_mul, mul_comm, ← hc, map_mul, map_natCast]; exact Ideal.mul_mem_left _ _ hgP2
  rcases hprim.mem_or_mem h1 with h | h
  · exact h
  · exfalso; rw [Submodule.colon_univ, hrad] at h; exact hjP h

theorem tame_kummer_surj : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ((g : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2 → ∀ (m : ℕ), 0 < m → ¬ g ∣ m → ∀ Y μ : Ω, Y ^ m = ((g : ℕ) : Ω) → μ ^ m = 1 → ∃ σ ∈ Ine (F := E) A, σ Y = μ * Y := by
  intro E Ω _ _ _ _ _ A v hA g _ hgv hgv2 m hm hgm Y μ hY hμ
  have hgp : g.Prime := Fact.out
  have hg := GlobalTheory.TameCoupledEx.val_g_lt A v hA hgv
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : NeZero m := ⟨hm.ne'⟩
  have hg0 : ((g : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.2 hgp.ne_zero
  have hY0 : Y ≠ 0 := GlobalTheory.TameCoupledEx.ne_zero_of_pow_eq hgp hm hY
  have hpow : ∀ σ : G E Ω, (σ Y / Y) ^ m = 1 := fun σ => tameQuot_pow σ hg0 hY
  have hne : ∀ σ : G E Ω, σ Y / Y ≠ 0 := fun σ => div_ne_zero (by simpa using hY0) hY0
  let χ : Ine (F := E) A →* rootsOfUnity m Ω :=
    { toFun := fun σ => ⟨Units.mk0 (σ.1 Y / Y) (hne σ.1), by
        rw [mem_rootsOfUnity]; ext; simp [hpow]⟩
      map_one' := by ext; simp [hY0]
      map_mul' := fun σ τ => by
        ext
        simp only [Subgroup.coe_mul, Units.val_mk0, Subgroup.coe_mul, Units.val_mul]
        exact GlobalTheory.TameCoupledEx.ratio_mul hgp hg σ.2 τ.1 hm hgm hY }
  have hχ : ∀ σ, (((χ σ : rootsOfUnity m Ω) : Ωˣ) : Ω) = σ.1 Y / Y := fun σ => rfl
  obtain ⟨⟨c, σ0, hσ0⟩, hc⟩ := IsCyclic.exists_generator (α := χ.range)
  set d := orderOf c with hd
  have hcm : c ^ m = 1 := by
    ext; simpa [← hσ0, hχ] using hpow σ0.1
  have hdm : d ∣ m := orderOf_dvd_of_pow_eq_one hcm
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdm hm
  have hall : ∀ σ : G E Ω, σ ∈ Ine (F := E) A → (σ Y / Y) ^ d = 1 := by
    intro σ hσ
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hc ⟨χ ⟨σ, hσ⟩, ⟨σ, hσ⟩, rfl⟩)
    have h1 : (χ ⟨σ, hσ⟩) ^ d = 1 := by
      have := congrArg Subtype.val hj
      simp only [Subgroup.coe_zpow] at this
      rw [← this, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd, pow_orderOf_eq_one, one_zpow]
    have h2 := congrArg (fun u : rootsOfUnity m Ω => ((u : Ωˣ) : Ω)) h1
    simpa [hχ] using h2
  set Z := Y ^ d with hZ
  have hZfix : ∀ σ : G E Ω, σ ∈ Ine (F := E) A → σ Z = Z := by
    intro σ hσ
    have e : σ Y = (σ Y / Y) * Y := by field_simp
    rw [hZ, map_pow, e, mul_pow, hall σ hσ, one_mul]
  set n := m / d with hn
  have hnd : d * n = m := Nat.mul_div_cancel' hdm
  have hZn : Z ^ n = ((g : ℕ) : Ω) := by rw [hZ, ← pow_mul, hnd, hY]
  have hn1 : n ≤ 1 := by
    have hZi : IsIntegral E Z := Algebra.IsIntegral.isIntegral Z
    haveI : FiniteDimensional E (IntermediateField.adjoin E {Z}) := IntermediateField.adjoin.finiteDimensional hZi
    set L := IntermediateField.normalClosure E (IntermediateField.adjoin E {Z}) Ω with hLdef
    haveI : NumberField L := NumberField.of_module_finite E L
    have hZL : Z ∈ L := IntermediateField.le_normalClosure _ (IntermediateField.mem_adjoin_simple_self E Z)
    set Z' : L := ⟨Z, hZL⟩ with hZ'
    set K : IntermediateField E L := IntermediateField.adjoin E {Z'} with hK
    haveI : NumberField K := NumberField.of_module_finite E K
    let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A.toSubring
      (fun x => ReciprocityTheory.Gal.mem_of_isIntegral_int A ((x.isIntegral_coe.map (IsScalarTower.toAlgHom ℤ L Ω))))
    set Q : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap f with hQ
    haveI : Q.IsPrime := Ideal.comap_isPrime f _
    have hQmem : ∀ x : 𝓞 L, x ∈ Q ↔ A.valuation (((x : L) : Ω)) < 1 := fun x =>
      Ideal.mem_comap.trans (ValuationSubring.valuation_lt_one_iff A (f x))
    have hfixK : ∀ σ ∈ Ine (F := E) A, ∀ y : K, σ (((y : L) : Ω)) = ((y : L) : Ω) := by
      intro σ hσ y
      have hle : K.toSubalgebra ≤ AlgHom.equalizer ((σ : Ω →ₐ[E] Ω).comp L.val) L.val := by
        rw [hK, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic Z')]
        refine Algebra.adjoin_le ?_
        rintro _ rfl
        exact hZfix σ hσ
      exact hle y.2
    have e1 := unram_of_fixed E Ω A L K Q hQmem hfixK
    have hunder : (Q.under (𝓞 K)).under (𝓞 E) = v.asIdeal := by
      ext x
      rw [Ideal.under_under, Ideal.mem_comap, hQmem, ← hA x]
      rfl
    set Z'' : K := ⟨Z', IntermediateField.mem_adjoin_simple_self E Z'⟩ with hZ''
    have hZ''n : Z'' ^ n = ((g : ℕ) : K) := by
      apply Subtype.ext; apply Subtype.ext
      simpa using hZn
    exact index_one_root E K v (Q.under (𝓞 K)) hunder e1 g hgv hgv2 n Z'' hZ''n
  have hdm' : d = m := by
    have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro h; rw [h, mul_zero] at hnd; exact hm.ne' hnd.symm)
    have : n = 1 := le_antisymm hn1 hn0
    rw [this, mul_one] at hnd; exact hnd
  have hprim : IsPrimitiveRoot (σ0.1 Y / Y) m := by
    have h1 : orderOf (σ0.1 Y / Y) = m := by
      rw [← hχ, orderOf_units, Subgroup.orderOf_coe, hσ0, ← hd, hdm']
    rw [← h1]; exact IsPrimitiveRoot.orderOf _
  obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hμ
  refine ⟨σ0.1 ^ i, pow_mem σ0.2 i, ?_⟩
  have := GlobalTheory.TameCoupledEx.ratio_pow hgp hg σ0.2 hm hgm hY i
  rw [hi] at this
  field_simp at this
  rw [this, mul_comm]

end GlobalTheory.TameKummerInertia
