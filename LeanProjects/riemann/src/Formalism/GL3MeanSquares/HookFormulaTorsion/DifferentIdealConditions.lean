import Mathlib
import Formalism.GL3MeanSquares.OrbitPointsDistinct
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.DirichletDensity.HostDensityArith

namespace Formalism.HermitianLattices.FiltrationBoundaryCriterion

namespace PfN

section
open Ideal UniqueFactorizationMonoid

theorem nf_map {S : Type*} [CommRing S] [IsDedekindDomain S] (I : Ideal S) (hI : I ≠ ⊥)
    (f : Ideal S ≃* Ideal S) : normalizedFactors (f I) = (normalizedFactors I).map f := by
  have h1 : ∀ P ∈ (normalizedFactors I).map f, Prime P := by
    intro P hP
    obtain ⟨P', hP', rfl⟩ := Multiset.mem_map.mp hP
    exact (MulEquiv.prime_iff f).mpr (prime_of_normalized_factor P' hP')
  have h2 : ((normalizedFactors I).map f).prod = f I := by
    rw [← map_multiset_prod, Ideal.prod_normalizedFactors_eq_self hI]
  have h3 := normalizedFactors_prod_of_prime h1
  rw [h2] at h3
  exact h3

theorem idealConjugateFactorizationUnique {S : Type*} [CommRing S] [IsDedekindDomain S] (D : Ideal S) (hD0 : D ≠ ⊥)
    (f : Ideal S ≃* Ideal S) (hfD : f D = D) (p : Ideal S → Prop)
    (hp : ∀ P ∈ normalizedFactors D, (p (f P) ↔ ¬ p P)) :
    ∃ B : Ideal S, D = B * f B ∧ (∀ P : Ideal S, P.IsPrime → P ∣ B → p P) ∧ B ⊔ f B = ⊤ ∧
      (∀ g : Ideal S ≃* Ideal S, g D = D → (∀ P ∈ normalizedFactors D, (p (g P) ↔ p P)) → g B = B) ∧
      ∀ B' : Ideal S, D = B' * f B' → (∀ P : Ideal S, P.IsPrime → P ∣ B' → p P) → B' = B := by
  classical
  set F := normalizedFactors D with hF
  have hprime : ∀ P ∈ F, Prime P := fun P hP => prime_of_normalized_factor P hP
  have hFf : ∀ g : Ideal S ≃* Ideal S, g D = D → F.map g = F := by
    intro g hg
    rw [hF, ← nf_map D hD0 g, hg]
  have hmax : ∀ P ∈ F, P.IsMaximal := by
    intro P hP
    have hp := hprime P hP
    exact Ideal.IsPrime.isMaximal (Ideal.isPrime_of_prime hp)
      (by rw [← Ideal.zero_eq_bot]; exact hp.ne_zero)
  refine ⟨(F.filter p).prod, ?_, ?_, ?_, ?_, ?_⟩
  · have hsplit : F.filter (fun P => ¬ p P) = (F.filter p).map f := by
      conv_lhs => rw [← hFf f hfD]
      rw [Multiset.filter_map]
      congr 1
      apply Multiset.filter_congr
      intro P hP
      simp only [Function.comp_apply, hp P hP, not_not]
    calc D = F.prod := (Ideal.prod_normalizedFactors_eq_self hD0).symm
      _ = (F.filter p).prod * (F.filter (fun P => ¬ p P)).prod := by
          rw [← Multiset.prod_add, Multiset.filter_add_not]
      _ = _ := by rw [hsplit, map_multiset_prod]
  · intro P hP hdvd
    obtain ⟨Q, hQ, hQP⟩ := hP.multiset_prod_le.mp (Ideal.dvd_iff_le.mp hdvd)
    rw [Multiset.mem_filter] at hQ
    rw [← (hmax Q hQ.1).eq_of_le hP.ne_top hQP]
    exact hQ.2
  · by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hMp := hM.isPrime
    have h1 : (F.filter p).prod ≤ M := le_trans le_sup_left hle
    have h2 : f (F.filter p).prod ≤ M := le_trans le_sup_right hle
    rw [map_multiset_prod] at h2
    obtain ⟨P, hP, hPM⟩ := hMp.multiset_prod_le.mp h1
    obtain ⟨Q, hQ, hQM⟩ := hMp.multiset_prod_le.mp h2
    obtain ⟨P', hP', rfl⟩ := Multiset.mem_map.mp hQ
    rw [Multiset.mem_filter] at hP hP'
    have eqP : P = M := (hmax P hP.1).eq_of_le hM.ne_top hPM
    have hfP' : f P' ∈ F := by rw [← hFf f hfD]; exact Multiset.mem_map_of_mem f hP'.1
    have eqQ : f P' = M := (hmax _ hfP').eq_of_le hM.ne_top hQM
    have := (hp P' hP'.1).mp (by rw [eqQ, ← eqP]; exact hP.2)
    exact this hP'.2
  · intro g hg hpg
    rw [map_multiset_prod]
    congr 1
    conv_rhs => rw [← hFf g hg]
    rw [Multiset.filter_map]
    congr 1
    apply Multiset.filter_congr
    intro P hP
    simp only [Function.comp_apply, hpg P hP]
  · intro B' hB' hpB'
    have hB0 : B' ≠ ⊥ := by
      rintro rfl
      apply hD0
      rw [hB', ← Ideal.zero_eq_bot, zero_mul]
    have hfB0 : f B' ≠ ⊥ := by
      intro h0
      apply hD0
      rw [hB', h0, ← Ideal.zero_eq_bot, mul_zero]
    have hsum : F = normalizedFactors B' + (normalizedFactors B').map f := by
      rw [hF, hB', normalizedFactors_mul hB0 hfB0, nf_map B' hB0 f]
    have hall : ∀ P ∈ normalizedFactors B', p P := by
      intro P hP
      exact hpB' P (Ideal.isPrime_of_prime (prime_of_normalized_factor P hP))
        (dvd_of_mem_normalizedFactors hP)
    have e1 : (normalizedFactors B').filter p = normalizedFactors B' :=
      Multiset.filter_eq_self.mpr hall
    have e2 : ((normalizedFactors B').map f).filter p = 0 := by
      rw [Multiset.filter_eq_nil]
      intro Q hQ
      obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hQ
      have hPF : P ∈ F := by rw [hsum]; exact Multiset.mem_add.mpr (Or.inl hP)
      rw [hp P hPF, not_not]
      exact hall P hP
    rw [hsum, Multiset.filter_add, e1, e2, add_zero, Ideal.prod_normalizedFactors_eq_self hB0]

end

section
open Ideal NumberField Polynomial

theorem diffQuad (K : Type) [Field K] [NumberField K] (d : ℕ) (hd : d.Prime) (hd4 : d % 4 = 3)
    (x : K) (hx : x ^ 2 = -(d : K)) (hadj : IntermediateField.adjoin ℚ {x} = ⊤)
    (β : 𝓞 K) (hβ : (β : K) = x) : differentIdeal ℤ (𝓞 K) = span {β} := by
  have hdisc : discr K = -(d : ℤ) :=
    Formalism.HF.Final.quadDiscr K (-(d : ℤ)) x (by push_cast; exact hx) hadj
      ((Nat.prime_iff_prime_int.mp hd).neg.squarefree) (by omega)
  have hN : (differentIdeal ℤ (𝓞 K)).absNorm = d := by
    rw [absNorm_differentIdeal K, hdisc]; simp
  have hβ2 : β ^ 2 = -(d : 𝓞 K) := by
    apply RingOfIntegers.ext
    have : ((β ^ 2 : 𝓞 K) : K) = (β : K) ^ 2 := by push_cast; rfl
    rw [this, hβ, hx]
    push_cast; rfl
  have hadj' : Algebra.adjoin ℚ {algebraMap (𝓞 K) K β} = ⊤ := by
    have h1 : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
    have h2 := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic h1
    rw [hadj] at h2
    show Algebra.adjoin ℚ {(β : K)} = ⊤
    rw [hβ, ← h2]
    rfl
  have hmem := aeval_derivative_mem_differentIdeal ℤ ℚ K β hadj'
  have hint : IsIntegral ℤ β := Algebra.IsIntegral.isIntegral β
  obtain ⟨r, hr⟩ := minpoly.isIntegrallyClosed_dvd hint (p := X ^ 2 + C (d : ℤ))
    (by simp [hβ2])
  have h2β : 2 * β ∈ differentIdeal ℤ (𝓞 K) := by
    have := congrArg (fun p => aeval β (derivative p)) hr
    simp only [derivative_X_pow, derivative_C, derivative_mul, map_add, map_mul,
      minpoly.aeval, zero_mul, add_zero] at this
    have e : (2 : 𝓞 K) * β = aeval β (derivative (minpoly ℤ β)) * aeval β r := by
      rw [← this]; simp [map_ofNat]
    rw [e]
    exact Ideal.mul_mem_right _ _ hmem
  have hdmem : (d : 𝓞 K) ∈ differentIdeal ℤ (𝓞 K) := by
    have := Ideal.absNorm_mem (differentIdeal ℤ (𝓞 K))
    rwa [hN] at this
  have hβmem : β ∈ differentIdeal ℤ (𝓞 K) := by
    have e : β = (d : 𝓞 K) * β - ((d / 2 : ℕ) : 𝓞 K) * (2 * β) := by
      have h : (d : 𝓞 K) = 2 * ((d / 2 : ℕ) : 𝓞 K) + 1 := by
        have : d = 2 * (d / 2) + 1 := by omega
        exact_mod_cast this
      linear_combination (-β) * h
    rw [e]
    exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hdmem) (Ideal.mul_mem_left _ _ h2β)
  have hle : span {β} ≤ differentIdeal ℤ (𝓞 K) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact hβmem
  obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.mpr hle
  have hrank : Module.finrank ℚ K = 2 := by
    have := Formalism.FrobeniusOrbits.SplitK.finrank_K (L := K) (b := x) hd.pos hx
    unfold Formalism.FrobeniusOrbits.Kd at this
    rw [hadj, IntermediateField.finrank_top'] at this
    exact this
  have hNβ : (span {β}).absNorm ^ 2 = d ^ 2 := by
    rw [← map_pow, Ideal.span_singleton_pow, hβ2, Ideal.absNorm_span_singleton]
    have : (-(d : 𝓞 K)) = algebraMap ℤ (𝓞 K) (-(d : ℤ)) := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank, hrank]
    simp [Int.natAbs_pow]
  have hNβ' : (span {β}).absNorm = d := by
    exact Nat.pow_left_injective (n := 2) (by norm_num) hNβ
  have hC1 : C.absNorm = 1 := by
    have := congrArg Ideal.absNorm hC
    rw [map_mul, hNβ', hN] at this
    exact Nat.eq_of_mul_eq_mul_left hd.pos (by rw [mul_one]; exact this.symm)
  rw [Ideal.absNorm_eq_one_iff] at hC1
  rw [hC, hC1, Ideal.mul_top]

end

section
open NumberField IntermediateField Ideal
open scoped Pointwise

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

theorem diffAbs : DiffAbs := by
  intro e q d hH L _ _ ζ a b h
  have hsq : bE ζ a b ^ 2 = -(d : hostE ζ a b) := DiscrB.bE_sq h
  let x : KinE ζ a b := ⟨bE ζ a b, Principal.bE_mem_KinE ζ a b⟩
  have hx : x ^ 2 = -(d : KinE ζ a b) := by
    apply Subtype.ext
    simpa [x] using hsq
  have hint : IsIntegral ℤ x := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [hx]
    exact (isIntegral_natCast d).neg
  have hadj : IntermediateField.adjoin ℚ {x} = ⊤ := by
    apply Formalism.HF.P.adjoin_top_of_lift
    rw [Set.image_singleton]
    rfl
  obtain ⟨β, hβ⟩ : ∃ β : 𝓞 (KinE ζ a b), (β : KinE ζ a b) = x := ⟨⟨x, hint⟩, rfl⟩
  have hK := diffQuad (KinE ζ a b) d hH.2.1 (by have := hH.2.2.2.1; omega) x hx hadj β hβ
  refine ⟨algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) β, ?_, ?_⟩
  · show (((β : KinE ζ a b)) : hostE ζ a b) = bE ζ a b
    rw [hβ]
  · rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)),
      hK, Ideal.map_span, Set.image_singleton]

variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

theorem fixK (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (hσ : galE e ζ a b σ ∈ Psi e)
    (x : KinE ζ a b) : σ (x : hostE ζ a b) = x := by
  rw [galE_mem_Psi_iff] at hσ
  have : (σ : hostE ζ a b →ₐ[ℚ] hostE ζ a b).comp (KinE ζ a b).val = (KinE ζ a b).val := by
    refine algHom_ext_of_eq_adjoin ℚ (S := KinE ζ a b) (s := {bE ζ a b}) rfl ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hσ
  exact DFunLike.congr_fun this x

abbrev cm (P : Ideal (𝓞 (hostE ζ a b))) : Ideal (𝓞 (KinE ζ a b)) :=
  P.comap (algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)))

theorem cm_smul (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b)
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (hσ : galE e ζ a b σ ∈ Psi e)
    (P : Ideal (𝓞 (hostE ζ a b))) : cm (σ • P) = cm P := by
  ext x
  rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  have : σ⁻¹ • algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) x =
      algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) x := by
    apply RingOfIntegers.ext
    exact fixK (e := e) σ⁻¹ (by rw [galE_inv hqd h]; exact (Psi e).inv_mem hσ) (x : KinE ζ a b)
  rw [this]

theorem smul_int (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (n : ℤ) :
    σ • (n : 𝓞 (hostE ζ a b)) = n :=
  map_intCast (MulSemiringAction.toRingHom _ (𝓞 (hostE ζ a b)) σ) n

theorem int_mem_smul (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (n : ℤ) (P : Ideal (𝓞 (hostE ζ a b)))
    (hn : (n : 𝓞 (hostE ζ a b)) ∈ P) : (n : 𝓞 (hostE ζ a b)) ∈ σ • P := by
  rw [← smul_int σ n]
  exact Ideal.smul_mem_pointwise_smul σ _ P hn

theorem int_mem_of_cm (P : Ideal (𝓞 (hostE ζ a b))) (𝔭 : Ideal (𝓞 (KinE ζ a b))) (hP : cm P = 𝔭)
    (n : ℤ) (hn : (n : 𝓞 (KinE ζ a b)) ∈ 𝔭) : (n : 𝓞 (hostE ζ a b)) ∈ P := by
  rw [← hP, Ideal.mem_comap, map_intCast] at hn
  exact hn

theorem stab_Psi (hH : HostHyp q d) (h : IsLayer (e + 2) q d ζ a b) (r : ℕ) (hr : r = 2 ∨ r = q)
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] (hm : ((r : ℤ) : 𝓞 (hostE ζ a b)) ∈ P)
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (hσ : σ • P = P) : galE e ζ a b σ ∈ Psi e := by
  have hq2 : Nat.Coprime q (2 ^ (e + 2)) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_two_right, Nat.odd_iff]
    have := hH.2.2.1; omega
  have hd2 : Nat.Coprime d (2 ^ (e + 2)) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_two_right, Nat.odd_iff]
    have := hH.2.2.2.1; omega
  have hD := hostDecomp e q d hH L ζ a b h (ZMod.unitOfCoprime q hq2) (ZMod.unitOfCoprime d hd2)
    (by simp) (by simp) σ
  have hst : σ ∈ MulAction.stabilizer _ P := hσ
  rcases hr with rfl | rfl
  · have : P.LiesOver (span {(2 : ℤ)}) := by
      have := liesOver_span_of_natCast_mem_frobenius_orbits P 2 Nat.prime_two hm
      simpa using this
    exact (hD.1 P).mp hst
  · have : P.LiesOver (span {(r : ℤ)}) := liesOver_span_of_natCast_mem_frobenius_orbits P r hH.1 hm
    rw [mem_Psi_iff]
    exact ((hD.2.1 P).mp hst).1

theorem cc_not_mem (e : ℕ) : cc e ∉ Psi e := by
  rw [mem_Psi_iff]
  simp [cc, c0]

theorem not_cm_eq_of_conj_smul_prime (hH : HostHyp q d) (h : IsLayer (e + 2) q d ζ a b)
    (c : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (hc : galE e ζ a b c = cc e) (r : ℕ)
    (hr : r = 2 ∨ r = q) (𝔭 : Ideal (𝓞 (KinE ζ a b)))
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] (hm : ((r : ℤ) : 𝓞 (hostE ζ a b)) ∈ P)
    (h1 : cm P = 𝔭) (h2 : cm (c • P) = 𝔭) : False := by
  have hqd := hH.toHypOdd
  have hEgal : IsGalois ℚ (hostE ζ a b) := hostE_isGalois hqd h
  have hKgal : IsGalois (KinE ζ a b) (hostE ζ a b) := IsGalois.tower_top_of_isGalois ℚ _ _
  have : IsGaloisGroup (hostE ζ a b ≃ₐ[KinE ζ a b] hostE ζ a b) (𝓞 (KinE ζ a b))
      (𝓞 (hostE ζ a b)) := IsGaloisGroup.of_isFractionRing _ _ _ (KinE ζ a b) (hostE ζ a b)
  have l1 : P.LiesOver 𝔭 := ⟨h1.symm⟩
  have l2 : (c • P).LiesOver 𝔭 := ⟨h2.symm⟩
  obtain ⟨τ, hτ⟩ := exists_smul_eq_of_isGaloisGroup 𝔭 P (c • P)
    (hostE ζ a b ≃ₐ[KinE ζ a b] hostE ζ a b)
  have hτ' : (τ.restrictScalars ℚ) • P = c • P := hτ
  have hfix : ((τ.restrictScalars ℚ)⁻¹ * c) • P = P := by
    rw [mul_smul, ← hτ', inv_smul_smul]
  have hmem := stab_Psi hH h r hr P hm _ hfix
  rw [galE_mul hqd h, galE_inv hqd h, hc] at hmem
  have hτΨ := Principal.galE_restrict_mem_Psi (e := e) τ
  have := (Psi e).mul_mem hτΨ hmem
  rw [mul_inv_cancel_left] at this
  exact cc_not_mem e this

theorem atLeast (hH : HostHyp q d) (h : IsLayer (e + 2) q d ζ a b)
    (c : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (hc : galE e ζ a b c = cc e) (r : ℕ) (hr : r.Prime)
    (𝔭 : Ideal (𝓞 (KinE ζ a b))) [𝔭.IsPrime] (hm𝔭 : ((r : ℤ) : 𝓞 (KinE ζ a b)) ∈ 𝔭)
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] (hm : ((r : ℤ) : 𝓞 (hostE ζ a b)) ∈ P) :
    cm P = 𝔭 ∨ cm (c • P) = 𝔭 := by
  have hqd := hH.toHypOdd
  have hEgal : IsGalois ℚ (hostE ζ a b) := hostE_isGalois hqd h
  have : IsGaloisGroup (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) ℤ (𝓞 (hostE ζ a b)) :=
    IsGaloisGroup.of_isFractionRing _ _ _ ℚ (hostE ζ a b)
  obtain ⟨P₀, -, hP₀, hcm⟩ := Ideal.exists_ideal_over_prime_of_isIntegral 𝔭
    (⊥ : Ideal (𝓞 (hostE ζ a b))) (by simp [← RingHom.ker_eq_comap_bot])
  have hm₀ := int_mem_of_cm P₀ 𝔭 hcm r hm𝔭
  have l0 : P₀.LiesOver (span {(r : ℤ)}) := liesOver_span_of_natCast_mem_frobenius_orbits P₀ r hr hm₀
  have l1 : P.LiesOver (span {(r : ℤ)}) := liesOver_span_of_natCast_mem_frobenius_orbits P r hr hm
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isGaloisGroup (span {(r : ℤ)}) P₀ P
    (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b)
  by_cases hΨ : galE e ζ a b σ ∈ Psi e
  · left
    rw [← hσ, cm_smul hqd h σ hΨ]; exact hcm
  · right
    rw [← hσ, ← mul_smul, cm_smul hqd h (c * σ) ?_]
    · exact hcm
    rw [galE_mul hqd h, hc, mem_Psi_iff]
    rw [mem_Psi_iff] at hΨ
    rcases Int.units_eq_one_or (galE e ζ a b σ).1.2 with h1 | h1
    · exact absurd h1 hΨ
    · simp [cc, c0, h1]

theorem key (hH : HostHyp q d) (h : IsLayer (e + 2) q d ζ a b)
    (c : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (hc : galE e ζ a b c = cc e) (r : ℕ) (hr : r = 2 ∨ r = q)
    (𝔭 : Ideal (𝓞 (KinE ζ a b))) [𝔭.IsPrime] (hm𝔭 : ((r : ℤ) : 𝓞 (KinE ζ a b)) ∈ 𝔭)
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] (hm : ((r : ℤ) : 𝓞 (hostE ζ a b)) ∈ P) :
    cm (c • P) = 𝔭 ↔ ¬ cm P = 𝔭 := by
  have hrp : r.Prime := by
    rcases hr with rfl | rfl
    · exact Nat.prime_two
    · exact hH.1
  constructor
  · intro h2 h1
    exact not_cm_eq_of_conj_smul_prime hH h c hc r hr 𝔭 P hm h1 h2
  · intro h1
    exact (atLeast hH h c hc r hrp 𝔭 hm𝔭 P hm).resolve_left h1

theorem excl (r s : ℕ) (hrs : Nat.Coprime r s) (𝔭 : Ideal (𝓞 (KinE ζ a b)))
    (hs : ((s : ℤ) : 𝓞 (KinE ζ a b)) ∈ 𝔭)
    (P : Ideal (𝓞 (hostE ζ a b))) [hP : P.IsPrime] (hm : ((r : ℤ) : 𝓞 (hostE ζ a b)) ∈ P) :
    cm P ≠ 𝔭 := by
  intro h1
  have hs' := int_mem_of_cm P 𝔭 h1 s hs
  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.mpr hrs)
  apply hP.ne_top
  rw [Ideal.eq_top_iff_one]
  have : (1 : 𝓞 (hostE ζ a b)) = (u : 𝓞 (hostE ζ a b)) * ((r : ℤ) : 𝓞 (hostE ζ a b)) +
      (v : 𝓞 (hostE ζ a b)) * ((s : ℤ) : 𝓞 (hostE ζ a b)) := by
    exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 (hostE ζ a b)) huv.symm
  rw [this]
  exact P.add_mem (P.mul_mem_left _ hm) (P.mul_mem_left _ hs')

theorem principalStable : PrincipalStable := by
  intro e q d hH L _ _ ζ a b h c hc 𝔭₂ 𝔭q h𝔭₂ h𝔭q h2 hq
  have hqd := hH.toHypOdd
  have hD0 : differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) ≠ ⊥ := by
    have := differentIdeal_ne_bot (A := 𝓞 (KinE ζ a b)) (B := 𝓞 (hostE ζ a b))
    exact this
  let f : (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) → (Ideal (𝓞 (hostE ζ a b)) ≃* Ideal (𝓞 (hostE ζ a b))) :=
    fun σ => (MulSemiringAction.toRingEquiv (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b)
      (Ideal (𝓞 (hostE ζ a b))) σ).toMulEquiv
  have hf : ∀ σ I, f σ I = σ • I := fun σ I => rfl
  have hcop : Nat.Coprime 2 q := by
    rw [Nat.coprime_two_left, Nat.odd_iff]
    have := hH.2.2.1; omega
  obtain ⟨B, hB1, hB2, hB3, hB4, hB5⟩ := idealConjugateFactorizationUnique _ hD0 (f c)
    (by rw [hf]; exact Principal.diff_smul_eq hqd h c)
    (fun P => cm P = 𝔭₂ ∨ cm P = 𝔭q)
    (by
      intro P hP
      rw [hf]
      rw [Ideal.mem_normalizedFactors_iff hD0] at hP
      obtain ⟨hPp, hle⟩ := hP
      have hdvd : P ∣ differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) := Ideal.dvd_iff_le.mpr hle
      rcases hostDiffSupport e q d hH L ζ a b h P hPp hdvd with hm | hm
      · have hm' : (((2 : ℕ) : ℤ) : 𝓞 (hostE ζ a b)) ∈ P := by exact_mod_cast hm
        have h2' : (((2 : ℕ) : ℤ) : 𝓞 (KinE ζ a b)) ∈ 𝔭₂ := by exact_mod_cast h2
        rw [or_iff_left (excl 2 q hcop 𝔭q hq (c • P) (int_mem_smul c _ P hm')),
          or_iff_left (excl 2 q hcop 𝔭q hq P hm')]
        exact key hH h c hc 2 (Or.inl rfl) 𝔭₂ h2' P hm'
      · have h2' : (((2 : ℕ) : ℤ) : 𝓞 (KinE ζ a b)) ∈ 𝔭₂ := by exact_mod_cast h2
        rw [or_iff_right (excl q 2 hcop.symm 𝔭₂ h2' (c • P) (int_mem_smul c _ P hm)),
          or_iff_right (excl q 2 hcop.symm 𝔭₂ h2' P hm)]
        exact key hH h c hc q (Or.inr rfl) 𝔭q hq P hm)
  refine ⟨B, hB1, hB2, hB3, ?_, hB5⟩
  intro σ hσ
  refine hB4 (f σ) (by rw [hf]; exact Principal.diff_smul_eq hqd h σ) ?_
  intro P _
  rw [hf, cm_smul hqd h σ hσ]

end

end PfN

theorem difference_absolute_bound : DiffAbs := PfN.diffAbs
theorem principal_part_stable : PrincipalStable := PfN.principalStable

end Formalism.HermitianLattices.FiltrationBoundaryCriterion
