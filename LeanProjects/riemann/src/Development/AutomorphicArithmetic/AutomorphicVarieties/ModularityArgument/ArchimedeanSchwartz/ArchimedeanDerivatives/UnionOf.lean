import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.NormChar
import ReciprocityTheory.Chebotarev.CyclotomicIrreducibleOfForallIsUnramifiedAt

noncomputable section

open NumberField IsDedekindDomain Polynomial GlobalTheory.HenQ Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V.Z.Bc

namespace UpperTheory.V.Z.Inf

section Primes

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

private theorem natCast_mem {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) {q : ℕ}
    (hq : q.Prime) (hd : q ∣ Ideal.absNorm w.asIdeal) : (q : 𝓞 F) ∈ w.asIdeal := by
  have hne : Ideal.absNorm w.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
  have hcard : Ideal.absNorm w.asIdeal = Nat.card (𝓞 F ⧸ w.asIdeal) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have : Finite (𝓞 F ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (hcard ▸ hne)
  have := Fact.mk hq
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 F ⧸ w.asIdeal) q (hcard ▸ hd)
  have h1 : q • x = 0 := hx ▸ addOrderOf_nsmul_eq_zero x
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, addOrderOf_zero] at hx
    exact hq.one_lt.ne hx
  have := w.isPrime
  rw [nsmul_eq_mul] at h1
  have h2 := (mul_eq_zero.1 h1).resolve_right hx0
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact h2

private theorem normV_absNorm {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) :
    normV w = Ideal.absNorm w.asIdeal := by
  rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

private theorem absNorm_pow (w : HeightOneSpectrum (𝓞 M)) :
    Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ (w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  rw [Ideal.inertiaDeg'_eq_inertiaDeg, Ideal.absNorm_pow_inertiaDeg]

private theorem sum_ef (hE : Module.finrank K M = 2) (v : HeightOneSpectrum (𝓞 K)) :
    ∑ P ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 M), v.asIdeal.ramificationIdx' P * v.asIdeal.inertiaDeg' P = 2 := by
  have := v.isMaximal
  rw [← hE]
  exact Ideal.sum_ramification_inertia (𝓞 M) K M v.ne_bot

private theorem mem_over (w : HeightOneSpectrum (𝓞 M)) :
    w.asIdeal ∈ IsDedekindDomain.primesOverFinset (w.under (𝓞 K)).asIdeal (𝓞 M) := by
  rw [IsDedekindDomain.mem_primesOverFinset_iff (w.under (𝓞 K)).ne_bot]
  exact ⟨w.isPrime, ⟨rfl⟩⟩

private theorem e_pos (w : HeightOneSpectrum (𝓞 M)) : 0 < (w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  exact Nat.pos_of_ne_zero (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver _ (w.under (𝓞 K)).ne_bot)

private theorem f_pos (w : HeightOneSpectrum (𝓞 M)) : 0 < (w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := (w.under (𝓞 K)).isMaximal
  exact Nat.pos_of_ne_zero (Ideal.inertiaDeg'_ne_zero _ _)

private theorem f_one (hE : Module.finrank K M = 2) {w w' : HeightOneSpectrum (𝓞 M)} (hne : w' ≠ w)
    (hu : w'.under (𝓞 K) = w.under (𝓞 K)) : (w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal = 1 := by
  classical
  have h1 := mem_over (K := K) w
  have h2 := mem_over (K := K) w'
  rw [hu] at h2
  have hne' : w.asIdeal ≠ w'.asIdeal := fun h => hne (HeightOneSpectrum.ext h.symm)
  have hsub : ({w.asIdeal, w'.asIdeal} : Finset (Ideal (𝓞 M))) ⊆
      IsDedekindDomain.primesOverFinset (w.under (𝓞 K)).asIdeal (𝓞 M) := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hle := Finset.sum_le_sum_of_subset
    (f := fun P => (w.under (𝓞 K)).asIdeal.ramificationIdx' P * (w.under (𝓞 K)).asIdeal.inertiaDeg' P) hsub
  rw [Finset.sum_pair hne', sum_ef hE] at hle
  have a := e_pos (K := K) w
  have b := f_pos (K := K) w
  have c := e_pos (K := K) w'
  have d := f_pos (K := K) w'
  rw [hu] at c d
  have : (w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal ≤ 1 := by nlinarith
  omega

private theorem f_two (hE : Module.finrank K M = 2) (w : HeightOneSpectrum (𝓞 M))
    (honly : ∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 K) = w.under (𝓞 K) → w' = w)
    (he : (w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal = 1) :
    (w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal = 2 := by
  classical
  have h := sum_ef (K := K) (M := M) hE (w.under (𝓞 K))
  rw [Finset.sum_eq_single_of_mem w.asIdeal (mem_over w) (fun Q hQ hQw => ?_), he, one_mul] at h
  · exact h
  · exfalso
    apply hQw
    rw [IsDedekindDomain.mem_primesOverFinset_iff (w.under (𝓞 K)).ne_bot] at hQ
    obtain ⟨hQp, hQl⟩ := hQ
    have hQ0 : Q ≠ ⊥ := by
      rintro rfl
      apply (w.under (𝓞 K)).ne_bot
      rw [hQl.over]
      exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
    have := honly ⟨Q, hQp, hQ0⟩ (HeightOneSpectrum.ext hQl.over.symm)
    exact congrArg HeightOneSpectrum.asIdeal this

private theorem unram_bound (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] :
    ∃ N : ℕ, ∀ w : HeightOneSpectrum (𝓞 M),
    ((N.factorial : ℕ) : 𝓞 K) ∉ (w.under (𝓞 K)).asIdeal → (w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal = 1 := by
  obtain ⟨N, hN⟩ := ReciprocityTheory.Cheb.exists_forall_isUnramifiedAt M
  refine ⟨N, fun w hw => ?_⟩
  have h1 : 1 < Ideal.absNorm (w.under (𝓞 K)).asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm _
  have hq := Nat.minFac_prime h1.ne'
  have hqv : ((Nat.minFac (Ideal.absNorm (w.under (𝓞 K)).asIdeal) : ℕ) : 𝓞 K) ∈ (w.under (𝓞 K)).asIdeal :=
    natCast_mem _ hq (Nat.minFac_dvd _)
  have hqN : N < Nat.minFac (Ideal.absNorm (w.under (𝓞 K)).asIdeal) := by
    by_contra hle
    push_neg at hle
    apply hw
    obtain ⟨k, hk⟩ := Nat.dvd_factorial hq.pos hle
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hqv
  have hqw : ((Nat.minFac (Ideal.absNorm (w.under (𝓞 K)).asIdeal) : ℕ) : 𝓞 M) ∈ w.asIdeal := by
    have : algebraMap (𝓞 K) (𝓞 M) ((Nat.minFac (Ideal.absNorm (w.under (𝓞 K)).asIdeal) : ℕ) : 𝓞 K) ∈ w.asIdeal := hqv
    rwa [map_natCast] at this
  haveI := w.isPrime
  haveI := hN _ hq hqN w.asIdeal hqw
  have hsq := ReciprocityTheory.Cheb.natCast_notMem_sq_of_isUnramifiedAt hq w.asIdeal
  apply Ideal.ramificationIdx'_spec
  · rw [pow_one, Ideal.map_le_iff_le_comap]
    exact le_rfl
  · intro h
    have h3 := h (Ideal.mem_map_of_mem (algebraMap (𝓞 K) (𝓞 M)) hqv)
    rw [map_natCast] at h3
    exact hsq (by simpa using h3)

private theorem exists_over (p : HeightOneSpectrum (𝓞 K)) :
    ∃ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = p := by
  have := p.isMaximal
  obtain ⟨Q, hQm, hQl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 M) p.asIdeal
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply p.ne_bot
    rw [hQl.over]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  exact ⟨⟨Q, hQm.isPrime, hQ0⟩, HeightOneSpectrum.ext hQl.over.symm⟩

private theorem finite_above (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) :
    {w : HeightOneSpectrum (𝓞 M) | w.under (𝓞 K) ∈ S}.Finite := by
  classical
  have : {w : HeightOneSpectrum (𝓞 M) | w.under (𝓞 K) ∈ S} ⊆
      ⋃ p ∈ S, HeightOneSpectrum.asIdeal ⁻¹' (↑(IsDedekindDomain.primesOverFinset (p : HeightOneSpectrum (𝓞 K)).asIdeal (𝓞 M)) : Set (Ideal (𝓞 M))) := by
    intro w hw
    exact Set.mem_biUnion hw (mem_over w)
  refine (hS.biUnion fun p _ => ?_).subset this
  exact (Finset.finite_toSet _).preimage (fun a _ b _ h => HeightOneSpectrum.ext h)

private theorem ind_key (hE : Module.finrank K M = 2) (sat : HeightOneSpectrum (𝓞 M) → Multiset ℂˣ → Prop)
    (satP : HeightOneSpectrum (𝓞 K) → Multiset ℂˣ → Prop) (hI : IndSys sat satP) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) ∉ S →
      (Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ∧ ∃ w' : HeightOneSpectrum (𝓞 M), w' ≠ w ∧
        w'.under (𝓞 K) = w.under (𝓞 K) ∧ ∃ B B', sat w B ∧ sat w' B' ∧ satP (w.under (𝓞 K)) (B + B')) ∨
      (Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ 2 ∧
        ∃ B B' : Multiset ℂˣ, sat w (B'.map (· ^ 2)) ∧ B = B' + B'.map (fun b => -b) ∧ satP (w.under (𝓞 K)) B) := by
  classical
  obtain ⟨N, hN⟩ := unram_bound K M
  have hT := Filter.eventually_cofinite.1 hI
  have hR : {p : HeightOneSpectrum (𝓞 K) | ((N.factorial : ℕ) : 𝓞 K) ∈ p.asIdeal}.Finite := by
    have h0 : Ideal.span {((N.factorial : ℕ) : 𝓞 K)} ≠ 0 := by
      rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Nat.factorial_pos N).ne'
    exact (Ideal.finite_factors h0).subset fun p hp => Ideal.dvd_span_singleton.2 hp
  have hF := hR.union (hT.image fun w => w.under (𝓞 K))
  refine ⟨hF.toFinset, fun w hw => ?_⟩
  rw [Set.Finite.mem_toFinset] at hw
  have hgood := not_not.1 fun h => hw (Or.inr ⟨w, h, rfl⟩)
  have he := hN w fun h => hw (Or.inl h)
  by_cases hs : ∃ w' : HeightOneSpectrum (𝓞 M), w' ≠ w ∧ w'.under (𝓞 K) = w.under (𝓞 K)
  · obtain ⟨w', hne, hu⟩ := hs
    left
    refine ⟨?_, w', hne, hu, hgood.1 w' hne hu⟩
    rw [absNorm_pow (K := K) w, f_one hE hne hu, pow_one]
  · push_neg at hs
    have honly : ∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 K) = w.under (𝓞 K) → w' = w :=
      fun w' hu => by_contra fun hne => hs w' hne hu
    have hN2 : Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ 2 := by
      rw [absNorm_pow (K := K) w, f_two hE w honly he]
    right
    refine ⟨hN2, hgood.2 ?_⟩
    rw [normV_absNorm, normV_absNorm, hN2]

end Primes

section Main

open Classical in

private def pick {X : Type} (sat : X → Multiset ℂˣ → Prop) (w : X) : Multiset ℂˣ :=
  if h : ∃ B, sat w B then h.choose else 0

private theorem pick_spec {X : Type} {sat : X → Multiset ℂˣ → Prop} {w : X} {B : Multiset ℂˣ} (h : sat w B) :
    sat w (pick sat w) := by
  have h' : ∃ B, sat w B := ⟨B, h⟩
  rw [pick, dif_pos h']
  exact h'.choose_spec

private theorem sat_unique {F : Type} [Field F] [NumberField F] [IsTotallyComplex F] {n : ℕ} (σ : CuspSub F n)
    {w : HeightOneSpectrum (𝓞 F)} {B B' : Multiset ℂˣ} (h : (CG.mk σ).HasSat w B) (h' : (CG.mk σ).HasSat w B') : B = B' :=
  GlobalTheory.LFun.HasSatGL.unique ((CG.hasSat_mk σ w B).1 h) ((CG.hasSat_mk σ w B').1 h')

private theorem sat_card {F : Type} [Field F] [NumberField F] [IsTotallyComplex F] {n : ℕ} (σ : CuspSub F n)
    {w : HeightOneSpectrum (𝓞 F)} {B : Multiset ℂˣ} (h : (CG.mk σ).HasSat w B) : Multiset.card B = n :=
  GlobalTheory.LFun.HasSatGL.card ((CG.hasSat_mk σ w B).1 h)

private theorem bound_cx {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) {B : Multiset ℂˣ} {c₀ c : ℝ}
    (hc : c₀ ≤ c) (hb : ∀ b ∈ B, ‖(b : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ c₀ ∧
      ‖((b⁻¹ : ℂˣ) : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ c₀) :
    ∀ b ∈ B.map (fun b : ℂˣ => (b : ℂ)), ‖b‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ c ∧ ‖b⁻¹‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ c := by
  have hN : (1 : ℝ) ≤ (Ideal.absNorm w.asIdeal : ℝ) := by
    have : Ideal.absNorm w.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have hmono : (Ideal.absNorm w.asIdeal : ℝ) ^ c₀ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ c :=
    Real.rpow_le_rpow_of_exponent_le hN hc
  intro b hb'
  obtain ⟨b₀, hb₀, rfl⟩ := Multiset.mem_map.1 hb'
  obtain ⟨h1, h2⟩ := hb b₀ hb₀
  refine ⟨h1.trans hmono, ?_⟩
  have : ((b₀ : ℂ))⁻¹ = ((b₀⁻¹ : ℂˣ) : ℂ) := (Units.val_inv_eq_inv_val b₀).symm
  rw [this]
  exact h2.trans hmono

end Main

end UpperTheory.V.Z.Inf
