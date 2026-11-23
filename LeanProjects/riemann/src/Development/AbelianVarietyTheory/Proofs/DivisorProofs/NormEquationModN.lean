import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOntoOfLeRadical

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.NormSurjMod

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem host_bar_bar (H : Host E) (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply Subtype.ext
  show ((H.bar (H.bar a) : 𝓞 E) : E) = (a : E)
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

theorem host_bar_rt (H : Host E) : H.bar H.rt = -H.rt := by
  have h1 : H.bar H.rt ^ 2 = H.rt ^ 2 := by
    rw [← map_pow, H.rt_sq, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with e | e
  · exfalso
    have e' : IsCMField.complexConj E (H.rt : E) = H.rt := by rw [← H.bar_eq, e]
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have c := IsCMField.complexEmbedding_complexConj E φ (H.rt : E)
    rw [e'] at c
    have r : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
      have := congrArg (fun z : 𝓞 E => φ (z : E)) H.rt_sq
      simpa using this
    obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 c.symm
    rw [hx] at r
    have r' : x ^ 2 = -(H.d : ℝ) := by exact_mod_cast r
    have : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    nlinarith [sq_nonneg x]
  · exact e

theorem host_base_element_add_conj (H : Host E) : H.w0 + H.bar H.w0 = 1 := by
  have h2 : 2 * H.bar H.w0 = 1 + H.bar H.rt := by
    have := congrArg H.bar H.two_weight_eq_one_add_root
    simpa [map_ofNat] using this
  rw [host_bar_rt] at h2
  have h3 : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by
    rw [mul_add, h2, H.two_weight_eq_one_add_root]; ring
  exact mul_left_cancel₀ two_ne_zero h3

theorem exists_bar_sub_notMem (H : Host E) (I : Ideal (𝓞 E)) (hI : I ≠ ⊤) : ∃ b, H.bar b - b ∉ I := by
  haveI := H.unram
  by_contra hn
  push_neg at hn
  let g : 𝓞 E →ₐ[𝓞 (maximalRealSubfield E)] 𝓞 E :=
    { (H.bar : 𝓞 E →+* 𝓞 E) with
      commutes' := fun r => by
        apply Subtype.ext
        show ((H.bar (algebraMap _ (𝓞 E) r) : 𝓞 E) : E) = ((algebraMap _ (𝓞 E) r : 𝓞 E) : E)
        rw [H.bar_eq]
        exact IsCMField.complexConj_apply_eq_self E (r : maximalRealSubfield E) }
  have hg : ∀ x, g x = H.bar x := fun x => rfl
  have h := Algebra.FormallyUnramified.ext_of_iInf (R := 𝓞 (maximalRealSubfield E)) I
    (Ideal.iInf_pow_eq_bot_of_isDomain I hI) (g₁ := AlgHom.id _ (𝓞 E)) (g₂ := g)
    (fun x => Ideal.Quotient.eq.2 (by
      rw [AlgHom.id_apply, hg, ← neg_sub]
      exact I.neg_mem (hn x)))
  have hrt : H.bar H.rt = H.rt := by rw [← hg, ← h]; rfl
  rw [host_bar_rt] at hrt
  have h0 : H.rt = 0 := by
    have : (2 : 𝓞 E) * H.rt = 0 := by linear_combination -hrt
    exact (mul_eq_zero.1 this).resolve_left two_ne_zero
  have hd := H.rt_sq
  rw [h0, zero_pow two_ne_zero, eq_comm, neg_eq_zero, Nat.cast_eq_zero] at hd
  exact H.d_prime.ne_zero hd

theorem normOnto_span_nat (H : Host E) (N : ℕ) (hN : 0 < N) :
    NormOnto (H.bar : 𝓞 E →+* 𝓞 E) (Ideal.span {(N : 𝓞 E)}) := by
  classical
  set σ : 𝓞 E →+* 𝓞 E := (H.bar : 𝓞 E →+* 𝓞 E) with hσdef
  have hσa : ∀ a, σ a = H.bar a := fun a => rfl
  have hσ : ∀ a, σ (σ a) = a := fun a => host_bar_bar H a
  have hw : H.w0 + σ H.w0 = 1 := host_base_element_add_conj H
  set I : Ideal (𝓞 E) := Ideal.span {(N : 𝓞 E)} with hIdef
  have hIstab : ∀ a ∈ I, σ a ∈ I := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    exact Ideal.mem_span_singleton'.2 ⟨σ b, by rw [map_mul, map_natCast]⟩
  have hI0 : I ≠ ⊥ := by
    rw [hIdef, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  have hfinP := Ideal.finite_minimalPrimes_of_isNoetherianRing (𝓞 E) I
  set s := hfinP.toFinset with hs
  have hPs : ∀ P ∈ s, P.IsPrime ∧ I ≤ P := fun P hP => ((hfinP.mem_toFinset).1 hP).1
  have hmax : ∀ P ∈ s, P.IsMaximal := fun P hP =>
    (hPs P hP).1.isMaximal (fun h0 => hI0 (le_bot_iff.1 (h0 ▸ (hPs P hP).2)))
  have hloc : ∀ P ∈ s, NormOnto σ (P ⊓ P.comap σ) := by
    intro P hP
    have hPm := hmax P hP
    have hsurj : Function.Surjective σ := fun a => ⟨σ a, hσ a⟩
    by_cases hst : P.comap σ = P
    · rw [hst, inf_idem]
      have hPne : P ≠ ⊥ := fun h0 => hI0 (le_bot_iff.1 (h0 ▸ (hPs P hP).2))
      obtain ⟨b, hb⟩ := exists_bar_sub_notMem H P hPm.ne_top
      exact normOnto_inert σ hσ P hPm (Ideal.finiteQuotientOfFreeOfNeBot P hPne) hst ⟨b, hb⟩
    · exact normOnto_split σ hσ P hPm (Ideal.comap_isMaximal_of_surjective σ hsurj) hst
  set K := s.inf fun P => P ⊓ P.comap σ with hK
  have hKn : NormOnto σ K := normOnto_finset_inf σ hσ s hmax hloc
  have hKstab : ∀ a ∈ K, σ a ∈ K := by
    intro a ha
    rw [hK, Submodule.mem_finsetInf] at ha ⊢
    exact fun P hP => stable_inf_comap σ hσ P a (ha P hP)
  have hIK : I ≤ K := by
    intro a ha
    rw [hK, Submodule.mem_finsetInf]
    intro P hP
    exact Ideal.mem_inf.2 ⟨(hPs P hP).2 ha, Ideal.mem_comap.2 ((hPs P hP).2 (hIstab a ha))⟩
  have hKrad : K ≤ I.radical := by
    rw [← Ideal.sInf_minimalPrimes]
    refine le_sInf fun P hP => ?_
    have hP' : P ∈ s := hfinP.mem_toFinset.2 hP
    exact le_trans (Finset.inf_le (f := fun P : Ideal (𝓞 E) => P ⊓ P.comap σ) hP') inf_le_left
  obtain ⟨m, hm⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hKrad (IsNoetherian.noetherian K)
  have hpow := normOnto_pow σ H.w0 hσ hw K hKstab hKn (m + 1) (by omega)
  refine normOnto_of_le_radical σ (K ^ (m + 1)) I
    (le_trans (Ideal.pow_le_pow_right (Nat.le_succ m)) hm) ?_ hpow
  rw [Ideal.radical_pow K (Nat.succ_ne_zero m)]
  exact le_trans hIK Ideal.le_radical

theorem exists_mul_bar_sub_eq_nsmul : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (N : ℕ),
    0 < N → ∀ u : 𝓞 E, (∃ b : 𝓞 E, H.bar u - u = N • b) → (∃ v b : 𝓞 E, u * v - 1 = N • b) →
      ∃ x b : 𝓞 E, x * H.bar x - u = N • b := by
  intro E _ _ _ H N hN u ⟨b0, hb0⟩ ⟨v, b1, hb1⟩
  have memI : ∀ y : 𝓞 E, y ∈ Ideal.span {(N : 𝓞 E)} ↔ ∃ b : 𝓞 E, y = N • b := fun y => by
    rw [Ideal.mem_span_singleton']
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨a, by rw [nsmul_eq_mul, mul_comm]⟩
    · rintro ⟨a, rfl⟩; exact ⟨a, by rw [nsmul_eq_mul, mul_comm]⟩
  have hw := host_base_element_add_conj H
  have hσ := host_bar_bar H
  set u' := H.w0 * u + H.bar (H.w0 * u) with hu'
  have hfix : (H.bar : 𝓞 E →+* 𝓞 E) u' = u' := by
    show H.bar u' = u'
    rw [hu', map_add, hσ, add_comm]
  have hdiff : u' - u = H.bar H.w0 * (N • b0) := by
    rw [hu', map_mul, ← hb0]
    linear_combination u * hw
  have hunit : u' * v - 1 ∈ Ideal.span {(N : 𝓞 E)} := by
    have : u' * v - 1 = (u' - u) * v + (u * v - 1) := by ring
    rw [this, hdiff, hb1]
    refine (memI _).2 ⟨H.bar H.w0 * b0 * v + b1, ?_⟩
    simp only [nsmul_eq_mul]; ring
  obtain ⟨x, hx⟩ := normOnto_span_nat H N hN u' hfix ⟨v, hunit⟩
  obtain ⟨b, hb⟩ := (memI _).1 hx
  refine ⟨x, b + H.bar H.w0 * b0, ?_⟩
  have hx' : x * H.bar x - u' = N • b := hb
  have : x * H.bar x - u = (x * H.bar x - u') + (u' - u) := by ring
  rw [this, hx', hdiff]
  simp only [nsmul_eq_mul]; ring

end GlobalTheory.NormSurjMod
