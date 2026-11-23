import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMTypeEmbeddings.EmbMemCmType

noncomputable section

open NumberField Formalism.L2.Host Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace PI.HostPsiFactsWork

variable {R : Ranks}

theorem phi_sqrt_neg_discriminant (H : Host R) :
    H.φ₀ (H.sqd) = Complex.I * (Real.sqrt (H.d : ℝ) : ℂ) := H.φ₀_mem

theorem host_sqd_ne_zero (H : Host R) : H.sqd ≠ 0 := by
  intro h0
  have hm := phi_sqrt_neg_discriminant H
  rw [h0, map_zero] at hm
  have hd : (0 : ℝ) < Real.sqrt (H.d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast H.hyp.2.1.pos)
  rcases mul_eq_zero.1 hm.symm with h | h
  · exact Complex.I_ne_zero h
  · exact hd.ne' (by exact_mod_cast h)

theorem conj_conj (H : Host R) (x : H.E) :
    H.conj (H.conj x) = x := by
  apply H.φ₀.injective
  rw [H.conjE_apply, H.conjE_apply, Complex.conj_conj]

theorem conj_bE (H : Host R) :
    H.conj (H.sqd) = - H.sqd := by
  apply H.φ₀.injective
  rw [H.conjE_apply, map_neg, phi_sqrt_neg_discriminant, map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem eq_of_cm_of_agree (H : Host R) (φ ψ : H.E →+* ℂ)
    (hφ : φ ∈ H.cmType) (hψ : ψ ∈ H.cmType)
    (hF : ∀ x ∈ H.F, φ x = ψ x) : φ = ψ := by
  have hb0 := host_sqd_ne_zero H
  have hcb := conj_bE H
  have hcc := conj_conj H
  set c := H.conj with hc
  set b := H.sqd with hb
  ext x
  have hu : (x + c x) / 2 ∈ H.F := by
    apply (H.conjE_mem_hostF_iff _).2
    rw [← hc, map_div₀, map_add, hcc, map_ofNat]
    ring
  have hv : (x - c x) / (2 * b) ∈ H.F := by
    apply (H.conjE_mem_hostF_iff _).2
    rw [← hc, map_div₀, map_sub, map_mul, hcc, map_ofNat, hcb, mul_neg, div_neg, ← neg_div,
      neg_sub]
  have hx : x = (x + c x) / 2 + (x - c x) / (2 * b) * b := by
    rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hb0]
    ring
  have hφb : φ b = Complex.I * (Real.sqrt (H.d : ℝ) : ℂ) := hφ
  have hψb : ψ b = Complex.I * (Real.sqrt (H.d : ℝ) : ℂ) := hψ
  rw [hx, map_add, map_add, map_mul, map_mul, hF _ hu, hF _ hv, hφb, hψb]

theorem agree_of_comap (H : Host R) (φ ψ : H.E →+* ℂ)
    (h : (InfinitePlace.mk φ).comap (algebraMap H.F H.E) =
      (InfinitePlace.mk ψ).comap (algebraMap H.F H.E)) :
    ∀ x ∈ H.F, φ x = ψ x := by
  rw [InfinitePlace.comap_mk, InfinitePlace.comap_mk, InfinitePlace.mk_eq_iff] at h
  intro x hx
  rcases h with h | h
  · exact RingHom.congr_fun h ⟨x, hx⟩
  · have h1 := RingHom.congr_fun h ⟨x, hx⟩
    rw [ComplexEmbedding.conjugate_coe_eq] at h1
    have hr : star (φ x) = φ x := (show ∀ f : H.E →+* ℂ, star (f x) = f x from hx) φ
    change starRingEnd ℂ (φ x) = ψ x at h1
    rw [starRingEnd_apply, hr] at h1
    exact h1

theorem mk_conj_comp (H : Host R) (φ : H.E →+* ℂ) :
    InfinitePlace.mk ((starRingEnd ℂ).comp φ) = InfinitePlace.mk φ := by
  have : (starRingEnd ℂ).comp φ = ComplexEmbedding.conjugate φ := by
    ext x; rfl
  rw [this, InfinitePlace.mk_conjugate_eq]

open Classical in
theorem onePsi : PI.EtaHostFacts.OnePsi := by
  intro _hc he R H w
  have hcm := H.der.cmType
  have : Algebra.IsAlgebraic H.F H.E := inferInstance
  obtain ⟨w', hw'⟩ := InfinitePlace.comap_surjective (k := H.F) (K := H.E) w

  obtain ⟨φ, hφcm, hφw⟩ : ∃ φ : H.E →+* ℂ, φ ∈ H.cmType ∧
      InfinitePlace.mk φ = w' := by
    by_cases h0 : w'.embedding ∈ H.cmType
    · exact ⟨w'.embedding, h0, InfinitePlace.mk_embedding w'⟩
    · refine ⟨(starRingEnd ℂ).comp w'.embedding, ?_, ?_⟩
      · by_contra h1
        exact h0 ((hcm.1 _).2 h1)
      · rw [mk_conj_comp H, InfinitePlace.mk_embedding]
  obtain ⟨g, hg⟩ := (he R H).1.2 φ
  have hgPsi : g ∈ R.Psi := ((he R H).2 g).1 (hg ▸ hφcm)
  rw [Finset.card_eq_one]
  refine ⟨⟨g, hgPsi⟩, Finset.eq_singleton_iff_unique_mem.2 ⟨?_, ?_⟩⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, aboveInf]
    rw [hg, hφw]
    exact hw'
  · rintro ⟨i, hi⟩ hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, aboveInf] at hmem
    have hagree := agree_of_comap H (H.emb i) φ (by rw [hmem, hφw]; exact hw'.symm)
    have heq := eq_of_cm_of_agree H (H.emb i) φ (emb_mem_cmType H i hi) hφcm hagree
    rw [← hg] at heq
    exact Subtype.ext ((he R H).1.1 heq)

end PI.HostPsiFactsWork
