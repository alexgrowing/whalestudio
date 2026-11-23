import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitVM
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitVA

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex Module

noncomputable section

variable {E : Type} [Field E] [NumberField E]

section Emb

theorem trace_sum_emb (z : E) : ((Algebra.trace ℚ E z : ℚ) : ℂ) = ∑ σ : E →+* ℂ, σ z := by
  have h := trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ) (x := z)
  rw [eq_ratCast] at h
  rw [h]
  exact Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun σ => rfl)

theorem norm_prod_emb (z : E) : ((Algebra.norm ℚ z : ℚ) : ℂ) = ∏ σ : E →+* ℂ, σ z := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ z
  rw [eq_ratCast] at h
  rw [h]
  exact Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun σ => rfl)

end Emb

section Coord
variable {dim : (E →+* ℂ) → ℕ}

def pN (ξ : Vsp dim) (σ : E →+* ℂ) : ℝ := ∑ a : Fin (dim σ), ‖ξ ⟨σ, a⟩‖ ^ 2

def nS (ξ : Vsp dim) (σ : E →+* ℂ) : ℝ := pN ξ σ + pN ξ (ComplexEmbedding.conjugate σ)

theorem pN_nonneg (ξ : Vsp dim) (σ : E →+* ℂ) : 0 ≤ pN ξ σ :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem nS_conj (ξ : Vsp dim) (σ : E →+* ℂ) : nS ξ (ComplexEmbedding.conjugate σ) = nS ξ σ := by
  rw [nS, nS, ComplexEmbedding.involutive_conjugate (K := E) σ, add_comm]

theorem norm_sq_sum_pN (ξ : Vsp dim) : ‖ξ‖ ^ 2 = ∑ σ, pN ξ σ := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_sigma]
  rfl

theorem nS_le [IsTotallyComplex E] (ξ : Vsp dim) (σ : E →+* ℂ) : nS ξ σ ≤ ‖ξ‖ ^ 2 := by
  classical
  rw [norm_sq_sum_pN, nS]
  have hne : ComplexEmbedding.conjugate σ ≠ σ := conjugate_ne σ
  rw [← Finset.sum_pair hne.symm]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun τ _ _ => pN_nonneg ξ τ)

def hA (x ξ : Vsp dim) (σ : E →+* ℂ) : ℂ := ∑ a : Fin (dim σ), x ⟨σ, a⟩ * (starRingEnd ℂ) (ξ ⟨σ, a⟩)

theorem im_Hf_act (x ξ : Vsp dim) (β : 𝓞 E) :
    ((Hf x (act β ξ)).im : ℂ) =
      ∑ σ, σ (β : E) * ((hA x ξ (ComplexEmbedding.conjugate σ) - (starRingEnd ℂ) (hA x ξ σ)) / (2 * I)) := by
  have hZ : Hf x (act β ξ) = ∑ σ, (starRingEnd ℂ) (σ (β : E)) * hA x ξ σ := by
    simp only [Hf, act, hA, Fintype.sum_sigma, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun a _ => ?_
    simp only [PiLp.toLp_apply, map_mul]
    ring
  have hre : ∑ σ, σ (β : E) * hA x ξ (ComplexEmbedding.conjugate σ) =
      ∑ σ, (starRingEnd ℂ) (σ (β : E)) * hA x ξ σ := by
    refine Fintype.sum_equiv (ComplexEmbedding.involutive_conjugate (K := E)).toPerm _ _ (fun σ => ?_)
    simp only [Function.Involutive.coe_toPerm, ComplexEmbedding.involutive_conjugate (K := E) σ,
      ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
  rw [hZ, Complex.im_eq_sub_conj, map_sum]
  simp only [map_mul, Complex.conj_conj, mul_sub, mul_div_assoc', Finset.sum_div, Finset.sum_sub_distrib]
  rw [← hre]
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_div]

theorem emb_dual (x ξ : Vsp dim) (y : E)
    (hy : ∀ β : 𝓞 E, ((Algebra.trace ℚ E ((β : E) * y) : ℚ) : ℝ) = (Hf x (act β ξ)).im) (σ : E →+* ℂ) :
    σ y = (hA x ξ (ComplexEmbedding.conjugate σ) - (starRingEnd ℂ) (hA x ξ σ)) / (2 * I) := by
  have h := emb_indep (fun σ => σ y -
      (hA x ξ (ComplexEmbedding.conjugate σ) - (starRingEnd ℂ) (hA x ξ σ)) / (2 * I)) (fun β => by
    have h1 := congrArg (fun r : ℝ => (r : ℂ)) (hy β)
    simp only [Complex.ofReal_ratCast] at h1
    rw [trace_sum_emb, im_Hf_act] at h1
    simp only [map_mul] at h1
    simp only [mul_sub, Finset.sum_sub_distrib, h1, sub_self])
  have := congrFun h σ
  simpa [sub_eq_zero] using this

theorem emb_dual_zero (x ξ : Vsp dim) (y : E)
    (hy : ∀ β : 𝓞 E, ((Algebra.trace ℚ E ((β : E) * y) : ℚ) : ℝ) = (Hf x (act β ξ)).im) (σ : E →+* ℂ)
    (hn : nS ξ σ = 0) : σ y = 0 := by
  have h1 : pN ξ σ = 0 := by
    have := pN_nonneg ξ σ; have := pN_nonneg ξ (ComplexEmbedding.conjugate σ); rw [nS] at hn; linarith
  have h2 : pN ξ (ComplexEmbedding.conjugate σ) = 0 := by
    have := pN_nonneg ξ σ; have := pN_nonneg ξ (ComplexEmbedding.conjugate σ); rw [nS] at hn; linarith
  have hz : ∀ τ, pN ξ τ = 0 → hA x ξ τ = 0 := by
    intro τ hτ
    have : ∀ a, ξ ⟨τ, a⟩ = 0 := by
      intro a
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => by positivity)).1 hτ a (Finset.mem_univ a)
      simpa using h
    simp [hA, this]
  rw [emb_dual x ξ y hy σ, hz _ h2, hz _ h1]
  simp

def actT (t : (E →+* ℂ) → ℂ) (v : Vsp dim) : Vsp dim := WithLp.toLp 2 fun i => t i.1 * v i

theorem act_eq_actT (β : 𝓞 E) (v : Vsp dim) : act β v = actT (canonicalEmbedding E (β : E)) v := rfl

theorem actT_sum {ι : Type} (s : Finset ι) (c : ι → ℝ) (t : ι → (E →+* ℂ) → ℂ) (v : Vsp dim) :
    actT (∑ k ∈ s, c k • t k) v = ∑ k ∈ s, c k • actT (t k) v := by
  ext i
  simp [actT, Finset.sum_mul, Complex.real_smul, mul_assoc]

theorem norm_actT_sq (t : (E →+* ℂ) → ℂ) (v : Vsp dim) :
    ‖actT t v‖ ^ 2 = ∑ σ, ‖t σ‖ ^ 2 * pN v σ := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [pN, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [actT, norm_mul, mul_pow]

end Coord

section CS
variable {dim : (E →+* ℂ) → ℕ}

theorem cs_bound [IsCMField E] (I : Submodule ℤ (Vsp dim))
    (hst : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I) {ξ : Vsp dim} (hξ : ξ ∈ I) (x u : Vsp dim)
    (hu : IsU I x u) (y : E)
    (hy : ∀ β : 𝓞 E, ((Algebra.trace ℚ E ((β : E) * y) : ℚ) : ℝ) = (Hf x (act β ξ)).im) :
    2 * ∑ σ : E →+* ℂ, ‖σ y‖ ^ 2 ≤ ‖ξ‖ ^ 2 * ‖u‖ ^ 2 := by
  classical
  set t : (E →+* ℂ) → ℂ := fun σ =>
    if nS ξ σ = 0 then 0 else (starRingEnd ℂ) (σ y) / (nS ξ σ : ℂ) with htdef
  have ht : ConjSymm t := by
    intro σ
    simp only [htdef, nS_conj, ComplexEmbedding.conjugate_coe_eq]
    split_ifs
    · simp
    · rw [map_div₀, Complex.conj_ofReal]
  obtain ⟨c, hc⟩ := real_span t ht
  set β : Free.ChooseBasisIndex ℤ (𝓞 E) → 𝓞 E := fun k => RingOfIntegers.basis E k
  have hβ : ∀ k, canonicalEmbedding E (integralBasis E k) = canonicalEmbedding E ((β k : 𝓞 E) : E) :=
    fun k => by rw [integralBasis_apply]
  set b := actT t ξ with hbdef
  have hb : b = ∑ k, c k • act (β k) ξ := by
    rw [hbdef, hc, actT_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hβ, ← act_eq_actT]
  have hactI : ∀ k, act (β k) ξ ∈ IR I := fun k => Submodule.subset_span (hst _ _ hξ)
  set S : ℝ := ∑ σ, if nS ξ σ = 0 then 0 else ‖σ y‖ ^ 2 / nS ξ σ with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun σ _ => by
    split_ifs with h
    · exact le_refl _
    · exact div_nonneg (by positivity) (by
        have := pN_nonneg ξ σ; have := pN_nonneg ξ (ComplexEmbedding.conjugate σ); rw [nS]; linarith)
  have hub : inner ℝ u b = S := by
    have e1 : inner ℝ u b = ∑ k, c k * ((Algebra.trace ℚ E ((β k : E) * y) : ℚ) : ℝ) := by
      rw [hb, inner_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [real_inner_smul_right, hu.2 _ (hactI k), hy]
    rw [e1]
    apply Complex.ofReal_injective
    push_cast
    simp only [trace_sum_emb, map_mul, Finset.mul_sum]
    rw [Finset.sum_comm, hSdef]
    push_cast
    refine Finset.sum_congr rfl fun σ _ => ?_
    have htσ : t σ = ∑ k, (c k : ℂ) * σ ((β k : 𝓞 E) : E) := by
      have := congrFun hc σ
      rw [Finset.sum_apply] at this
      rw [this]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Pi.smul_apply, hβ, canonicalEmbedding.apply_at, Complex.real_smul]
    have e2 : ∑ k, (c k : ℂ) * (σ ((β k : 𝓞 E) : E) * σ y) = t σ * σ y := by
      rw [htσ, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e2, htdef]
    simp only
    split_ifs with h
    · simp
    · rw [div_mul_eq_mul_div, Complex.conj_mul', Complex.ofReal_div]
      push_cast
      ring
  have hbb : ‖b‖ ^ 2 = S / 2 := by
    rw [hbdef, norm_actT_sq]
    have hF : ∀ σ, ‖t σ‖ ^ 2 = if nS ξ σ = 0 then 0 else ‖σ y‖ ^ 2 / nS ξ σ ^ 2 := by
      intro σ
      simp only [htdef]
      split_ifs with h
      · simp
      · rw [norm_div, Complex.norm_conj, div_pow]
        congr 1
        rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hsym : ∑ σ, ‖t σ‖ ^ 2 * pN ξ σ = ∑ σ, ‖t σ‖ ^ 2 * pN ξ (ComplexEmbedding.conjugate σ) := by
      refine Fintype.sum_equiv (ComplexEmbedding.involutive_conjugate (K := E)).toPerm _ _ (fun σ => ?_)
      simp only [Function.Involutive.coe_toPerm, ComplexEmbedding.involutive_conjugate (K := E) σ]
      rw [hF, hF, nS_conj, ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]
    have h2 : 2 * ∑ σ, ‖t σ‖ ^ 2 * pN ξ σ = S := by
      rw [two_mul]
      nth_rewrite 2 [hsym]
      rw [← Finset.sum_add_distrib, hSdef]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [← mul_add, hF]
      split_ifs with h
      · simp
      · rw [show pN ξ σ + pN ξ (ComplexEmbedding.conjugate σ) = nS ξ σ from rfl]
        field_simp
    linarith
  have hS2 : 2 * S ≤ ‖u‖ ^ 2 := by
    have hcs : S ≤ ‖u‖ * ‖b‖ := hub ▸ real_inner_le_norm u b
    rcases hS0.lt_or_eq with hpos | hzero
    · have h3 : S ^ 2 ≤ ‖u‖ ^ 2 * ‖b‖ ^ 2 := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ hS0 hcs 2
      rw [hbb] at h3
      nlinarith
    · rw [← hzero]
      have := sq_nonneg ‖u‖
      linarith
  by_cases hξ0 : ‖ξ‖ = 0
  · have hz : ∀ σ : E →+* ℂ, σ y = 0 := by
      intro σ
      apply emb_dual_zero x ξ y hy σ
      have h1 := nS_le ξ σ
      rw [hξ0] at h1
      have h2 : 0 ≤ nS ξ σ := by
        have := pN_nonneg ξ σ; have := pN_nonneg ξ (ComplexEmbedding.conjugate σ); unfold nS; linarith
      have h3 : nS ξ σ ≤ 0 := by simpa using h1
      exact le_antisymm h3 h2
    simp [hz]
    positivity
  · have hpos : 0 < ‖ξ‖ ^ 2 := by positivity
    have hlow : ∑ σ : E →+* ℂ, ‖σ y‖ ^ 2 / ‖ξ‖ ^ 2 ≤ S := by
      rw [hSdef]
      refine Finset.sum_le_sum fun σ _ => ?_
      split_ifs with h
      · rw [emb_dual_zero x ξ y hy σ h]
        simp
      · have hn : 0 < nS ξ σ := lt_of_le_of_ne (by
          have := pN_nonneg ξ σ; have := pN_nonneg ξ (ComplexEmbedding.conjugate σ); rw [nS]; linarith)
          (Ne.symm h)
        exact div_le_div_of_nonneg_left (by positivity) hn (nS_le ξ σ)
    rw [← Finset.sum_div] at hlow
    have := (div_le_iff₀ hpos).1 hlow
    nlinarith

end CS

end

end ReciprocityTheory.ChartRestriction.G.I2
