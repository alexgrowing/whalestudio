import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.CMFormBound

section Val

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [Field K] [Algebra O K]
  [IsFractionRing O K]

theorem ord_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : ord_vw O (x * y) = ord_vw O x + ord_vw O y := by
  have hx' : (IsDiscreteValuationRing.maximalIdeal O).valuation K x ≠ 0 := by simpa using hx
  have hy' : (IsDiscreteValuationRing.maximalIdeal O).valuation K y ≠ 0 := by simpa using hy
  unfold ord_vw
  rw [map_mul, WithZero.log_mul hx' hy']
  ring

theorem ord_of_not_mem (x : O) (hx : x ∉ IsLocalRing.maximalIdeal O) : ord_vw O (algebraMap O K x) = 0 := by
  have h1 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (algebraMap O K x) = 1 :=
    le_antisymm ((IsDiscreteValuationRing.maximalIdeal O).valuation_le_one x)
      (not_lt.1 fun h => hx (((IsDiscreteValuationRing.maximalIdeal O).valuation_lt_one_iff_mem x).1 h))
  unfold ord_vw
  rw [h1, WithZero.log_one, neg_zero]

theorem ord_natCast_ne [CharZero O] (l : ℕ) (hl : l ≠ 0) (h : (l : O) ∈ IsLocalRing.maximalIdeal O) : ord_vw O (l : K) ≠ 0 := by
  have h0 : (l : K) ≠ 0 := by
    rw [← map_natCast (algebraMap O K)]
    exact (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 (Nat.cast_ne_zero.2 hl)
  have h1 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (l : K) < 1 := by
    rw [← map_natCast (algebraMap O K), HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact h
  have h2 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (l : K) ≠ 0 := by simpa using h0
  unfold ord_vw
  intro h4
  have := WithZero.exp_log h2
  rw [neg_eq_zero.1 h4, WithZero.exp_zero] at this
  exact h1.ne this.symm

theorem val_of_ne (l : ℕ) {x : K} (hx : x ≠ 0) :
    val_vp O l x = (((ord_vw O x : ℚ) / (ord_vw O (l : K) : ℚ) : ℚ) : WithTop ℚ) := by
  rw [val_vp, if_neg hx]

theorem val_mul (l : ℕ) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    val_vp O l (x * y) = val_vp O l x + val_vp O l y := by
  rw [val_of_ne O l hx, val_of_ne O l hy, val_of_ne O l (mul_ne_zero hx hy), ord_mul O hx hy,
    ← WithTop.coe_add]
  congr 1
  push_cast
  ring

end Val

theorem conj_sqrt (E : Type) [Field E] [NumberField E] [IsCMField E] (d : ℕ) (hd : d.Prime) (r : E)
    (hr : r ^ 2 = -(d : E)) : IsCMField.complexConj E r = -r := by
  have h1 : (IsCMField.complexConj E r) ^ 2 = r ^ 2 := by
    rw [← map_pow, hr, map_neg, map_natCast]
  have hne : IsCMField.complexConj E r ≠ r := by
    intro h
    let ψ : E →+* ℂ := Classical.choice inferInstance
    have h2 : conj (ψ r) = ψ r := by rw [← IsCMField.complexEmbedding_complexConj, h]
    have h3 : (ψ r) ^ 2 = -(d : ℂ) := by rw [← map_pow, hr, map_neg, map_natCast]
    obtain ⟨x, hx⟩ : ∃ x : ℝ, (x : ℂ) = ψ r := ⟨(ψ r).re, Complex.conj_eq_iff_re.1 h2⟩
    rw [← hx] at h3
    have h4 : x ^ 2 = -(d : ℝ) := by exact_mod_cast h3
    have h5 : (0 : ℝ) < d := by exact_mod_cast hd.pos
    nlinarith [sq_nonneg x]
  have h6 : (IsCMField.complexConj E r - r) * (IsCMField.complexConj E r + r) = 0 := by
    linear_combination h1
  rcases mul_eq_zero.1 h6 with h | h
  · exact absurd (sub_eq_zero.1 h) hne
  · exact eq_neg_of_add_eq_zero_left h

theorem eig_ext {E : Type} [Field E] [NumberField E] [IsCMField E] {c : Ideal (OF E)} (hc : c ≠ ⊥)
    {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K] {H : Type} [AddCommGroup H] [Module O H]
    (ρ : orderC c →+* Module.End O H) (ρE : E →+* Module.End K (K ⊗[O] H))
    (hρE : ∀ a : orderC c, ρE a = (ρ a).baseChange K) (σ : E →+* K) (v : K ⊗[O] H) (hv : v ∈ eigK ρ σ)
    (a : E) : ρE a v = σ a • v := by
  have hS : ∀ b ∈ orderC c, ρE b v = σ b • v := by
    intro b hb
    have := Module.End.mem_eigenspace_iff.1 (Submodule.mem_iInf _ |>.1 hv ⟨b, hb⟩)
    rw [show b = ((⟨b, hb⟩ : orderC c) : E) from rfl, hρE]
    exact this
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 E) a
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  set N := algebraMap (OF E) (𝓞 E) n with hN
  have hmem : ∀ z : 𝓞 E, algebraMap (𝓞 E) E (N * z) ∈ orderC c := fun z =>
    Subring.subset_closure (Or.inr ⟨N * z, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hn), rfl⟩)
  have hy0 : algebraMap (𝓞 E) E y ≠ 0 := by
    simpa using nonZeroDivisors.ne_zero hy
  have hN0 : algebraMap (𝓞 E) E N ≠ 0 := by
    rw [hN, ← IsScalarTower.algebraMap_apply]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (OF E) E)).2 hn0
  set b := algebraMap (𝓞 E) E (N * y)
  have hb0 : b ≠ 0 := by simp only [b, map_mul]; exact mul_ne_zero hN0 hy0
  have hab : a * b = algebraMap (𝓞 E) E (N * x) := by
    simp only [b, map_mul, ← hxy]
    field_simp
  have h1 := hS b (hmem y)
  have h2 := hS (a * b) (hab ▸ hmem x)
  have h3 : ρE b⁻¹ v = (σ b)⁻¹ • v := by
    have h4 : v = σ b • ρE b⁻¹ v := by
      rw [← map_smul, ← h1, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel₀ hb0, map_one, Module.End.one_apply]
    have hσb : σ b ≠ 0 := (map_ne_zero σ).2 hb0
    conv_rhs => rw [h4, smul_smul, inv_mul_cancel₀ hσb, one_smul]
  have h5 : ρE a = ρE b⁻¹ * ρE (a * b) := by
    rw [← map_mul]; congr 1; field_simp
  rw [h5, Module.End.mul_apply, h2, map_smul, h3, smul_smul, map_mul, mul_assoc,
    mul_inv_cancel₀ ((map_ne_zero σ).2 hb0), mul_one]

end GlobalTheory.CMFormBound

namespace GlobalTheory.CMFormBound

theorem formClaims : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → (∀ i, 0 ≤ val_vp O l (algebraMap O K (B (e i) (f i))) ∧ val_vp O l (algebraMap O K (B (e i) (f i))) ≤ val_vp O l (algebraMap O K D)) → (∃! ρE : E →+* Module.End K (K ⊗[O] H), ∀ a : orderC c, ρE a = (ρ a).baseChange K) → FormClaims l φ ρ B D e f := by
  intro E _ _ _ c hc l hl O _ _ _ _ K _ _ _ hlm hcard D hD hCl I _ φ hφ H _ _ ρ Fil B hLat hEig e f hgens hB hρE
  refine ⟨hρE, ?_⟩
  intro ρE hρE' d r ξ hd hr hξ hξ0 hval
  have hconjr := conj_sqrt E d hd r hr
  have ha_real : IsCMField.complexConj E (ξ * r) = ξ * r := by
    rw [map_mul, hξ, hconjr, neg_mul_neg]
  have hr0 : r ≠ 0 := by
    rintro rfl
    have h0 : (d : E) = 0 := by
      rw [zero_pow two_ne_zero] at hr
      exact neg_eq_zero.1 hr.symm
    exact hd.ne_zero (by exact_mod_cast h0)
  have ha0 : ξ * r ≠ 0 := mul_ne_zero hξ0 hr0
  have hinv : ρE (ξ * r) * ρE (ξ * r)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ ha0, map_one]
  have hinv' : ρE (ξ * r)⁻¹ * ρE (ξ * r) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ ha0, map_one]
  refine ⟨⟨(IsCMField.complexConj_eq_self_iff E (ξ * r)).1 ha_real, ha0⟩, ?_, ?_⟩
  · refine ⟨(B.baseChange K).compl₂ (ρE (ξ * r)), ?_, ?_⟩
    · intro x y
      rw [LinearMap.compl₂_apply, ← Module.End.mul_apply, hinv, Module.End.one_apply]
    · intro BF' hBF'
      refine LinearMap.ext₂ fun x y => ?_
      rw [LinearMap.compl₂_apply, hBF' x (ρE (ξ * r) y), ← Module.End.mul_apply, hinv', Module.End.one_apply]
  · intro BF hBF i
    have hBFxy : ∀ x y, BF x y = B.baseChange K x (ρE (ξ * r) y) := by
      intro x y
      rw [hBF x (ρE (ξ * r) y), ← Module.End.mul_apply, hinv', Module.End.one_apply]
    have hfmem : inK K H (f i) ∈ eigK ρ (bar (φ i)) := by
      have : f i ∈ eigLat ρ (bar (φ i)) := by
        rw [(hgens i).2]
        exact Submodule.mem_span_singleton_self _
      exact this
    have heig := eig_ext hc ρ ρE hρE' (bar (φ i)) _ hfmem (ξ * r)
    have hbar : bar (φ i) (ξ * r) = φ i (ξ * r) := by
      show φ i (IsCMField.complexConj E (ξ * r)) = _
      rw [ha_real]
    have hK : B.baseChange K (inK K H (e i)) (inK K H (f i)) = algebraMap O K (B (e i) (f i)) := by
      simp [inK, LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def]
    have hval1 : BF (inK K H (e i)) (inK K H (f i)) = φ i (ξ * r) * algebraMap O K (B (e i) (f i)) := by
      rw [hBFxy, heig, hbar, LinearMap.map_smul, smul_eq_mul, hK]
    have hD0 : algebraMap O K D ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hD
    have hB0 : algebraMap O K (B (e i) (f i)) ≠ 0 := by
      intro h0
      have h1 := (hB i).2
      rw [h0, val_vp, if_pos rfl, val_of_ne O l hD0, top_le_iff] at h1
      exact WithTop.coe_ne_top h1
    have hφξ : φ i ξ ≠ 0 := (map_ne_zero _).2 hξ0
    have hφr : φ i r ≠ 0 := (map_ne_zero _).2 hr0
    have hF0 : BF (inK K H (e i)) (inK K H (f i)) ≠ 0 := by
      rw [hval1]
      exact mul_ne_zero ((map_ne_zero _).2 ha0) hB0
    have hlne : ord_vw O (l : K) ≠ 0 := ord_natCast_ne O l hl.ne_zero hlm
    have hvr : val_vp O l (φ i r) = (((if l = d then 1 / 2 else 0 : ℚ)) : WithTop ℚ) := by
      have hsq : φ i r * φ i r = -1 * (d : K) := by
        rw [← map_mul, ← sq, hr, map_neg, map_natCast]; ring
      have hdK : (d : K) ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hsq
        exact hφr (mul_self_eq_zero.1 hsq)
      have hm1 : ord_vw O ((-1 : K)) = 0 := by
        have := ord_of_not_mem O (K := K) (-1 : O) (by
          intro h; exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top
            ((Ideal.eq_top_iff_one _).2 (by simpa using (IsLocalRing.maximalIdeal O).neg_mem h)))
        simpa using this
      have hord := congrArg (ord_vw O) hsq
      rw [ord_mul O hφr hφr, ord_mul O (by norm_num) hdK, hm1, zero_add] at hord
      rw [val_of_ne O l hφr]
      by_cases hld : l = d
      · subst hld
        rw [if_pos rfl]
        congr 1
        have : (ord_vw O (φ i r) : ℚ) * 2 = ord_vw O ((l : ℕ) : K) := by exact_mod_cast (by linarith : ord_vw O (φ i r) * 2 = ord_vw O ((l : ℕ) : K))
        have hq : (ord_vw O ((l : ℕ) : K) : ℚ) ≠ 0 := by exact_mod_cast hlne
        field_simp
        linarith
      · rw [if_neg hld]
        have hdu : (d : O) ∉ IsLocalRing.maximalIdeal O := by
          intro hdm
          have hcop : IsCoprime (d : ℤ) (l : ℤ) :=
            Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hd hl).2 (Ne.symm hld))
          obtain ⟨u, w, huw⟩ := hcop
          have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
            have := congrArg (Int.cast : ℤ → O) huw
            push_cast at this
            rw [← this]
            exact add_mem (Ideal.mul_mem_left _ _ hdm) (Ideal.mul_mem_left _ _ hlm)
          exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)
        have hd0 : ord_vw O ((d : ℕ) : K) = 0 := by
          have := ord_of_not_mem O (K := K) (d : O) hdu
          simpa using this
        rw [hd0] at hord
        have : ord_vw O (φ i r) = 0 := by linarith
        rw [this]
        simp
    have hvF : val_vp O l (BF (inK K H (e i)) (inK K H (f i))) =
        val_vp O l (algebraMap O K (B (e i) (f i))) + val_vp O l (φ i ξ) + val_vp O l (φ i r) := by
      rw [hval1, map_mul, val_mul O l (mul_ne_zero hφξ hφr) hB0, val_mul O l hφξ hφr]
      rw [add_comm, add_assoc]
    refine ⟨hval1, hF0, hvF, hvr, ?_⟩
    rw [hvF, hvr]
    calc val_vp O l (algebraMap O K (B (e i) (f i))) + val_vp O l (φ i ξ) + (((if l = d then 1 / 2 else 0 : ℚ)) : WithTop ℚ)
        ≤ val_vp O l (algebraMap O K D) + 0 + (((if l = d then 1 / 2 else 0 : ℚ)) : WithTop ℚ) := by
          gcongr
          · exact (hB i).2
          · exact hval (φ i)
      _ = _ := by rw [add_zero]

end GlobalTheory.CMFormBound
