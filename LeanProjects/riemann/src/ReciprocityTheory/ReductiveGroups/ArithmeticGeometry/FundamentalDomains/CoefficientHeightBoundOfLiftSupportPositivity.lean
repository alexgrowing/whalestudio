import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicOutsideLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.QuadraticOffDiagonalBounds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IntegerApproximationCountHolds

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate ComplexOrder

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem coefficient_height_bound_of (h2 : UnipotentLatticeLift (E := E)) (h3d : FourierCoefficientSupport (E := E))
    (h5 : NonvanishingCoefficientPositivity (E := E)) (hD3 : IntegerApproximationCount (E := E)) : CoefficientHeightBound (E := E) := by
  intro r X la P ξ ν c1 w z0 x a hS hHmax t ht K2 S
  classical
  obtain ⟨hHyp, hxL, hxξ, hxx, hxne, hw0, hua⟩ := hS
  obtain ⟨-, hPSS, hξ, hc1, hνsum, -, -, -, hchar, hz0, -⟩ := hHyp
  obtain ⟨hξΛ, hξξ, hξ0⟩ := hξ
  obtain ⟨hzdom, hzD⟩ := hz0
  have hNC : (X.NC : E) ≠ 0 := by exact_mod_cast X.NC_pos.ne'
  have hξx : herm X.Gm ξ x = 0 := by
    rw [← HermitianTraceFormVanishing.herm_conj X.Gm X.Gm_herm x ξ, hxξ]
    simp
  have hIso : IsIsoPair X.Gm ![ξ, (X.NC : E) • x] := by
    refine ⟨?_, ?_⟩
    · intro i k
      fin_cases i <;> fin_cases k <;>
        simp [HermitianTraceFormVanishing.herm_smul_left, HermitianTraceFormVanishing.herm_smul_right, hξξ, hxξ, hξx, hxx]
    · rw [LinearIndependent.pair_iff]
      intro s s' hst
      by_cases hs0 : s' = 0
      · subst hs0
        refine ⟨?_, rfl⟩
        simpa [hξ0] using hst
      · exfalso
        have hsn : s' * (X.NC : E) ≠ 0 := mul_ne_zero hs0 hNC
        apply hxne (-(s / (s' * (X.NC : E))))
        have h' : (s' * (X.NC : E)) • x = -(s • ξ) := by
          rw [mul_smul]
          exact eq_neg_of_add_eq_zero_right hst
        calc x = (s' * (X.NC : E))⁻¹ • ((s' * (X.NC : E)) • x) := by
              rw [smul_smul, inv_mul_cancel₀ hsn, one_smul]
          _ = -(s / (s' * (X.NC : E))) • ξ := by
              rw [h', smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
  have hΛ : ∀ i, (![ξ, (X.NC : E) • x] : Fin 2 → Fin r → E) i ∈ X.Λ := by
    intro i
    fin_cases i
    · simpa using hξΛ
    · simpa using X.NC_sub x hxL

  have hmem : ∀ χ ∈ S, IsHermFam χ ∧ X.IsFreqZ X.g χ ∧ (∀ τ, χ τ 0 0 = (ν τ : ℂ)) ∧
      (∀ τ, (Matrix.of (χ τ)).PosSemidef) := by
    intro χ hχ
    obtain ⟨⟨y, hy, hfz⟩, -⟩ := hχ
    have hHF : IsHermFam χ ∧ X.IsFreqZ X.g χ := by
      by_contra hn
      apply hfz
      unfold Data.fz
      rw [if_neg hn]
    have e := h3d r X ![ξ, (X.NC : E) • x] hIso hΛ la P hPSS.1.1 hchar ν χ y hy
    by_cases hν : ∀ τ, χ τ 0 0 = (ν τ : ℂ)
    · rw [if_pos hν] at e
      have hP : X.fz ![ξ, (X.NC : E) • x] X.g χ P y ≠ 0 := fun h0 => hfz (e.trans h0)
      exact ⟨hHF.1, hHF.2, hν,
        fun τ => (h5 r X _ hIso hΛ la P hPSS hchar χ ⟨y, hy, hP⟩ τ).posSemidef⟩
    · exfalso
      rw [if_neg hν] at e
      exact hfz e

  have hHne : ∀ τ : X.Ψ, X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) ≠ 0 := fun τ h => by
    have h1 := hzD τ
    rw [X.Hf_self hzdom τ] at h
    rw [Complex.ofReal_eq_zero.mp h, mul_zero] at h1
    exact zero_ne_one h1
  have hcoord : ∀ τ : X.Ψ, ∃ p q : ℂ, q * a τ 0 + p = 0 ∧ q * a τ 1 = 1 ∧
      ‖p‖ ^ 2 + ‖q‖ ^ 2 ≤ (X.NC : ℝ) ^ 2 * (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2) := by
    intro τ
    have hcpos : 0 < X.c τ := by
      unfold Data.c
      rw [X.ξ0_abs τ]
      linarith [X.minWeight_pos]
    have hmw : 0 < X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ) := X.maj_pos hzdom τ (hw0 τ)
    have hc0 : X.c τ ≠ 0 := hcpos.ne'
    have hm0 : X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ) ≠ 0 := hmw.ne'
    have hs : Real.sqrt (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)) ^ 2 =
        X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ) := Real.sq_sqrt (mul_pos hcpos hmw).le
    have hcast : ((Real.sqrt (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)))⁻¹ : ℂ) =
        (((Real.sqrt (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)))⁻¹ : ℝ) : ℂ) := by
      simp
    have hua' : X.uvec ![ξ, (X.NC : E) • x] a τ =
        (((Real.sqrt (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)))⁻¹ : ℝ) : ℂ) •
          X.ucomp z0 ξ (X.embV x) τ := by
      rw [hua τ, hcast]
    have he : X.uvec ![ξ, (X.NC : E) • x] a τ =
        a τ 0 • Data.emb τ.1 ξ + a τ 1 • Data.emb τ.1 ((X.NC : E) • x) := by
      simp [Data.uvec, Fin.sum_univ_two]
    have h1 : X.c τ * (X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)).re = 1 := by
      rw [X.Hf_self hzdom, Complex.ofReal_re]
      exact hzD τ
    have hwf : X.Hf z0 τ (X.ucomp z0 ξ (X.embV x) τ) (Data.emb τ.1 ξ) = 0 := by
      show X.Hf z0 τ (Data.emb τ.1 x - (X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) /
        X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0
      rw [UnipotentCoefficientShift.Hf_sub_left, UnipotentCoefficientShift.Hf_smul_left, div_mul_cancel₀ _ (hHne τ), sub_self]
    have h2e : X.Hf z0 τ (X.uvec ![ξ, (X.NC : E) • x] a τ) (Data.emb τ.1 ξ) = 0 := by
      rw [hua', UnipotentCoefficientShift.Hf_smul_left, hwf, mul_zero]
    have h3 : X.c τ * (X.Hf z0 τ (X.uvec ![ξ, (X.NC : E) • x] a τ)
        (X.uvec ![ξ, (X.NC : E) • x] a τ)).re = 1 := by
      rw [hua', X.Hf_self hzdom, Complex.ofReal_re, UnipotentCoefficientShift.maj_smul hzdom, inv_pow, hs]
      field_simp
    obtain ⟨p, q, hp1, hp2, hpq⟩ :=
      QuadraticOffDiagonalBounds.coord hzdom τ _ _ _ (a τ 0) (a τ 1) (X.c τ) he h1 h2e h3
    refine ⟨p, q, hp1, hp2, ?_⟩
    rw [hpq, X.Hf_self hzdom, Complex.ofReal_re]
    exact hHmax τ

  set Hm : ℝ := (X.NC : ℝ) ^ 2 * (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2) with hHm
  have hHm1 : 1 ≤ Hm := by
    have h1 : (1 : ℝ) ≤ X.NC := by exact_mod_cast X.NC_pos
    have h2 : 0 ≤ 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2 := by positivity
    rw [hHm]
    nlinarith
  set B : ℝ := Hm * (c1 + t / 2) with hB
  have hB0 : 0 ≤ B := mul_nonneg (by linarith) (by linarith)
  have hent : ∀ χ ∈ S, ∀ τ : X.Ψ, ‖χ τ 0 1‖ ≤ B ∧ ‖χ τ 1 1‖ ≤ B := by
    intro χ hχ τ
    obtain ⟨hH, -, hν, hpsd⟩ := hmem χ hχ
    have hχt : 2 * ∑ τ, (X.chiAt χ a τ).re ≤ t := hχ.2
    have q00 : ∀ τ', (∑ i, ∑ k, χ τ' i k * (![1, 0] : Fin 2 → ℂ) i *
        conj ((![1, 0] : Fin 2 → ℂ) k)) = χ τ' 0 0 := by
      intro τ'
      simp [Fin.sum_univ_two]
    have q11 : (∑ i, ∑ k, χ τ i k * (![0, 1] : Fin 2 → ℂ) i * conj ((![0, 1] : Fin 2 → ℂ) k)) =
        χ τ 1 1 := by
      simp [Fin.sum_univ_two]
    have hνnn : ∀ τ', 0 ≤ ν τ' := by
      intro τ'
      have h := QuadraticOffDiagonalBounds.quad_nonneg (hpsd τ') ![1, 0]
      rw [q00, hν τ', Complex.ofReal_re] at h
      exact h
    have hchinn : ∀ τ', 0 ≤ (X.chiAt χ a τ').re := fun τ' => QuadraticOffDiagonalBounds.quad_nonneg (hpsd τ') (a τ')
    have hντ : ν τ ≤ c1 :=
      le_trans (Finset.single_le_sum (fun τ' _ => hνnn τ') (Finset.mem_univ τ)) hνsum
    have hchτ : (X.chiAt χ a τ).re ≤ t / 2 := by
      have := Finset.single_le_sum (fun τ' _ => hchinn τ') (Finset.mem_univ τ)
      linarith
    obtain ⟨p, q, hp1, hp2, hpq⟩ := hcoord τ
    have hvec : q • a τ + p • (![1, 0] : Fin 2 → ℂ) = ![0, 1] := by
      funext i
      fin_cases i
      · simp
        linear_combination hp1
      · simp
        linear_combination hp2
    have hc := QuadraticOffDiagonalBounds.quad_comb (hpsd τ) q p (a τ) ![1, 0]
    rw [hvec, q11, q00 τ, hν τ, Complex.ofReal_re] at hc
    have hchi : (∑ i, ∑ k, χ τ i k * a τ i * conj (a τ k)).re = (X.chiAt χ a τ).re := rfl
    rw [hchi] at hc
    have hre11 : (χ τ 1 1).re ≤ B := by
      calc (χ τ 1 1).re ≤ (‖q‖ ^ 2 + ‖p‖ ^ 2) * ((X.chiAt χ a τ).re + ν τ) := hc
        _ ≤ Hm * (c1 + t / 2) := by
            apply mul_le_mul (by linarith) (by linarith) (by linarith [hchinn τ, hνnn τ])
              (by linarith)
    have hnn11 : 0 ≤ (χ τ 1 1).re := by
      have h := QuadraticOffDiagonalBounds.quad_nonneg (hpsd τ) ![0, 1]
      rwa [q11] at h
    have hreal11 : χ τ 1 1 = ((χ τ 1 1).re : ℂ) :=
      (Complex.conj_eq_iff_re.mp (hH τ 1 1).symm).symm
    have hn11 : ‖χ τ 1 1‖ ≤ B := by
      rw [hreal11, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn11]
      exact hre11
    have hoff := QuadraticOffDiagonalBounds.offdiag_le (hpsd τ) (hH τ 0 1)
    rw [hν τ, Complex.ofReal_re] at hoff
    have hcB : c1 ≤ B := by
      have : c1 + t / 2 ≤ Hm * (c1 + t / 2) := by nlinarith
      linarith
    exact ⟨by linarith, hn11⟩

  have hdisc : 0 < dEnat E := Int.natAbs_pos.mpr (NumberField.discr_ne_zero E)
  obtain ⟨N0, hN0⟩ : ∃ n : ℕ, n = X.g * dEnat E ^ 2 := ⟨_, rfl⟩
  have hN0E : (N0 : E) ≠ 0 := by
    rw [hN0]
    exact_mod_cast (Nat.mul_pos X.g_pos (pow_pos hdisc 2)).ne'
  have hN0r : (N0 : ℝ) = X.g * dE E ^ 2 := by
    simp only [hN0, dEnat, dE, Nat.cast_mul, Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs]
  have hβ : ∀ χ ∈ S, ∃ β : Matrix (Fin 2) (Fin 2) E, (∀ i k, cc (β i k) = β k i) ∧
      χ = X.embH β ∧ ∀ i k, IsIntegral ℤ ((N0 : E) * β i k) := by
    intro χ hχ
    obtain ⟨hH, hF, -, -⟩ := hmem χ hχ
    obtain ⟨β, hβ1, hβ2, hβ3⟩ := (h2 r X _ hIso hΛ).2.2 χ hH hF
    exact ⟨β, hβ1, hβ2, fun i k => by rw [hN0]; exact hβ3 i k⟩
  choose! β hβh hβe hβi using hβ
  have hent' : ∀ χ ∈ S, ∀ (τ : X.Ψ) (i k : Fin 2), χ τ i k = τ.1 (β χ i k) := fun χ hχ τ i k =>
    congrFun (congrFun (congrFun (hβe χ hχ) τ) i) k
  have hσ : ∀ χ ∈ S, ∀ i k : Fin 2, (∀ τ : X.Ψ, ‖χ τ i k‖ ≤ B) →
      ∀ σ : E →+* ℂ, ‖σ ((N0 : E) * β χ i k)‖ ≤ (N0 : ℝ) * B := by
    intro χ hχ i k hb σ
    rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    by_cases hs : σ ∈ X.Ψ
    · have h := hb ⟨σ, hs⟩
      rw [hent' χ hχ] at h
      exact h
    · have hcc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
        RingHom.ext fun a => by simp
      have hc : ComplexEmbedding.conjugate σ ∈ X.Ψ := by
        rw [X.cmType, hcc]
        exact hs
      have h := hb ⟨_, hc⟩
      rw [hent' χ hχ] at h
      simpa [ComplexEmbedding.conjugate_coe_eq] using h
  obtain ⟨hAfin, hAcard⟩ := (hD3 r X.toData).2 ((N0 : ℝ) * B) (mul_nonneg (Nat.cast_nonneg _) hB0)
  set A := {α : 𝓞 E | ∀ σ : E →+* ℂ, ‖σ (α : E)‖ ≤ (N0 : ℝ) * B} with hA
  let φ : (X.Ψ → Fin 2 → Fin 2 → ℂ) → E × E := fun χ => ((N0 : E) * β χ 0 1, (N0 : E) * β χ 1 1)
  have hmaps : ∀ χ ∈ S, φ χ ∈ (Subtype.val '' A) ×ˢ (Subtype.val '' A) := by
    intro χ hχ
    exact ⟨⟨⟨(N0 : E) * β χ 0 1, hβi χ hχ 0 1⟩, hσ χ hχ 0 1 (fun τ => (hent χ hχ τ).1), rfl⟩,
      ⟨⟨(N0 : E) * β χ 1 1, hβi χ hχ 1 1⟩, hσ χ hχ 1 1 (fun τ => (hent χ hχ τ).2), rfl⟩⟩
  have hinj : Set.InjOn φ S := by
    intro χ hχ χ' hχ' hφ
    obtain ⟨h01', h11'⟩ := Prod.mk.inj (hφ : ((N0 : E) * β χ 0 1, (N0 : E) * β χ 1 1) =
      ((N0 : E) * β χ' 0 1, (N0 : E) * β χ' 1 1))
    have h01 : β χ 0 1 = β χ' 0 1 := mul_left_cancel₀ hN0E h01'
    have h11 : β χ 1 1 = β χ' 1 1 := mul_left_cancel₀ hN0E h11'
    obtain ⟨hH, -, hν, -⟩ := hmem χ hχ
    obtain ⟨hH', -, hν', -⟩ := hmem χ' hχ'
    have e01 : ∀ τ, χ τ 0 1 = χ' τ 0 1 := fun τ => by
      rw [hent' χ hχ, hent' χ' hχ', h01]
    have e11 : ∀ τ, χ τ 1 1 = χ' τ 1 1 := fun τ => by
      rw [hent' χ hχ, hent' χ' hχ', h11]
    funext τ i k
    fin_cases i <;> fin_cases k
    · exact (hν τ).trans (hν' τ).symm
    · exact e01 τ
    · exact (hH τ 0 1).trans ((congrArg conj (e01 τ)).trans (hH' τ 0 1).symm)
    · exact e11 τ
  have hTfin : ((Subtype.val '' A) ×ˢ (Subtype.val '' A)).Finite :=
    (hAfin.image _).prod (hAfin.image _)
  have hSfin : S.Finite := Set.Finite.of_finite_image
    (hTfin.subset (by rintro _ ⟨χ, hχ, rfl⟩; exact hmaps χ hχ)) hinj
  have hcard := Set.ncard_le_ncard_of_injOn φ hmaps hinj hTfin
  rw [Set.ncard_prod] at hcard
  have himA : (Subtype.val '' A).ncard ≤ A.ncard := Set.ncard_image_le hAfin
  have hcard' : S.ncard ≤ A.ncard * A.ncard := hcard.trans (Nat.mul_le_mul himA himA)
  refine ⟨hSfin, ?_⟩
  have hR0 : 0 ≤ (N0 : ℝ) * B := mul_nonneg (Nat.cast_nonneg _) hB0
  have hNH : 0 ≤ (N0 : ℝ) * Hm := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have hR1 : 1 + 2 * ((N0 : ℝ) * B) ≤ K2 * t := by
    simp only [K2, ← hHm]
    rw [← hN0r, hB]
    nlinarith [mul_nonneg (mul_nonneg hNH hc1.le) (sub_nonneg.mpr ht)]
  calc (S.ncard : ℝ) ≤ (A.ncard : ℝ) * A.ncard := by exact_mod_cast hcard'
    _ ≤ (1 + 2 * ((N0 : ℝ) * B)) ^ (2 * fdeg E) * (1 + 2 * ((N0 : ℝ) * B)) ^ (2 * fdeg E) :=
        mul_le_mul hAcard hAcard (Nat.cast_nonneg _) (pow_nonneg (by linarith) _)
    _ = (1 + 2 * ((N0 : ℝ) * B)) ^ (4 * fdeg E) := by
        rw [← pow_add]
        congr 1
        ring
    _ ≤ (K2 * t) ^ (4 * fdeg E) := pow_le_pow_left₀ (by linarith) hR1 _

theorem coefficient_height_bound_of_lift_support_positivity (h2 : UnipotentLatticeLift (E := E)) (h3d : FourierCoefficientSupport (E := E))
    (h5 : NonvanishingCoefficientPositivity (E := E)) : CoefficientHeightBound (E := E) :=
  coefficient_height_bound_of h2 h3d h5 integerApproximationCount_holds

end ReciprocityTheory.ChartRestriction.G.FD
