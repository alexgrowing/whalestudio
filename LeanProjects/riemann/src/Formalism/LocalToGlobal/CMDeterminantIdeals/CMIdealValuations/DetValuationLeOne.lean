import Formalism.LocalToGlobal.CMDeterminantIdeals.CmNumbersLink
import Formalism.LocalToGlobal.CMDeterminantIdeals.HadamardLoc0

noncomputable section

namespace Formalism.L2.LamCM

open NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped nonZeroDivisors ComplexOrder

theorem key_formula_link : KeyCoreLink := by
  intro h
  obtain ⟨κ, h1, h2, h3, h4⟩ := h
  refine ⟨κ, h1, h2, ?_, h4.2⟩
  intro R K _ _ _ _ _ _ _ x xK hpb
  obtain ⟨u, hu, -⟩ := h3 R K x xK hpb
  exact ⟨u, hu⟩

section Core

theorem keyDegCore_core (hKF : KeyCore) (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K)
    (hT : T.Good) (hL : abelian₂.Good) (hloc : ∀ p, KeyLocAt x T abelian₂ p) (harch : ∀ σ, KeyArchAt x T abelian₂ σ)
    (hN : ∀ k : K, k ≠ 0 → ∑ σ : K →+* ℂ, Real.log ‖σ k‖ =
      Real.log ((FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ k) : ℚ) : ℝ))
    (hS : ∀ (I : FractionalIdeal (𝓞 K)⁰ K) (k : K), I ≠ 0 → k ≠ 0 →
      (∀ p : HeightOneSpectrum (𝓞 K), ∃ c : K, IsLocGen p c I ∧ p.valuation K k ≤ p.valuation K c ∧
        p.valuation K k⁻¹ ≤ p.valuation K c⁻¹) → FractionalIdeal.spanSingleton (𝓞 K)⁰ k = I) :
    T.dual.deg = (1 / 2) * abelian₂.dual.deg + (x.P.g : ℝ) / 4 * (Module.finrank ℚ K : ℝ) * Real.log (2 * Real.pi) := by
  obtain ⟨κ, hH, hF, hU1, hU2⟩ := hKF
  set k : K := (κ K x : K) with hkdef
  have hk : k ≠ 0 := (κ K x).ne_zero
  have hloc' : ∀ p : HeightOneSpectrum (𝓞 K), ∃ ca cd : K, IsLocGen p ca T.I ∧ IsLocGen p cd abelian₂.I ∧
      p.valuation K k ≤ p.valuation K (ca ^ 8 / cd ^ 4) ∧ p.valuation K k⁻¹ ≤ p.valuation K (ca ^ 8 / cd ^ 4)⁻¹ := by
    intro p
    obtain ⟨K', _, _, R, _, _, _, _, _, f, x', a, d, ca, cd, ua, ud, hPB, hInt, hval, ha, hd, hca, hcd⟩ := hloc p
    obtain ⟨th', hth', v', hv', M, xR, hth'eq, hv'eq, hMdet, hPBR⟩ := hInt
    have hFx : (κ K' x' : K') = f k := hF K K' f x x' hPB
    have hHx : a ^ 8 * (κ K' ⟨x'.P, x'.g_pos, x'.rig, x'.rig_gen, th', hth', v', hv'⟩ : K') =
        M.det ^ 4 * (κ K' x' : K') :=
      hH K' x'.P x'.g_pos x'.rig x'.rig_gen x'.th x'.th_ne x'.v x'.basis th' hth' v' hv' a M hth'eq hv'eq
    obtain ⟨u, hu⟩ := hU1 R K' xR _ hPBR
    rw [hu, hFx, hMdet, ha, hd] at hHx
    have hfa : f ca ≠ 0 := (map_ne_zero f).2 hca.1
    have hfd : f cd ≠ 0 := (map_ne_zero f).2 hcd.1
    have hD : algebraMap R K' (ud : R) ≠ 0 := (ud.isUnit.map (algebraMap R K')).ne_zero
    have hc : ca ^ 8 / cd ^ 4 ≠ 0 := div_ne_zero (pow_ne_zero _ hca.1) (pow_ne_zero _ hcd.1)
    have hfk : f k = (f ca * algebraMap R K' (ua : R)) ^ 8 * algebraMap R K' (u : R) /
        (f cd * algebraMap R K' (ud : R)) ^ 4 := by
      rw [eq_div_iff (pow_ne_zero _ (mul_ne_zero hfd hD)), hHx]; ring
    have hw : f (k / (ca ^ 8 / cd ^ 4)) = algebraMap R K' ((ua ^ 8 * u * ud⁻¹ ^ 4 : Rˣ) : R) := by
      rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_mul, map_mul,
        map_pow, map_pow, map_units_inv, map_div₀, map_div₀, map_pow, map_pow, hfk]
      field_simp
    have hw' : f (k⁻¹ / (ca ^ 8 / cd ^ 4)⁻¹) = algebraMap R K' (((ua ^ 8 * u * ud⁻¹ ^ 4)⁻¹ : Rˣ) : R) := by
      rw [inv_div_inv, ← inv_div, map_inv₀, hw, map_units_inv]
    exact ⟨ca, cd, hca, hcd, valuation_le_of_eq_algebraMap p f hval hc _ hw,
      valuation_le_of_eq_algebraMap p f hval (inv_ne_zero hc) _ hw'⟩
  have hJ : T.I ^ 8 * (abelian₂.I ^ 4)⁻¹ ≠ 0 := mul_ne_zero (pow_ne_zero _ hT.1) (inv_ne_zero (pow_ne_zero _ hL.1))
  have hspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ k = T.I ^ 8 * (abelian₂.I ^ 4)⁻¹ := hS _ k hJ hk (fun p => by
    obtain ⟨ca, cd, h1, h2, h3, h4⟩ := hloc' p
    exact ⟨_, isLocGen_pow8_div_pow4 hT.1 hL.1 h1 h2, h3, h4⟩)
  have hNT : ((FractionalIdeal.absNorm T.I : ℚ) : ℝ) ≠ 0 := by
    exact_mod_cast (FractionalIdeal.absNorm_eq_zero_iff.not.2 hT.1)
  have hNL : ((FractionalIdeal.absNorm abelian₂.I : ℚ) : ℝ) ≠ 0 := by
    exact_mod_cast (FractionalIdeal.absNorm_eq_zero_iff.not.2 hL.1)
  have hNk : Real.log ((FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ k) : ℚ) : ℝ) =
      8 * Real.log ((FractionalIdeal.absNorm T.I : ℚ) : ℝ) - 4 * Real.log ((FractionalIdeal.absNorm abelian₂.I : ℚ) : ℝ) := by
    rw [hspan, map_mul, map_inv₀, map_pow, map_pow]
    push_cast
    rw [Real.log_mul (pow_ne_zero _ hNT) (inv_ne_zero (pow_ne_zero _ hNL)), Real.log_inv, Real.log_pow,
      Real.log_pow]
    push_cast
    ring
  have harch' : ∀ σ : K →+* ℂ, Real.log ‖σ k‖ + 8 * Real.log (T.n σ) - 4 * Real.log (abelian₂.n σ) =
      2 * (x.P.g : ℝ) * Real.log (2 * Real.pi) := by
    intro σ
    obtain ⟨xσ, u, Hm, W, χ, θ, Fd, hPB, hAH, hRig, hFn, hDiff, hFD, hTn, hLn⟩ := harch σ
    have hFσ : (κ ℂ xσ : ℂ) = σ k := hF K ℂ σ x xσ hPB
    obtain ⟨_, _, _, hg, _⟩ := hPB
    have he : (volume Fd).toReal / (Real.pi ^ xσ.P.g * ‖W.det‖ ^ 2) = (abelian₂.n σ ^ 2)⁻¹ := by
      rw [hLn, inv_div]
    have hU := hU2 xσ u Hm W χ θ Fd _ _ hAH hRig hFn hDiff hFD hTn rfl
    rw [he, hFσ, hg] at hU
    have hsk0 : 0 < ‖σ k‖ := norm_pos_iff.2 ((map_ne_zero σ).2 hk)
    have ht := hT.2 σ
    have hl := hL.2 σ
    have h8 : ‖σ k‖ * (T.n σ ^ 2) ^ 4 * ((abelian₂.n σ ^ 2)⁻¹) ^ 2 = ‖σ k‖ * T.n σ ^ 8 * (abelian₂.n σ ^ 4)⁻¹ := by
      field_simp
    rw [h8] at hU
    have := congrArg Real.log hU
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_inv,
      Real.log_pow, Real.log_pow, Real.log_pow] at this
    push_cast at this
    linarith
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (K →+* ℂ))) rfl (fun σ _ => harch' σ)
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, NumberField.Embeddings.card K ℂ, nsmul_eq_mul, hN k hk, hNk] at hsum
  simp only [MLine.deg, MLine.dual, map_inv₀, Rat.cast_inv, Real.log_inv, Finset.sum_neg_distrib]
  linarith

end Core

theorem key_degree_essential : KeyDegCore := by
  intro hKC K _ _ x T abelian₂ hT hL hloc harch
  refine keyDegCore_core hKC K x T abelian₂ hT hL hloc harch (fun k hk => sum_log_norm_embeddings hk)
    (fun I k hI hk hlocI => ?_)
  have hsk : FractionalIdeal.spanSingleton (𝓞 K)⁰ k ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact hk
  refine eq_of_count_eq hsk hI (fun p => ?_)
  obtain ⟨c, h1, h2, h3⟩ := hlocI p
  rw [count_eq_of_valuation_le p hk h1.1 h2 h3, h1.2]

section Lie

theorem lieGram_eq {g : ℕ} (Hm W : Matrix (Fin g) (Fin g) ℂ) :
    lieGram Hm W = (Real.pi : ℂ) • (W * Hm * W.conjTranspose).transpose := by
  ext i j
  simp only [lieGram, Matrix.of_apply, Matrix.smul_apply, Matrix.transpose_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, dotProduct, Matrix.mulVec, Pi.star_apply, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

end Lie

section Had

variable {K : Type} [Field K] [NumberField K]

theorem prod_span_le_of_loc {g : ℕ} (abelian₂ : MLine K) (ℓ : Fin g → MLine K) (d : K) (hLam : abelian₂.I ≠ 0)
    (hℓ : ∀ j, (ℓ j).I ≠ 0) (hd : d ≠ 0)
    (hloc : ∀ p : HeightOneSpectrum (𝓞 K), ∃ (cd : K) (cl : Fin g → K), IsLocGen p cd abelian₂.I ∧
      (∀ j, IsLocGen p (cl j) (ℓ j).I) ∧ p.valuation K ((∏ j, cl j) * d) ≤ p.valuation K cd) :
    (∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ d ≤ abelian₂.I := by
  have hP : (∏ j, (ℓ j).I) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hℓ j
  have hs : FractionalIdeal.spanSingleton (𝓞 K)⁰ d ≠ 0 := spanSingleton_ne_zero' hd
  have hX0 : (∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ d ≠ 0 := mul_ne_zero hP hs
  have h1 : (∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ d * abelian₂.I⁻¹ ≤ 1 := by
    apply le_one_of_count_nonneg (mul_ne_zero hX0 (inv_ne_zero hLam))
    intro p
    obtain ⟨cd, cl, hcd, hcl, hv⟩ := hloc p
    have hgen : IsLocGen p ((∏ j, cl j) * d) ((∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ d) :=
      IsLocGen.mul' (IsLocGen.prod' Finset.univ cl (fun j => (ℓ j).I) hcl hℓ) ⟨hd, rfl⟩ hP hs
    rw [FractionalIdeal.count_mul K p hX0 (inv_ne_zero hLam), FractionalIdeal.count_inv, ← hgen.2, ← hcd.2]
    rw [valuation_eq_exp_count p hgen.1, valuation_eq_exp_count p hcd.1, WithZero.exp_le_exp] at hv
    omega
  calc (∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ d
      = (∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ d * abelian₂.I⁻¹ * abelian₂.I := by
        rw [mul_assoc _ abelian₂.I⁻¹, inv_mul_cancel₀ hLam, mul_one]
    _ ≤ 1 * abelian₂.I := mul_le_mul' h1 le_rfl
    _ = abelian₂.I := one_mul _

theorem hadamard_of_le (g : ℕ) (abelian₂ : MLine K) (ℓ : Fin g → MLine K) (u : Fin g → Fin g → K)
    (H : (K →+* ℂ) → Matrix (Fin g) (Fin g) ℂ) (La : ℝ) (hLam : abelian₂.I ≠ 0) (hℓ : ∀ j, (ℓ j).Good)
    (hdne : (Matrix.of u).det ≠ 0) (hLa : 0 < La) (hH : ∀ σ, (H σ).PosDef)
    (hn : ∀ σ, abelian₂.n σ = Real.sqrt (H σ).det.re)
    (hle : (∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ (Matrix.of u).det ≤ abelian₂.I)
    (hsq : ∀ σ j, ReciprocityTheory.MultiplicativeHeights.hq (H σ) (ReciprocityTheory.MultiplicativeHeights.embVec σ (u j)) ≤ (La * (ℓ j).n σ) ^ 2) :
    ∑ j, (ℓ j).deg - (g : ℝ) * (Module.finrank ℚ K : ℝ) * Real.log La ≤ abelian₂.deg := by
  set d := (Matrix.of u).det with hd
  have hX0 : (∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ d ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun j _ => (hℓ j).1)
      (by rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff])
  have hN := A2.absNorm_anti' hle hX0
  have hposI : ∀ j, (0 : ℝ) < ((FractionalIdeal.absNorm (ℓ j).I : ℚ) : ℝ) := fun j => by
    exact_mod_cast A2.absNorm_pos' (hℓ j).1
  have hposd : ∀ σ : K →+* ℂ, 0 < ‖σ d‖ := fun σ => norm_pos_iff.2 ((map_ne_zero σ).2 hdne)
  have hposD := A2.absNorm_pos' hLam
  have hNX : ((FractionalIdeal.absNorm ((∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ d) : ℚ) : ℝ) =
      (∏ j, ((FractionalIdeal.absNorm (ℓ j).I : ℚ) : ℝ)) * ∏ σ : K →+* ℂ, ‖σ d‖ := by
    rw [map_mul, map_prod, Rat.cast_mul, Rat.cast_prod, A2.absNorm_span_real]
  have hlogN : Real.log ((FractionalIdeal.absNorm abelian₂.I : ℚ) : ℝ) ≤
      ∑ j, Real.log ((FractionalIdeal.absNorm (ℓ j).I : ℚ) : ℝ) + ∑ σ : K →+* ℂ, Real.log ‖σ d‖ := by
    rw [← Real.log_prod (fun j _ => (hposI j).ne'), ← Real.log_prod (fun σ _ => (hposd σ).ne'),
      ← Real.log_mul (Finset.prod_pos fun j _ => hposI j).ne' (Finset.prod_pos fun σ _ => hposd σ).ne', ← hNX]
    exact Real.log_le_log (by exact_mod_cast hposD) (by exact_mod_cast hN)
  have hσ : ∀ σ : K →+* ℂ, Real.log ‖σ d‖ + Real.log (Real.sqrt (H σ).det.re) ≤
      ∑ j, (Real.log La + Real.log ((ℓ j).n σ)) := by
    intro σ
    have hD := A2.det_re_pos (hH σ)
    have hGpd : (ReciprocityTheory.MultiplicativeHeights.gramC (H σ) σ u).PosDef := by
      rw [A2.gramC_eq]
      apply (hH σ).conjTranspose_mul_mul_same
      apply Matrix.mulVec_injective_iff_isUnit.2
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact IsUnit.mk0 _ ((map_ne_zero σ).2 hdne)
    have hdiagpos : ∀ j, 0 < (ReciprocityTheory.MultiplicativeHeights.gramC (H σ) σ u j j).re := fun j => by
      simpa using (Complex.lt_def.1 (hGpd.diag_pos (i := j))).1
    have hHd := hadamardInequality g _ hGpd
    rw [A2.gramC_det, Complex.re_ofReal_mul] at hHd
    have hbound : ∏ j, (ReciprocityTheory.MultiplicativeHeights.gramC (H σ) σ u j j).re ≤ ∏ j, (La * (ℓ j).n σ) ^ 2 := by
      apply Finset.prod_le_prod
      · intro j _
        exact (hdiagpos j).le
      · intro j _
        exact hsq σ j
    have key : ‖σ d‖ ^ 2 * (H σ).det.re ≤ ∏ j, (La * (ℓ j).n σ) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      exact hHd.trans hbound
    have hpos' : 0 < ‖σ d‖ ^ 2 * (H σ).det.re := by
      have := hposd σ
      positivity
    have hlog := Real.log_le_log hpos' key
    have hnpos : ∀ j, 0 < (ℓ j).n σ := fun j => (hℓ j).2 σ
    rw [Real.log_mul (by have := hposd σ; positivity) hD.ne', Real.log_pow,
      Real.log_prod (fun j _ => by have := hnpos j; positivity)] at hlog
    have hs : ∑ j, Real.log ((La * (ℓ j).n σ) ^ 2) = 2 * ∑ j, (Real.log La + Real.log ((ℓ j).n σ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Real.log_pow, Real.log_mul hLa.ne' (hnpos j).ne']
      push_cast
      ring
    rw [hs] at hlog
    rw [Real.log_sqrt hD.le]
    push_cast at hlog
    linarith
  have hsumσ := Finset.sum_le_sum fun σ (_ : σ ∈ (Finset.univ : Finset (K →+* ℂ))) => hσ σ
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsumσ
  have hc : ∑ σ : K →+* ℂ, ∑ j, Real.log ((ℓ j).n σ) = ∑ j, ∑ σ : K →+* ℂ, Real.log ((ℓ j).n σ) :=
    Finset.sum_comm
  have hcard : (Fintype.card (K →+* ℂ) : ℝ) = Module.finrank ℚ K := by
    exact_mod_cast NumberField.Embeddings.card K ℂ
  rw [hc, hcard] at hsumσ
  have hLd : abelian₂.deg = -Real.log ((FractionalIdeal.absNorm abelian₂.I : ℚ) : ℝ) -
      ∑ σ, Real.log (Real.sqrt (H σ).det.re) := by
    simp only [MLine.deg, hn]
  rw [hLd]
  simp only [MLine.deg, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  linarith

end Had

theorem hadamard_local_base : HadamardLoc0 := by
  intro K _ _ g abelian₂ ℓ U H La hLam hℓ hdet hLa hH hn hloc hsq
  have hle := prod_span_le_of_loc abelian₂ ℓ U.det hLam (fun j => (hℓ j).1) hdet hloc
  exact hadamard_of_le g abelian₂ ℓ U H La hLam hℓ hdet hLa hH hn hle hsq

theorem lambda_key_formula : LamKey := by
  intro hKC K _ _ x T abelian₂ ℓ U H La logOm V _ c G μ n S Rr hT hL hloc harch hℓ hdne hLa hH hn hlocU hsq hnd
    hcf hmem hS hRr hev
  have hdeg := key_degree_essential hKC K x T abelian₂ hT hL hloc harch
  have hHad := hadamard_local_base K x.P.g abelian₂ ℓ U H La hL.1 hℓ hdne (by linarith) hH hn hlocU hsq
  have hTd : T.dual.Good := (degree_algebraic K T T hT hT).2.2.1
  have hd := finrank_pos_real K
  have hnd' : T.dual.ndeg ≤ (1 / 2) * abelian₂.dual.ndeg + (x.P.g : ℝ) / 4 * Real.log (2 * Real.pi) := by
    apply le_of_eq
    simp only [MLine.ndeg]
    rw [hdeg]
    field_simp
  exact lambda_number_base K x.P.g abelian₂ ℓ T.dual La logOm V c G μ n S Rr ⟨hL, hℓ, hTd, hLa, hHad, hnd, hnd'⟩ hcf hmem hS
    hRr hev

end Formalism.L2.LamCM
