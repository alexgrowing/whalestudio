import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Places
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

private lemma nrm_le {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (x : w.adicCompletion E) (h : ValuativeRel.valuation (w.adicCompletion E) x ≤ 1) : ‖x‖ ≤ 1 :=
  norm_le_one_of_mem w ((mem_valuationInteger_iff w x).1 ((Valuation.mem_integer_iff _ _).2 h))

private lemma nrm_eq {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    {x y : w.adicCompletion E}
    (h : ValuativeRel.valuation (w.adicCompletion E) x = ValuativeRel.valuation (w.adicCompletion E) y) :
    ‖x‖ = ‖y‖ := by
  have key : ∀ a b : w.adicCompletion E, b ≠ 0 →
      ValuativeRel.valuation (w.adicCompletion E) a = ValuativeRel.valuation (w.adicCompletion E) b →
      ‖a‖ ≤ ‖b‖ := by
    intro a b hb hab
    have hb' : ValuativeRel.valuation (w.adicCompletion E) b ≠ 0 := (Valuation.ne_zero_iff _).2 hb
    have h1 : ValuativeRel.valuation (w.adicCompletion E) (a / b) ≤ 1 := by
      rw [map_div₀, hab, div_self hb']
    have h2 := nrm_le w _ h1
    rw [norm_div] at h2
    exact (div_le_one (norm_pos_iff.2 hb)).1 h2
  by_cases hy : y = 0
  · subst hy
    have hx : x = 0 := (Valuation.zero_iff _).1 (by rw [h, map_zero])
    rw [hx]
  have hx : x ≠ 0 := by
    intro hx
    exact hy ((Valuation.zero_iff _).1 (by rw [← h, hx, map_zero]))
  exact le_antisymm (key x y hy h) (key y x hx h.symm)

private lemma nrm_unif {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    ‖((GLnLocal.uniformizer (w.adicCompletion E) : _) : w.adicCompletion E)‖ ≤ 1 / 2 := by
  have hlt : ValuativeRel.valuation (w.adicCompletion E)
      ((GLnLocal.uniformizer (w.adicCompletion E) : _) : w.adicCompletion E) < 1 :=
    GLnLocal.valuation_uniformizer_lt_one _
  have hne : ((GLnLocal.uniformizer (w.adicCompletion E) : _) : w.adicCompletion E) ≠ 0 :=
    GLnLocal.uniformizer_ne_zero _
  generalize ((GLnLocal.uniformizer (w.adicCompletion E) : _) : w.adicCompletion E) = x at hlt hne
  have hv : Valued.v x < 1 := by
    by_contra hge
    have hge' : 1 ≤ Valued.v x := not_lt.1 hge
    have hinv : Valued.v x⁻¹ ≤ 1 := by
      rw [map_inv₀]; exact inv_le_one_of_one_le₀ hge'
    have hm : x⁻¹ ∈ HeightOneSpectrum.adicCompletionIntegers E w :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hinv
    have h3 := (Valuation.mem_integer_iff _ _).1 ((mem_valuationInteger_iff w _).2 hm)
    rw [map_inv₀] at h3
    have h0 : ValuativeRel.valuation (w.adicCompletion E) x ≠ 0 := (Valuation.ne_zero_iff _).2 hne
    exact absurd h3 (not_le.2 ((one_lt_inv₀ (zero_lt_iff.2 h0)).2 hlt))
  have hvne : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hne
  have hN : 1 < Ideal.absNorm w.asIdeal := HeightOneSpectrum.one_lt_absNorm w
  have hN2 : (2 : ℝ) ≤ (Ideal.absNorm w.asIdeal : ℝ) := by exact_mod_cast hN
  have h1 : (1 : NNReal) < (Ideal.absNorm w.asIdeal : NNReal) := by exact_mod_cast hN
  have hlt1 : ‖x‖ < 1 := by
    rw [FinitePlace.norm_def]
    exact_mod_cast (WithZeroMulInt.toNNReal_lt_one_iff h1).2 hv
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hvne] at hlt1 ⊢
  generalize (WithZero.unzero hvne).toAdd = m at hlt1 ⊢
  have hm : m ≤ -1 := by
    by_contra hc
    have hm0 : 0 ≤ m := by omega
    have h5 : (1 : NNReal) ≤ (Ideal.absNorm w.asIdeal : NNReal) ^ m := one_le_zpow₀ h1.le hm0
    have h6 : (1 : ℝ) ≤ (((Ideal.absNorm w.asIdeal : NNReal) ^ m : NNReal) : ℝ) := by exact_mod_cast h5
    exact absurd hlt1 (not_lt.2 h6)
  have h6 : (Ideal.absNorm w.asIdeal : NNReal) ^ m ≤ (Ideal.absNorm w.asIdeal : NNReal) ^ (-1 : ℤ) :=
    zpow_le_zpow_right₀ h1.le hm
  have h7 : (((Ideal.absNorm w.asIdeal : NNReal) ^ m : NNReal) : ℝ) ≤ (Ideal.absNorm w.asIdeal : ℝ)⁻¹ := by
    have := NNReal.coe_le_coe.2 h6
    simpa using this
  refine h7.trans ?_
  rw [one_div]
  exact inv_anti₀ (by norm_num) hN2

private lemma prod_zp {n : ℕ} {K : Type} [Field K] (x : K) (hx : x ≠ 0) (e : Fin n → ℤ) (J : Finset (Fin n)) :
    ∏ i ∈ J, x ^ e i = x ^ ∑ i ∈ J, e i := by
  classical
  induction J using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hx]

private lemma fin_real (r : ℝ) (h0 : 0 < r) (h1 : r ≤ 1 / 2) (j m : ℕ) (hm : 1 ≤ m) :
    r ^ (j * m) * 2 ^ j ≤ 1 := by
  have hr1 : r ≤ 1 := by linarith
  have ha : r ^ (j * m) ≤ r ^ j := pow_le_pow_of_le_one h0.le hr1 (Nat.le_mul_of_pos_right j hm)
  have hb : r ^ j * 2 ^ j ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by positivity) (by linarith)
  exact (mul_le_mul_of_nonneg_right ha (by positivity)).trans hb

theorem UpperTheory.norm_coeff_zero_factor_charpoly_iwahori_diagPow_le :
    A1 → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ν : Fin n → ℤ), Function.Injective ν → ∑ i, ν i = 0 →
        (∀ J : Finset (Fin n), J.Nonempty → J ≠ Finset.univ → ∑ i ∈ J, ν i ≠ 0) → ∀ j : ℕ, 0 < j →
        ∀ a ∈ GLnLocal.iwahori (w.adicCompletion E) n, ∀ b ∈ GLnLocal.iwahori (w.adicCompletion E) n,
        ∀ p₁ p₂ : (w.adicCompletion E)[X], p₁.Monic → p₂.Monic → 0 < p₁.natDegree → 0 < p₂.natDegree →
        p₁ * p₂ = ((a * Cartan.diagPow (w.adicCompletion E) n (fun i => (j : ℤ) * ν i) * b : GL (Fin n) (w.adicCompletion E)) :
          Matrix (Fin n) (Fin n) (w.adicCompletion E)).charpoly →
        ‖p₁.coeff 0‖ * 2 ^ j ≤ 1 ∨ ‖p₂.coeff 0‖ * 2 ^ j ≤ 1 := by
  intro hA E _ _ w n ν hν hsum hJ j hj a ha b hb p₁ p₂ hm₁ hm₂ hd₁ hd₂ hp
  classical
  have hϖ : ((GLnLocal.uniformizer (w.adicCompletion E) : _) : w.adicCompletion E) ≠ 0 :=
    GLnLocal.uniformizer_ne_zero _
  have hr := nrm_unif w
  have hdiag : ∀ J : Finset (Fin n), ∏ i ∈ J, ((Cartan.diagPow (w.adicCompletion E) n (fun i => (j : ℤ) * ν i) :
      GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i i =
      ((GLnLocal.uniformizer (w.adicCompletion E) : _) : w.adicCompletion E) ^ ((j : ℤ) * ∑ i ∈ J, ν i) := by
    intro J
    rw [Finset.mul_sum, ← prod_zp _ hϖ]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Cartan.coe_diagPow, Matrix.diagonal_apply_eq]
  generalize ((GLnLocal.uniformizer (w.adicCompletion E) : _) : w.adicCompletion E) = ϖ at hϖ hr hdiag
  have hr0 : 0 < ‖ϖ‖ := norm_pos_iff.2 hϖ
  have hinj : Function.Injective (fun i => (j : ℤ) * ν i) := fun x y h =>
    hν (mul_left_cancel₀ (by exact_mod_cast hj.ne') h)
  obtain ⟨J, hJc, hJv⟩ := hA (w.adicCompletion E) n _ hinj a ha b hb p₁ hm₁ ⟨p₂, hp.symm⟩
  have hcp : (p₁ * p₂).natDegree = n := by
    rw [hp, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  obtain ⟨J', hJ'c, hJ'v⟩ := hA (w.adicCompletion E) n _ hinj a ha b hb (p₁ * p₂) (hm₁.mul hm₂) (hp ▸ dvd_rfl)
  have hJ'u : J' = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hJ'c, hcp, Fintype.card_fin]
  have hdeg : p₁.natDegree + p₂.natDegree = n := by
    rw [← hm₁.natDegree_mul hm₂]; exact hcp
  have hne : J.Nonempty := Finset.card_pos.1 (by omega)
  have hnu : J ≠ Finset.univ := by
    intro h
    rw [h, Finset.card_univ, Fintype.card_fin] at hJc
    omega
  have hs := hJ J hne hnu
  have h1 : ‖p₁.coeff 0‖ = ‖ϖ‖ ^ ((j : ℤ) * ∑ i ∈ J, ν i) := by
    rw [nrm_eq w (hJv.trans (by rw [hdiag])), norm_zpow]
  have h2 : ‖p₁.coeff 0‖ * ‖p₂.coeff 0‖ = 1 := by
    rw [← norm_mul, ← mul_coeff_zero, nrm_eq w (hJ'v.trans (congrArg _ (hdiag J'))), hJ'u, hsum]
    simp
  generalize (∑ i ∈ J, ν i) = s at hs h1
  rcases lt_or_gt_of_ne hs with hlt | hgt
  · right
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ -s)
    have hs' : s = -(m : ℤ) := by omega
    have hm1 : 1 ≤ m := by omega
    have h3 : ‖p₂.coeff 0‖ = ‖ϖ‖ ^ (j * m) := by
      have h4 : ‖p₁.coeff 0‖ = (‖ϖ‖ ^ (j * m))⁻¹ := by
        rw [h1, hs', mul_neg, zpow_neg, ← Nat.cast_mul, zpow_natCast]
      rw [h4] at h2
      exact (inv_mul_eq_one₀ (pow_ne_zero _ hr0.ne')).1 h2 |>.symm
    rw [h3]
    exact fin_real _ hr0 hr j m hm1
  · left
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hgt.le
    have hm1 : 1 ≤ m := by omega
    rw [h1, hm, ← Nat.cast_mul, zpow_natCast]
    exact fin_real _ hr0 hr j m hm1
