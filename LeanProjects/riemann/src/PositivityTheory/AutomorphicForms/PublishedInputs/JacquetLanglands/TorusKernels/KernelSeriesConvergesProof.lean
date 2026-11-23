import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.KernelSeriesConvergence

open UpperTheory.Esk

variable {F I Gf : Type} [Field F] [Group Gf] [Fintype I]

theorem ht_e (D : Dat F I Gf) (z : X I) (x : Gf) :
    D.Ht ![0, 1] z x = (∏ v, |(z v).1.im|) * D.hf ![0, 1] x := by
  simp [Dat.Ht]

theorem kap_nonneg (z w : P) : 0 ≤ kap z w := by
  unfold kap; split_ifs <;> positivity

theorem Kap_nonneg (k : I → ℕ) (z w : X I) : 0 ≤ Kap k z w :=
  Finset.prod_nonneg fun v _ => Real.rpow_nonneg (kap_nonneg _ _) _

theorem N_pos (z : X I) : 0 < ∏ v, |(z v).1.im| :=
  Finset.prod_pos fun v _ => abs_pos.2 (z v).2

theorem fix_of (γ : PG F) (h : γ.out 1 0 = 0) : Fix ![0, 1] γ := by
  refine ⟨γ.out 1 1, ?_⟩
  ext j; fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, h]

theorem e_ne : (![0, 1] : Fin 2 → F) ≠ 0 := fun h => by simpa using congrFun h 1

theorem kap_split (k : I → ℕ) (z w : X I) :
    Kap k z w = (Kap k z w * ∏ v, (|(z v).1.im| / |(w v).1.im|) ^ ((1 : ℝ) / 2)) *
      ((∏ v, |(w v).1.im|) / ∏ v, |(z v).1.im|) ^ ((1 : ℝ) / 2) := by
  rw [← Finset.prod_div_distrib, ← Real.finsetProd_rpow _ _ (fun v _ => by positivity), mul_assoc,
    ← Finset.prod_mul_distrib, Finset.prod_eq_one, mul_one]
  intro v _
  have h1 := abs_pos.2 (z v).2
  have h2 := abs_pos.2 (w v).2
  rw [← Real.mul_rpow (by positivity) (by positivity),
    show |(z v).1.im| / |(w v).1.im| * (|(w v).1.im| / |(z v).1.im|) = 1 by field_simp, Real.one_rpow]

theorem ratio (hE0d : E0d) {ι : Type} [Fintype ι] (D : Dat F I Gf) (hax : D.Ax) (a : ι → Gf) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (y : D.Y) (γ : PG F) (i : ι), ¬ Fix ![0, 1] γ →
      γ • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H) →
      (∏ v, |((γ • y.2 : D.Xs) v).1.im|) * D.HtY ![0, 1] y ^ 2 ≤ C' * ∏ v, |(y.2 v).1.im| := by
  obtain ⟨h1, h2, -, h4, h5, -⟩ := hE0d F I Gf D hax
  have he : (![0, 1] : Fin 2 → F) ≠ 0 := e_ne
  choose Cm hCm using fun i => hax.mul (a i)⁻¹
  refine ⟨∑ i, max (Cm i) 0, Finset.sum_nonneg fun i _ => le_max_right _ _, fun y γ i hγ hi => ?_⟩
  have hγ' : γ.out 1 0 ≠ 0 := fun h => hγ (fix_of γ h)
  have hy : D.HtY ![0, 1] y = (∏ v, |(y.2 v).1.im|) * D.hf ![0, 1] (D.rep y.1) := ht_e D y.2 (D.rep y.1)
  have hgy : D.HtY ![0, 1] (γ • y) =
      (∏ v, |((γ • y.2 : D.Xs) v).1.im|) * D.hf ![0, 1] (D.rep y.1 * a i) := by
    have : γ • y = (((D.rep y.1 * a i : Gf) : Gf ⧸ D.H), γ • y.2) := Prod.ext hi rfl
    rw [this]; exact (h1 _ he _ _).trans (ht_e D _ _)
  have hprod : D.HtY ![0, 1] (γ • y) * D.HtY ![0, 1] y ≤ 1 := by
    have := h2 _ he γ.out y
    rw [QuotientGroup.out_eq'] at this
    rw [this, mul_comm]
    apply h5
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using hγ'
  have hx : 0 < D.hf ![0, 1] (D.rep y.1) := hax.pos _ he _
  have hxa : 0 < D.hf ![0, 1] (D.rep y.1 * a i) := hax.pos _ he _
  have hmul : D.hf ![0, 1] (D.rep y.1) ≤ Cm i * D.hf ![0, 1] (D.rep y.1 * a i) := by
    simpa using hCm i _ he (D.rep y.1 * a i)
  have hCm0 : 0 ≤ Cm i := by nlinarith
  have hNg : 0 ≤ ∏ v, |((γ • y.2 : D.Xs) v).1.im| := Finset.prod_nonneg fun v _ => abs_nonneg _
  have hN := (N_pos y.2).le
  have hHt : 0 ≤ D.HtY ![0, 1] y := (h4 _ he y).le
  have hHg : 0 ≤ D.HtY ![0, 1] (γ • y) := (h4 _ he _).le
  have hCi : Cm i ≤ ∑ j, max (Cm j) 0 :=
    (le_max_left _ _).trans (Finset.single_le_sum (f := fun j => max (Cm j) 0) (fun j _ => le_max_right (Cm j) 0) (Finset.mem_univ i))
  have e1 : (∏ v, |((γ • y.2 : D.Xs) v).1.im|) * D.HtY ![0, 1] y ^ 2 =
      ((∏ v, |((γ • y.2 : D.Xs) v).1.im|) * D.hf ![0, 1] (D.rep y.1)) * D.HtY ![0, 1] y * ∏ v, |(y.2 v).1.im| := by
    rw [sq, hy]; ring
  have e2 : (∏ v, |((γ • y.2 : D.Xs) v).1.im|) * D.hf ![0, 1] (D.rep y.1) ≤ Cm i * D.HtY ![0, 1] (γ • y) := by
    rw [hgy]; nlinarith [mul_le_mul_of_nonneg_left hmul hNg]
  rw [e1]
  calc ((∏ v, |((γ • y.2 : D.Xs) v).1.im|) * D.hf ![0, 1] (D.rep y.1)) * D.HtY ![0, 1] y * ∏ v, |(y.2 v).1.im|
      ≤ (Cm i * D.HtY ![0, 1] (γ • y)) * D.HtY ![0, 1] y * ∏ v, |(y.2 v).1.im| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right e2 hHt) hN
    _ = Cm i * (D.HtY ![0, 1] (γ • y) * D.HtY ![0, 1] y) * ∏ v, |(y.2 v).1.im| := by ring
    _ ≤ Cm i * 1 * ∏ v, |(y.2 v).1.im| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hCm0) hN
    _ ≤ (∑ j, max (Cm j) 0) * ∏ v, |(y.2 v).1.im| := by
        rw [mul_one]; exact mul_le_mul_of_nonneg_right hCi hN

theorem main (hE0c : KernelTermsInvariantBounded) (hE0d : E0d) (hPack : Pack) (hMult : Mult) (hKI : KapInt)
    {ι : Type} [Fintype ι] (D : Dat F I Gf) (k : I → ℕ) (a : ι → Gf) (hyp : D.Hyp k a) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ C : ℝ≥0, ∀ y : D.Y, c₀ ≤ D.HtY ![0, 1] y →
      ∑' γ : {γ : PG F // ¬ Fix ![0, 1] γ}, ‖D.kk k a γ.1 y‖ₑ ≤ C := by
  have he : (![0, 1] : Fin 2 → F) ≠ 0 := e_ne
  obtain ⟨-, -, -, ⟨CE, hCE⟩, hTe, -⟩ := hE0c F I Gf ι D k a hyp
  obtain ⟨C', hC'0, hC'⟩ := ratio hE0d D hyp.ax a
  obtain ⟨Cp, hCp⟩ := hPack F I Gf D hyp.ax
  obtain ⟨CM, hCM⟩ := hMult F I Gf D hyp.ax (1 / 16) c₀ (by norm_num) hc₀
  obtain ⟨CK, A, hK⟩ := hKI I k hyp.four
  have hm : ∀ v, Measurable fun w : D.Xs => (w v).1.im := fun v =>
    Complex.measurable_im.comp (measurable_subtype_coe.comp (measurable_pi_apply v))
  refine ⟨(Fintype.card ι : ℝ≥0) * Cp * A * CK *
    Real.toNNReal (max CE 0 * Real.sqrt C' * max CM 0 * (1 + 1 / c₀)), fun y hy => ?_⟩
  have hHt : 0 < D.HtY ![0, 1] y := hc₀.trans_le hy
  set Ht := D.HtY ![0, 1] y with hHtdef
  set h : D.Xs → ℝ≥0∞ := fun w => ENNReal.ofReal (Kap k y.2 w * ∏ v, (|(y.2 v).1.im| / |(w v).1.im|) ^ ((1 : ℝ) / 2))
    with hhdef
  set K : ℝ := max CE 0 * Real.sqrt C' / Ht with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ γ : {γ : PG F // ¬ Fix ![0, 1] γ}, ‖D.kk k a γ.1 y‖ₑ ≤
      ∑ i, ({γ' : PG F | γ' • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}).indicator
        (fun γ' => ENNReal.ofReal K * h (γ' • y.2)) γ.1 := by
    rintro ⟨γ, hγ⟩
    by_cases h0 : D.Te a γ.out (D.rep y.1) = 0
    · have : D.kk k a γ y = 0 := by simp [Dat.kk, Dat.kt, h0]
      simp [this]
    obtain ⟨i, hi⟩ := hTe γ y.1 h0
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun i => ({γ' : PG F | γ' • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}).indicator
        (fun γ' => ENNReal.ofReal K * h (γ' • y.2)) γ) (fun _ _ => bot_le) (Finset.mem_univ i))
    simp only [Set.indicator_of_mem (show γ ∈ {γ' : PG F | γ' • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)} from hi)]
    rw [hhdef, ← ofReal_norm, ← ENNReal.ofReal_mul hK0]
    apply ENNReal.ofReal_le_ofReal
    have hr := hC' y γ i hγ hi
    have hN := N_pos y.2
    have hsq : ((∏ v, |((γ • y.2 : D.Xs) v).1.im|) / ∏ v, |(y.2 v).1.im|) ^ ((1 : ℝ) / 2) ≤ Real.sqrt C' / Ht := by
      rw [← Real.sqrt_eq_rpow]
      have : (∏ v, |((γ • y.2 : D.Xs) v).1.im|) / ∏ v, |(y.2 v).1.im| ≤ C' / Ht ^ 2 := by
        rw [div_le_div_iff₀ hN (by positivity)]; linarith
      calc Real.sqrt ((∏ v, |((γ • y.2 : D.Xs) v).1.im|) / ∏ v, |(y.2 v).1.im|) ≤ Real.sqrt (C' / Ht ^ 2) :=
            Real.sqrt_le_sqrt this
        _ = Real.sqrt C' / Ht := by rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hHt.le]
    have hX : 0 ≤ Kap k y.2 (γ • y.2) * ∏ v, (|(y.2 v).1.im| / |((γ • y.2 : D.Xs) v).1.im|) ^ ((1 : ℝ) / 2) :=
      mul_nonneg (Kap_nonneg _ _ _) (Finset.prod_nonneg fun v _ => by positivity)
    calc ‖D.kk k a γ y‖ ≤ CE * Kap k y.2 (γ • y.2 : D.Xs) := hCE γ y
      _ ≤ max CE 0 * Kap k y.2 (γ • y.2 : D.Xs) := mul_le_mul_of_nonneg_right (le_max_left _ _) (Kap_nonneg _ _ _)
      _ = max CE 0 * ((Kap k y.2 (γ • y.2) * ∏ v, (|(y.2 v).1.im| / |((γ • y.2 : D.Xs) v).1.im|) ^ ((1 : ℝ) / 2)) *
            ((∏ v, |((γ • y.2 : D.Xs) v).1.im|) / ∏ v, |(y.2 v).1.im|) ^ ((1 : ℝ) / 2)) := by
          congr 1; exact kap_split k y.2 _
      _ ≤ max CE 0 * ((Kap k y.2 (γ • y.2) * ∏ v, (|(y.2 v).1.im| / |((γ • y.2 : D.Xs) v).1.im|) ^ ((1 : ℝ) / 2)) *
            (Real.sqrt C' / Ht)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hX) (le_max_right _ _)
      _ = K * (Kap k y.2 (γ • y.2) * ∏ v, (|(y.2 v).1.im| / |((γ • y.2 : D.Xs) v).1.im|) ^ ((1 : ℝ) / 2)) := by
          rw [hKdef]; ring

  have hmeas : Measurable h :=
    ((hK y.2).1.mul (Finset.measurable_prod _ fun v _ =>
      (measurable_const.div (hm v).abs).pow_const _)).ennreal_ofReal
  have hA : ∀ w w' : D.Xs, Near (1 / 2) w w' → h w ≤ A * h w' := by
    intro w w' hn
    have := ENNReal.ofReal_le_ofReal ((hK y.2).2.2.2 w w' hn).2
    rwa [ENNReal.ofReal_mul A.coe_nonneg, ENNReal.ofReal_coe_nnreal] at this
  obtain ⟨hfin, hcard⟩ := hCM y ![0, 1] he hy
  have hcard' : ((({γ : PG F | γ • y.1 = y.1 ∧ Near (1 / 16) y.2 (γ • y.2 : D.Xs)}.ncard : ℕ) : ℝ≥0∞)) ≤
      ENNReal.ofReal (max CM 0 * (1 + Ht)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (hcard.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  have hint : ∫⁻ w, h w ≤ CK := (hK y.2).2.2.1
  have hcos : ∀ i, ∑' γ : PG F, ({γ' : PG F | γ' • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}).indicator
        (fun γ' => ENNReal.ofReal K * h (γ' • y.2)) γ ≤
      ENNReal.ofReal K * (Cp * A * ENNReal.ofReal (max CM 0 * (1 + Ht)) * CK) := by
    intro i
    rw [← tsum_subtype, ENNReal.tsum_mul_left]
    gcongr
    calc ∑' γ : {γ' : PG F | γ' • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}, h (γ.1 • y.2)
        ≤ Cp * A * ({γ : PG F | γ • y.1 = y.1 ∧ Near (1 / 16) y.2 (γ • y.2 : D.Xs)}.ncard : ℝ≥0∞) * ∫⁻ w, h w :=
          hCp y _ h A hmeas hA hfin
      _ ≤ Cp * A * ENNReal.ofReal (max CM 0 * (1 + Ht)) * CK := by gcongr
  have hfinal : ENNReal.ofReal K * ENNReal.ofReal (max CM 0 * (1 + Ht)) ≤
      ENNReal.ofReal (max CE 0 * Real.sqrt C' * max CM 0 * (1 + 1 / c₀)) := by
    rw [← ENNReal.ofReal_mul hK0]
    apply ENNReal.ofReal_le_ofReal
    have h1 : (1 + Ht) / Ht ≤ 1 + 1 / c₀ := by
      have := one_div_le_one_div_of_le hc₀ hy
      rw [add_div, div_self hHt.ne']; linarith
    have h2 : 0 ≤ max CE 0 * Real.sqrt C' * max CM 0 := by positivity
    calc K * (max CM 0 * (1 + Ht)) = max CE 0 * Real.sqrt C' * max CM 0 * ((1 + Ht) / Ht) := by
          rw [hKdef]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 h2
  calc ∑' γ : {γ : PG F // ¬ Fix ![0, 1] γ}, ‖D.kk k a γ.1 y‖ₑ
      ≤ ∑' γ : {γ : PG F // ¬ Fix ![0, 1] γ}, ∑ i, ({γ' : PG F | γ' • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}).indicator
        (fun γ' => ENNReal.ofReal K * h (γ' • y.2)) γ.1 := ENNReal.tsum_le_tsum hpt
    _ ≤ ∑' γ : PG F, ∑ i, ({γ' : PG F | γ' • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}).indicator
        (fun γ' => ENNReal.ofReal K * h (γ' • y.2)) γ :=
        ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
    _ = ∑ i, ∑' γ : PG F, ({γ' : PG F | γ' • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}).indicator
        (fun γ' => ENNReal.ofReal K * h (γ' • y.2)) γ := Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)
    _ ≤ ∑ i : ι, ENNReal.ofReal K * (Cp * A * ENNReal.ofReal (max CM 0 * (1 + Ht)) * CK) :=
        Finset.sum_le_sum fun i _ => hcos i
    _ = (Fintype.card ι : ℝ≥0∞) * Cp * A * CK * (ENNReal.ofReal K * ENNReal.ofReal (max CM 0 * (1 + Ht))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ (Fintype.card ι : ℝ≥0∞) * Cp * A * CK * ENNReal.ofReal (max CE 0 * Real.sqrt C' * max CM 0 * (1 + 1 / c₀)) := by
        gcongr
    _ = (((Fintype.card ι : ℝ≥0) * Cp * A * CK *
          Real.toNNReal (max CE 0 * Real.sqrt C' * max CM 0 * (1 + 1 / c₀)) : ℝ≥0) : ℝ≥0∞) := by
        rw [ENNReal.ofReal]; push_cast; ring

end UpperTheory.Esk.KernelSeriesConvergence

open UpperTheory.Esk in
theorem UpperTheory.Esk.kernel_series_converges_proof : UpperTheory.Esk.B1b → UpperTheory.Esk.KernelTermsInvariantBounded → UpperTheory.Esk.E0d → UpperTheory.Esk.Pack → UpperTheory.Esk.Mult → UpperTheory.Esk.KapInt → UpperTheory.Esk.E1 := by
  intro _ hE0c hE0d hPack hMult hKI F I Gf ι _ _ _ _ D k a hyp c₀ hc₀
  obtain ⟨C, hC⟩ := KernelSeriesConvergence.main hE0c hE0d hPack hMult hKI D k a hyp c₀ hc₀
  refine ⟨C, fun y s hs hy => ?_⟩
  obtain ⟨-, h2, -, -, -, -, -, -, -, h10, h11⟩ := hE0d F I Gf D hyp.ax
  obtain ⟨-, h2c, -⟩ := hE0c F I Gf ι D k a hyp
  obtain ⟨δ, hδ⟩ := h10 s hs
  have he : (![0, 1] : Fin 2 → F) ≠ 0 := KernelSeriesConvergence.e_ne
  have hy' : c₀ ≤ D.HtY ![0, 1] ((δ : PG F) • y) := by rw [h2 _ he δ y, hδ]; exact hy
  have hfix : ∀ γ : PG F, ¬ Fix s γ ↔ ¬ Fix ![0, 1] (MulAut.conj (δ : PG F) γ) := by
    intro γ
    have := h11 ![0, 1] γ.out δ
    rw [QuotientGroup.out_eq', hδ] at this
    exact not_congr this.symm
  let e : {γ : PG F // ¬ Fix s γ} ≃ {γ : PG F // ¬ Fix ![0, 1] γ} :=
    (MulAut.conj (δ : PG F)).toEquiv.subtypeEquiv hfix
  calc ∑' γ : {γ : PG F // ¬ Fix s γ}, ‖D.kk k a γ.1 y‖ₑ
      = ∑' γ : {γ : PG F // ¬ Fix s γ}, ‖D.kk k a (e γ).1 ((δ : PG F) • y)‖ₑ := by
        congr 1; funext γ
        rw [show (e γ).1 = (δ : PG F) * γ.1 * (δ : PG F)⁻¹ from rfl, h2c]
    _ = ∑' γ : {γ : PG F // ¬ Fix ![0, 1] γ}, ‖D.kk k a γ.1 ((δ : PG F) • y)‖ₑ :=
        e.tsum_eq (fun γ => ‖D.kk k a γ.1 ((δ : PG F) • y)‖ₑ)
    _ ≤ C := hC _ hy'
