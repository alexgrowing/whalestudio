import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.HeightsOnQuotientLemmas

open UpperTheory.Esk

variable {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf)

theorem rep_mk (x : Gf) : ∃ h ∈ D.H, D.rep (show D.Om from (x : Gf ⧸ D.H)) = x * h := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul D.H x
  exact ⟨h, h.2, hh⟩

theorem htY_mk (hA : D.Ax) (s : Fin 2 → F) (hs : s ≠ 0) (z : D.Xs) (x : Gf) :
    D.HtY s ((x : Gf ⧸ D.H), z) = D.Ht s z x := by
  obtain ⟨h, hh, e⟩ := rep_mk D x
  simp only [Dat.HtY, Dat.Ht]
  rw [e, hA.lev s hs x h hh]

theorem vecMul_ne {s : Fin 2 → F} (hs : s ≠ 0) (γ : GL (Fin 2) F) : s ᵥ* γ.val ≠ 0 := by
  intro h
  apply hs
  have := congrArg (fun t => t ᵥ* (γ⁻¹ : GL (Fin 2) F).val) h
  simp only [Matrix.vecMul_vecMul, Matrix.zero_vecMul] at this
  rwa [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one] at this

theorem im_smul (g : GL (Fin 2) ℝ) (z : P) : (g • z).1.im = g.val.det * z.1.im / Complex.normSq (den g z.1) := by
  rw [coe_smul, im_div]

theorem fac (g : GL (Fin 2) ℝ) (z : P) (a b : ℝ) :
    |(g • z).1.im| / ‖(a : ℂ) * (g • z).1 + b‖ ^ 2 =
      |g.val.det| * (|z.1.im| / ‖((a * g 0 0 + b * g 1 0 : ℝ) : ℂ) * z.1 + ((a * g 0 1 + b * g 1 1 : ℝ) : ℂ)‖ ^ 2) := by
  have h0 := den_ne g z.2
  have e : (a : ℂ) * (g • z).1 + b =
      (((a * g 0 0 + b * g 1 0 : ℝ) : ℂ) * z.1 + ((a * g 0 1 + b * g 1 1 : ℝ) : ℂ)) / den g z.1 := by
    rw [coe_smul, eq_div_iff h0, add_mul, mul_assoc, div_mul_cancel₀ _ h0]
    simp only [num, den]
    push_cast
    ring
  have hn : 0 < ‖den g z.1‖ ^ 2 := by positivity
  rw [e, im_smul, norm_div, div_pow, abs_div, abs_mul, Complex.normSq_eq_norm_sq,
    abs_of_nonneg (sq_nonneg ‖den g z.1‖), div_div_div_cancel_right₀ hn.ne', mul_div_assoc]

theorem r_apply (v : I) (γ : GL (Fin 2) F) (i j : Fin 2) : (D.r v γ) i j = D.σ v (γ i j) := rfl

theorem r_det (v : I) (γ : GL (Fin 2) F) : (D.r v γ).val.det = D.σ v γ.val.det := by
  rw [RingHom.map_det]
  rfl

theorem ht_act (hA : D.Ax) (s : Fin 2 → F) (hs : s ≠ 0) (γ : GL (Fin 2) F) (z : X I) (x : Gf) :
    D.Ht s (D.act γ z) (D.j γ * x) = D.Ht (s ᵥ* γ.val) z x := by
  have hr := hA.rat s hs γ x
  simp only [Dat.Ht, Dat.act]
  rw [← hr]
  have key : ∀ v, |((D.r v γ • z v : P)).1.im| / ‖(D.σ v (s 0) : ℂ) * (D.r v γ • z v).1 + (D.σ v (s 1) : ℂ)‖ ^ 2 =
      |D.σ v γ.val.det| * (|(z v).1.im| /
        ‖(D.σ v ((s ᵥ* γ.val) 0) : ℂ) * (z v).1 + (D.σ v ((s ᵥ* γ.val) 1) : ℂ)‖ ^ 2) := by
    intro v
    have e0 : D.σ v (s 0) * (D.r v γ) 0 0 + D.σ v (s 1) * (D.r v γ) 1 0 = D.σ v ((s ᵥ* γ.val) 0) := by
      simp [r_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    have e1 : D.σ v (s 0) * (D.r v γ) 0 1 + D.σ v (s 1) * (D.r v γ) 1 1 = D.σ v ((s ᵥ* γ.val) 1) := by
      simp [r_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    rw [fac, e0, e1, r_det]
  rw [Finset.prod_congr rfl (fun v _ => key v), Finset.prod_mul_distrib]
  ring

theorem htY_smul (hA : D.Ax) (s : Fin 2 → F) (hs : s ≠ 0) (γ : GL (Fin 2) F) (y : D.Y) :
    D.HtY s ((γ : PG F) • y) = D.HtY (s ᵥ* γ.val) y := by
  obtain ⟨ω, z⟩ := y
  obtain ⟨x, rfl⟩ : ∃ x : Gf, (show D.Om from (x : Gf ⧸ D.H)) = ω := QuotientGroup.mk_surjective ω
  show D.HtY s (((D.j γ * x : Gf) : Gf ⧸ D.H), D.act γ z) = D.HtY (s ᵥ* γ.val) ((x : Gf ⧸ D.H), z)
  exact (htY_mk D hA s hs _ _).trans ((ht_act D hA s hs γ z x).trans (htY_mk D hA _ (vecMul_ne hs γ) z x).symm)

theorem htY_smulc (hA : D.Ax) (s : Fin 2 → F) (hs : s ≠ 0) (c : F) (hc : c ≠ 0) : D.HtY (c • s) = D.HtY s := by
  funext y
  simp only [Dat.HtY, Dat.Ht]
  rw [hA.smul s hs c hc]
  have hσ : ∀ v, D.σ v c ≠ 0 := fun v => (map_ne_zero (D.σ v)).2 hc
  have key : ∀ v, |(y.2 v).1.im| / ‖(D.σ v ((c • s) 0) : ℂ) * (y.2 v).1 + (D.σ v ((c • s) 1) : ℂ)‖ ^ 2 =
      (|(y.2 v).1.im| / ‖(D.σ v (s 0) : ℂ) * (y.2 v).1 + (D.σ v (s 1) : ℂ)‖ ^ 2) / D.σ v c ^ 2 := by
    intro v
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.ofReal_mul]
    rw [show (D.σ v c : ℂ) * D.σ v (s 0) * (y.2 v).1 + D.σ v c * D.σ v (s 1) =
        D.σ v c * (D.σ v (s 0) * (y.2 v).1 + D.σ v (s 1)) by ring, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      mul_pow, sq_abs, div_div, mul_comm (D.σ v c ^ 2)]
  rw [Finset.prod_congr rfl (fun v _ => key v), Finset.prod_div_distrib]
  have hp : ∏ v, D.σ v c ^ 2 ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero 2 (hσ v)
  field_simp

theorem lin_ne (s : Fin 2 → F) (hs : s ≠ 0) (v : I) (z : P) : (D.σ v (s 0) : ℂ) * z.1 + (D.σ v (s 1) : ℂ) ≠ 0 := by
  intro h
  have h1 := congrArg Complex.im h
  have h2 := congrArg Complex.re h
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.zero_im, Complex.add_re, Complex.mul_re, sub_zero, Complex.zero_re] at h1 h2
  have a0 : D.σ v (s 0) = 0 := (mul_eq_zero.1 h1).resolve_right z.2
  rw [a0, zero_mul, zero_add] at h2
  apply hs
  funext i
  fin_cases i
  · exact (map_eq_zero (D.σ v)).1 a0
  · exact (map_eq_zero (D.σ v)).1 h2

theorem htY_pos (hA : D.Ax) (s : Fin 2 → F) (hs : s ≠ 0) (y : D.Y) : 0 < D.HtY s y :=
  mul_pos (Finset.prod_pos fun v _ => div_pos (abs_pos.2 (y.2 v).2)
    (pow_pos (norm_pos_iff.2 (lin_ne D s hs v (y.2 v))) 2)) (hA.pos s hs _)

theorem loc (a b a' b' : ℝ) (z : P) (hw : (a : ℂ) * z.1 + b ≠ 0) (hw' : (a' : ℂ) * z.1 + b' ≠ 0) :
    |z.1.im| / ‖(a : ℂ) * z.1 + b‖ ^ 2 * (|z.1.im| / ‖(a' : ℂ) * z.1 + b'‖ ^ 2) * (a * b' - b * a') ^ 2 ≤ 1 := by
  have key : |z.1.im| * |a * b' - b * a'| ≤ ‖(a : ℂ) * z.1 + b‖ * ‖(a' : ℂ) * z.1 + b'‖ := by
    have e : (((a : ℂ) * z.1 + b) * conj ((a' : ℂ) * z.1 + b')).im = (a * b' - b * a') * z.1.im := by
      simp [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    calc |z.1.im| * |a * b' - b * a'| = |(((a : ℂ) * z.1 + b) * conj ((a' : ℂ) * z.1 + b')).im| := by
          rw [e, abs_mul, mul_comm]
      _ ≤ ‖((a : ℂ) * z.1 + b) * conj ((a' : ℂ) * z.1 + b')‖ := Complex.abs_im_le_norm _
      _ = _ := by rw [norm_mul, Complex.norm_conj]
  have p1 := norm_pos_iff.2 hw
  have p2 := norm_pos_iff.2 hw'
  have k2 := pow_le_pow_left₀ (by positivity) key 2
  rw [← sq_abs (a * b' - b * a'), div_mul_div_comm, div_mul_eq_mul_div, div_le_one (by positivity)]
  calc |z.1.im| * |z.1.im| * |a * b' - b * a'| ^ 2 = (|z.1.im| * |a * b' - b * a'|) ^ 2 := by ring
    _ ≤ (‖(a : ℂ) * z.1 + b‖ * ‖(a' : ℂ) * z.1 + b'‖) ^ 2 := k2
    _ = _ := by ring

theorem ne_of_det {s s' : Fin 2 → F} (hd : s 0 * s' 1 - s 1 * s' 0 ≠ 0) : s ≠ 0 ∧ s' ≠ 0 := by
  constructor
  · rintro rfl; simp at hd
  · rintro rfl; simp at hd

theorem htY_prod (hA : D.Ax) (s s' : Fin 2 → F) (hd : s 0 * s' 1 - s 1 * s' 0 ≠ 0) (y : D.Y) :
    D.HtY s y * D.HtY s' y ≤ 1 := by
  obtain ⟨hs, hs'⟩ := ne_of_det hd
  have hx := hA.prod s s' hd (D.rep y.1)
  simp only [Dat.HtY, Dat.Ht]
  have hl : ∀ v, |(y.2 v).1.im| / ‖(D.σ v (s 0) : ℂ) * (y.2 v).1 + (D.σ v (s 1) : ℂ)‖ ^ 2 *
      (|(y.2 v).1.im| / ‖(D.σ v (s' 0) : ℂ) * (y.2 v).1 + (D.σ v (s' 1) : ℂ)‖ ^ 2) *
      D.σ v (s 0 * s' 1 - s 1 * s' 0) ^ 2 ≤ 1 := by
    intro v
    rw [map_sub, map_mul, map_mul]
    exact loc _ _ _ _ _ (lin_ne D s hs v _) (lin_ne D s' hs' v _)
  calc (∏ v, |(y.2 v).1.im| / ‖(D.σ v (s 0) : ℂ) * (y.2 v).1 + (D.σ v (s 1) : ℂ)‖ ^ 2) * D.hf s (D.rep y.1) *
        ((∏ v, |(y.2 v).1.im| / ‖(D.σ v (s' 0) : ℂ) * (y.2 v).1 + (D.σ v (s' 1) : ℂ)‖ ^ 2) * D.hf s' (D.rep y.1))
      = ((∏ v, |(y.2 v).1.im| / ‖(D.σ v (s 0) : ℂ) * (y.2 v).1 + (D.σ v (s 1) : ℂ)‖ ^ 2) *
        (∏ v, |(y.2 v).1.im| / ‖(D.σ v (s' 0) : ℂ) * (y.2 v).1 + (D.σ v (s' 1) : ℂ)‖ ^ 2)) *
        (D.hf s (D.rep y.1) * D.hf s' (D.rep y.1)) := by ring
    _ ≤ ((∏ v, |(y.2 v).1.im| / ‖(D.σ v (s 0) : ℂ) * (y.2 v).1 + (D.σ v (s 1) : ℂ)‖ ^ 2) *
        (∏ v, |(y.2 v).1.im| / ‖(D.σ v (s' 0) : ℂ) * (y.2 v).1 + (D.σ v (s' 1) : ℂ)‖ ^ 2)) *
        ∏ v, D.σ v (s 0 * s' 1 - s 1 * s' 0) ^ 2 := mul_le_mul_of_nonneg_left hx (by positivity)
    _ = ∏ v, (|(y.2 v).1.im| / ‖(D.σ v (s 0) : ℂ) * (y.2 v).1 + (D.σ v (s 1) : ℂ)‖ ^ 2 *
      (|(y.2 v).1.im| / ‖(D.σ v (s' 0) : ℂ) * (y.2 v).1 + (D.σ v (s' 1) : ℂ)‖ ^ 2) *
      D.σ v (s 0 * s' 1 - s 1 * s' 0) ^ 2) := by rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    _ ≤ 1 := Finset.prod_le_one (fun v _ => by positivity) (fun v _ => hl v)

theorem meas_ht (s : Fin 2 → F) (x : Gf) : Measurable fun z : D.Xs => D.Ht s z x := by
  unfold Dat.Ht
  refine Measurable.mul_const (Finset.measurable_prod _ fun v _ => ?_) _
  have hz : Measurable fun z : D.Xs => (z v).1 :=
    measurable_subtype_coe.comp (measurable_pi_apply (X := fun _ : I => P) v)
  exact (continuous_abs.measurable.comp (Complex.measurable_im.comp hz)).div
    (((measurable_const.mul hz).add measurable_const).norm.pow_const 2)

theorem meas_htY (hA : D.Ax) (s : Fin 2 → F) : Measurable (D.HtY s) := by
  have := hA.cO
  exact measurable_from_prod_countable_right fun ω => meas_ht D s (D.rep ω)

theorem meas_lam (hA : D.Ax) (T : ℝ) : MeasurableSet (D.abelian₂ T) := by
  have := hA.cF
  have e : D.abelian₂ T = ⋂ s : Fin 2 → F, ⋂ (_ : s ≠ 0), {y | D.HtY s y ≤ T} := by
    ext y
    simp only [Dat.abelian₂, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [e]
  exact MeasurableSet.iInter fun s => MeasurableSet.iInter fun _ => measurableSet_le (meas_htY D hA s) measurable_const

theorem meas_lamF (hA : D.Ax) (T : ℝ) (γ : PG F) : MeasurableSet (D.LamF T γ) := by
  have := hA.cF
  have e : D.LamF T γ = ⋂ s : Fin 2 → F, ⋂ (_ : s ≠ 0), ⋂ (_ : Fix s γ), {y | D.HtY s y ≤ T} := by
    ext y
    simp only [Dat.LamF, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [e]
  exact MeasurableSet.iInter fun s => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
    measurableSet_le (meas_htY D hA s) measurable_const

theorem lam_smul (hA : D.Ax) (T : ℝ) (δ : PG F) (y : D.Y) (h : y ∈ D.abelian₂ T) : δ • y ∈ D.abelian₂ T := by
  obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective δ
  simp only [Dat.abelian₂, Set.mem_ofPred_eq] at h ⊢
  intro s hs
  rw [htY_smul D hA s hs d y]
  exact h _ (vecMul_ne hs d)

theorem fix_mk (t : Fin 2 → F) (g : GL (Fin 2) F) : Fix t (g : PG F) ↔ ∃ c : F, t ᵥ* g.val = c • t := by
  obtain ⟨ζ, hζ, e⟩ : ∃ ζ ∈ Subgroup.center (GL (Fin 2) F), (g : PG F).out = g * ζ := by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.center (GL (Fin 2) F)) g
    exact ⟨h, h.2, hh⟩
  obtain ⟨h1, h2, h3⟩ := center_entries hζ
  have hl : ζ 0 0 ≠ 0 := by
    intro h0
    apply ζ.det_ne_zero
    rw [Matrix.det_fin_two, h1, ← h3, h0]
    ring
  have hv : ∀ u : Fin 2 → F, u ᵥ* (ζ : Matrix (Fin 2) (Fin 2) F) = ζ 0 0 • u := by
    intro u
    funext i
    fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, h1, h2, h3, mul_comm]
  unfold Fix
  rw [e, Units.val_mul, ← Matrix.vecMul_vecMul, hv]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨(ζ 0 0)⁻¹ * c, ?_⟩
    rw [mul_smul, ← hc, smul_smul, inv_mul_cancel₀ hl, one_smul]
  · rintro ⟨c, hc⟩
    exact ⟨ζ 0 0 * c, by rw [hc, smul_smul]⟩

theorem vm_inv (X Y : Fin 2 → F) (δ : GL (Fin 2) F) : X ᵥ* (δ⁻¹ : GL (Fin 2) F).val = Y ↔ X = Y ᵥ* δ.val := by
  constructor
  · rintro rfl
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one]
  · rintro rfl
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]

theorem fix_conj (s : Fin 2 → F) (γ δ : GL (Fin 2) F) :
    Fix s ((δ : PG F) * γ * (δ : PG F)⁻¹) ↔ ∃ c : F, (s ᵥ* δ.val) ᵥ* γ.val = c • (s ᵥ* δ.val) := by
  rw [show ((δ : PG F) * γ * (δ : PG F)⁻¹) = ((δ * γ * δ⁻¹ : GL (Fin 2) F) : PG F) by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv], fix_mk]
  refine exists_congr fun c => ?_
  rw [Units.val_mul, ← Matrix.vecMul_vecMul, vm_inv, Units.val_mul, ← Matrix.vecMul_vecMul, Matrix.smul_vecMul]

theorem lamF_smul (hA : D.Ax) (T : ℝ) (γ δ : PG F) (y : D.Y) (h : y ∈ D.LamF T γ) :
    δ • y ∈ D.LamF T (δ * γ * δ⁻¹) := by
  obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective δ
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
  simp only [Dat.LamF, Set.mem_ofPred_eq] at h ⊢
  intro s hs hf
  rw [htY_smul D hA s hs d y]
  exact h _ (vecMul_ne hs d) ((fix_mk _ g).2 ((fix_conj s g d).1 hf))

theorem line {s0 s : Fin 2 → F} (h0 : s0 ≠ 0) (hs : s ≠ 0) (hd : s0 0 * s 1 - s0 1 * s 0 = 0) :
    ∃ c : F, c ≠ 0 ∧ s = c • s0 := by
  by_cases a : s0 0 = 0
  · have b : s0 1 ≠ 0 := fun b => h0 (by funext i; fin_cases i <;> simp [a, b])
    have hs0 : s 0 = 0 := by
      rw [a, zero_mul, zero_sub, neg_eq_zero] at hd
      exact (mul_eq_zero.1 hd).resolve_left b
    refine ⟨s 1 / s0 1, fun hc => hs ?_, ?_⟩
    · have : s 1 = 0 := by rw [div_eq_zero_iff] at hc; exact hc.resolve_right b
      funext i; fin_cases i <;> simp [hs0, this]
    · funext i; fin_cases i <;> simp [hs0, a, b]
  · refine ⟨s 0 / s0 0, fun hc => hs ?_, ?_⟩
    · have e0 : s 0 = 0 := by rw [div_eq_zero_iff] at hc; exact hc.resolve_right a
      have e1 : s 1 = 0 := by
        rw [e0, mul_zero, sub_zero] at hd
        exact (mul_eq_zero.1 hd).resolve_left a
      funext i; fin_cases i <;> simp [e0, e1]
    · funext i
      fin_cases i
      · simp [a]
      · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
        field_simp
        linear_combination hd

theorem bounded (hA : D.Ax) (y : D.Y) : ∃ T₀, ∀ T, T₀ ≤ T → y ∈ D.abelian₂ T := by
  by_cases h : ∃ s0 : Fin 2 → F, s0 ≠ 0 ∧ 1 < D.HtY s0 y
  · obtain ⟨s0, h0, h1⟩ := h
    refine ⟨max 1 (D.HtY s0 y), fun T hT s hs => ?_⟩
    by_cases h2 : D.HtY s y ≤ 1
    · exact h2.trans ((le_max_left _ _).trans hT)
    · push Not at h2
      by_cases hd : s0 0 * s 1 - s0 1 * s 0 = 0
      · obtain ⟨c, hc, rfl⟩ := line h0 hs hd
        rw [htY_smulc D hA s0 h0 c hc]
        exact (le_max_right _ _).trans hT
      · exfalso
        have := htY_prod D hA s0 s hd y
        nlinarith
  · push Not at h
    exact ⟨1, fun T hT s hs => (h s hs).trans hT⟩

theorem row (s : Fin 2 → F) (hs : s ≠ 0) : ∃ γ : GL (Fin 2) F, ![0, 1] ᵥ* γ.val = s := by
  by_cases h0 : s 0 = 0
  · have h1 : s 1 ≠ 0 := fun h1 => hs (by funext i; fin_cases i <;> simp [h0, h1])
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; s 0, s 1] (by simp [Matrix.det_fin_two_of, h1]), ?_⟩
    funext i
    fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; s 0, s 1] (by simp [Matrix.det_fin_two_of, h0]), ?_⟩
    funext i
    fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

end UpperTheory.Esk.HeightsOnQuotientLemmas

open UpperTheory.Esk.HeightsOnQuotientLemmas in
theorem UpperTheory.Esk.heights_on_quotient_proof : UpperTheory.Esk.B1a → UpperTheory.Esk.E0d := by
  intro _ F I Gf _ _ _ D hA
  refine ⟨fun s hs z x => htY_mk D hA s hs z x, fun s hs γ y => htY_smul D hA s hs γ y,
    fun s hs c hc => htY_smulc D hA s hs c hc, fun s hs y => htY_pos D hA s hs y,
    fun s s' hd y => htY_prod D hA s s' hd y, fun s => meas_htY D hA s,
    fun T => ⟨meas_lam D hA T, fun δ y => ⟨fun h => ?_, lam_smul D hA T δ y⟩⟩,
    fun T γ => ⟨meas_lamF D hA T γ, fun δ y => ⟨fun h => ?_, lamF_smul D hA T γ δ y⟩⟩,
    fun y => bounded D hA y, fun s hs => row s hs, fun s γ δ => fix_conj s γ δ⟩
  · have := lam_smul D hA T δ⁻¹ _ h
    rwa [inv_smul_smul] at this
  · have := lamF_smul D hA T _ δ⁻¹ _ h
    rwa [inv_smul_smul, show δ⁻¹ * (δ * γ * δ⁻¹) * δ⁻¹⁻¹ = γ by group] at this
