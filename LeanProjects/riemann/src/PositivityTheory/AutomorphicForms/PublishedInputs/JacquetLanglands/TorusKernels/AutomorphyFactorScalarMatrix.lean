import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.KernelLevelTransform

open UpperTheory.Esk Classical

set_option linter.unusedSectionVars false

variable {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf)

def tm (k : I → ℕ) (ω : D.Om) (w : X I) (p : X I × Gf) (g : GL (Fin 2) F) : ℂ :=
  D.ee ((D.rep ω)⁻¹ * (D.j g)⁻¹ * p.2) * (qq k p.1 (D.act g w) * D.J k g w)

theorem kern_eq (k : I → ℕ) (y : D.Y) (p : X I × Gf) : D.Kern k y p = ∑' γ : PG F, tm D k y.1 y.2 p γ.out := rfl

theorem ee_mul_right (x : Gf) (h : D.H) : D.ee (x * h) = D.ee x * D.χ h := by
  unfold Dat.ee
  by_cases hx : x ∈ D.H
  · have hxh : x * (h : Gf) ∈ D.H := D.H.mul_mem hx h.2
    rw [dif_pos hxh, dif_pos hx, ← Units.val_mul, ← map_mul]
    rfl
  · have hxh : x * (h : Gf) ∉ D.H := fun hh => hx (by simpa using D.H.mul_mem hh (D.H.inv_mem h.2))
    rw [dif_neg hxh, dif_neg hx, zero_mul]

theorem ee_mul_left (x : Gf) (h : D.H) : D.ee (h * x) = D.χ h * D.ee x := by
  unfold Dat.ee
  by_cases hx : x ∈ D.H
  · have hxh : (h : Gf) * x ∈ D.H := D.H.mul_mem h.2 hx
    rw [dif_pos hxh, dif_pos hx, ← Units.val_mul, ← map_mul]
    rfl
  · have hxh : (h : Gf) * x ∉ D.H := fun hh => hx (by simpa using D.H.mul_mem (D.H.inv_mem h.2) hh)
    rw [dif_neg hxh, dif_neg hx, mul_zero]

theorem norm_ee_le (hD : D.Ax) (x : Gf) : ‖D.ee x‖ ≤ 1 := by
  unfold Dat.ee
  split_ifs with hx
  · exact (hD.χn _).le
  · simp

theorem smulO_out (γ : PG F) (ω : D.Om) : γ • ω = ((D.j γ.out * D.rep ω : Gf) : Gf ⧸ D.H) := by
  have h1 := D.mk_smulO γ.out (D.rep ω)
  rw [QuotientGroup.out_eq'] at h1
  rw [← h1]
  congr 1
  exact (QuotientGroup.out_eq' ω).symm

theorem smulX_out (γ : PG F) (w : D.Xs) : (γ • w : D.Xs) = D.act γ.out w := by
  have h1 := D.mk_smulX γ.out w
  rwa [QuotientGroup.out_eq'] at h1

theorem tm_supp (k : I → ℕ) (ω : D.Om) (w : X I) (γ : PG F) (z : X I) (x : Gf)
    (h : ¬ γ • ω = ((x : Gf) : Gf ⧸ D.H)) : tm D k ω w (z, x) γ.out = 0 := by
  unfold tm
  rw [Dat.ee, dif_neg, zero_mul]
  intro hm
  apply h
  rw [smulO_out]
  apply QuotientGroup.eq.2
  simpa [_root_.mul_inv_rev, mul_assoc] using hm

theorem automorphy_factor_scalar_matrix (k : ℕ) (g : GL (Fin 2) ℝ) (h10 : g 1 0 = 0) (h01 : g 0 1 = 0) (h : g 0 0 = g 1 1) (z : P) :
    j1 k g z = ((SignType.sign (g 0 0) : ℝ) : ℂ) ^ k := by
  have hdet : g.val.det = g 0 0 * g 0 0 := by rw [det_eq, h01, ← h]; ring
  have ha : g 0 0 ≠ 0 := by
    intro h0
    apply g.det_ne_zero
    rw [hdet, h0, zero_mul]
  unfold j1 den
  rw [h10, ← h, hdet]
  have hr : (g 0 0) ^ k * |g 0 0 * g 0 0| ^ (-(k : ℝ) / 2) = (SignType.sign (g 0 0) : ℝ) ^ k := by
    have e1 : |g 0 0 * g 0 0| ^ (-(k : ℝ) / 2) = (|g 0 0| ^ k)⁻¹ := by
      rw [abs_mul, ← sq, ← Real.rpow_natCast_mul (abs_nonneg _), show ((2 : ℕ) : ℝ) * (-(k : ℝ) / 2) = -(k : ℝ) by push_cast; ring,
        Real.rpow_neg (abs_nonneg _), Real.rpow_natCast]
    rw [e1]
    have hb : |g 0 0| ^ k ≠ 0 := pow_ne_zero _ (abs_ne_zero.2 ha)
    field_simp
    conv_lhs => rw [← sign_mul_abs (g 0 0)]
    rw [mul_pow]
    ring
  have := congrArg (fun r : ℝ => (r : ℂ)) hr
  push_cast at this ⊢
  simpa using this

theorem J_center (k : I → ℕ) (hc : D.Compat k) (c : GL (Fin 2) F) (hcc : c ∈ Subgroup.center (GL (Fin 2) F)) (w : X I) :
    D.J k c w = D.χ ⟨D.j c, D.cenH c hcc⟩ := by
  rw [hc c hcc]
  obtain ⟨h1, h2, h3⟩ := center_entries hcc
  unfold Dat.J
  refine Finset.prod_congr rfl fun v _ => ?_
  exact automorphy_factor_scalar_matrix (k v) (D.r v c) (by change D.σ v (c 1 0) = 0; rw [h2, map_zero])
    (by change D.σ v (c 0 1) = 0; rw [h1, map_zero]) (by change D.σ v (c 0 0) = D.σ v (c 1 1); rw [h3]) (w v)

theorem act_center (c : GL (Fin 2) F) (hcc : c ∈ Subgroup.center (GL (Fin 2) F)) (w : X I) : D.act c w = w := by
  obtain ⟨h1, h2, h3⟩ := center_entries hcc
  funext v
  exact center_smul (D.r v c) (by change D.σ v (c 0 1) = 0; rw [h1, map_zero]) (by change D.σ v (c 1 0) = 0; rw [h2, map_zero])
    (by change D.σ v (c 0 0) = D.σ v (c 1 1); rw [h3]) (w v)

theorem act_mul (g h : GL (Fin 2) F) (w : X I) : D.act (g * h) w = D.act g (D.act h w) := by
  funext v
  change D.r v (g * h) • w v = D.r v g • (D.r v h • w v)
  rw [map_mul, mul_smul]

theorem J_mul (hB : B1b) (k : I → ℕ) (g h : GL (Fin 2) F) (w : X I) : D.J k (g * h) w = D.J k g (D.act h w) * D.J k h w := by
  unfold Dat.J
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_mul]
  exact hB.1 _ _ _ _

theorem tm_center (hB : B1b) (k : I → ℕ) (hc : D.Compat k) (ω : D.Om) (w : X I) (p : X I × Gf) (g c : GL (Fin 2) F)
    (hcc : c ∈ Subgroup.center (GL (Fin 2) F)) : tm D k ω w p (g * c) = tm D k ω w p g := by
  unfold tm
  set h : D.H := ⟨D.j c, D.cenH c hcc⟩
  have hz : ∀ a : Gf, a * (D.j c)⁻¹ = (D.j c)⁻¹ * a := fun a => Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ (D.cenC c hcc)) a
  have e : (D.rep ω)⁻¹ * (D.j (g * c))⁻¹ * p.2 = ((h⁻¹ : D.H) : Gf) * ((D.rep ω)⁻¹ * (D.j g)⁻¹ * p.2) := by
    rw [map_mul, _root_.mul_inv_rev, ← mul_assoc, hz]
    simp [h, mul_assoc]
  rw [e, ee_mul_left, J_mul D hB, act_center D c hcc, act_mul, act_center D c hcc, J_center D k hc c hcc, map_inv]
  have hu : (((D.χ h)⁻¹ : ℂˣ) : ℂ) * (D.χ h : ℂ) = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  linear_combination (D.ee ((D.rep ω)⁻¹ * (D.j g)⁻¹ * p.2) * (qq k p.1 (D.act g w) * D.J k g w)) * hu

theorem tm_mk (hB : B1b) (k : I → ℕ) (hc : D.Compat k) (ω : D.Om) (w : X I) (p : X I × Gf) (g g' : GL (Fin 2) F)
    (h : (g : PG F) = g') : tm D k ω w p g = tm D k ω w p g' := by
  have h2 := QuotientGroup.eq.1 h
  have : g' = g * (g⁻¹ * g') := by group
  rw [this, tm_center D hB k hc ω w p g _ h2]

theorem qJ_aut (hB : B1b) (k : I → ℕ) (γ g : GL (Fin 2) F) (z w : X I) :
    qq k (D.act γ z) (D.act (γ * g) w) * D.J k (γ * g) w = D.J k γ z * (qq k z (D.act g w) * D.J k g w) := by
  unfold qq Dat.J
  simp only [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  change q1 (k v) (D.r v γ • z v) (D.r v (γ * g) • w v) * j1 (k v) (D.r v (γ * g)) (w v) =
    j1 (k v) (D.r v γ) (z v) * (q1 (k v) (z v) (D.r v g • w v) * j1 (k v) (D.r v g) (w v))
  rw [map_mul, mul_smul, hB.1, ← mul_assoc, hB.2.2.1, mul_assoc]

theorem tm_aut (hB : B1b) (k : I → ℕ) (ω : D.Om) (w : X I) (γ g : GL (Fin 2) F) (z : X I) (x : Gf) :
    tm D k ω w (D.act γ z, D.j γ * x) (γ * g) = D.J k γ z * tm D k ω w (z, x) g := by
  unfold tm
  rw [show (D.rep ω)⁻¹ * (D.j (γ * g))⁻¹ * (D.j γ * x) = (D.rep ω)⁻¹ * (D.j g)⁻¹ * x by rw [map_mul]; group]
  rw [qJ_aut D hB]
  ring

theorem tm_lev (k : I → ℕ) (ω : D.Om) (w : X I) (g : GL (Fin 2) F) (z : X I) (x : Gf) (h : D.H) :
    tm D k ω w (z, x * h) g = D.χ h * tm D k ω w (z, x) g := by
  unfold tm
  rw [show (D.rep ω)⁻¹ * (D.j g)⁻¹ * (x * h) = (D.rep ω)⁻¹ * (D.j g)⁻¹ * x * h by group, ee_mul_right]
  ring

def cst (k : I → ℕ) : ℝ := ∏ v, ((k v : ℝ) - 1) / (4 * Real.pi)

theorem cst_nonneg (k : I → ℕ) (hk : ∀ v, 1 ≤ k v) : 0 ≤ cst k := by
  refine Finset.prod_nonneg fun v _ => div_nonneg ?_ (by positivity)
  have : (1 : ℝ) ≤ k v := by exact_mod_cast hk v
  linarith

theorem nrm_pos (k : I → ℕ) (z : X I) : 0 < nrm k z :=
  Finset.prod_pos fun v _ => Real.rpow_pos_of_pos (abs_pos.2 (z v).2) _

theorem nrm_cont (k : I → ℕ) : Continuous (nrm k : X I → ℝ) := by
  unfold nrm
  refine continuous_finsetProd _ fun v _ => ?_
  exact (continuous_abs.comp (Complex.continuous_im.comp (continuous_subtype_val.comp (continuous_apply v)))).rpow_const
    fun _ => Or.inr (by positivity)

theorem Kap_nonneg (hC : B1c) (k : I → ℕ) (z w : X I) : 0 ≤ Kap k z w :=
  Finset.prod_nonneg fun v _ => Real.rpow_nonneg (hC.1 _ _).1 _

theorem Kap_symm (hC : B1c) (k : I → ℕ) (z w : X I) : Kap k z w = Kap k w z := by
  unfold Kap
  exact Finset.prod_congr rfl fun v _ => by rw [(hC.1 (z v) (w v)).2.2]

theorem norm_qJ (hB : B1b) (k : I → ℕ) (hk : ∀ v, 1 ≤ k v) (g : GL (Fin 2) F) (z w : X I) :
    ‖qq k z (D.act g w) * D.J k g w‖ * nrm k z = cst k * Kap k z (D.act g w) * nrm k w := by
  unfold qq Dat.J nrm Kap cst
  rw [norm_mul, norm_prod, norm_prod]
  simp only [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  have h6 := hB.2.2.2.2.2.1 (k v) (z v) (D.act g w v) (hk v)
  have h5 := hB.2.2.2.2.1 (k v) (D.r v g) (w v)
  calc ‖q1 (k v) (z v) (D.act g w v)‖ * ‖j1 (k v) (D.r v g) (w v)‖ * |(z v).1.im| ^ ((k v : ℝ) / 2)
        = (‖q1 (k v) (z v) (D.act g w v)‖ * |(z v).1.im| ^ ((k v : ℝ) / 2)) * ‖j1 (k v) (D.r v g) (w v)‖ := by ring
    _ = ((k v : ℝ) - 1) / (4 * Real.pi) * kap (z v) (D.act g w v) ^ ((k v : ℝ) / 2) *
          (‖j1 (k v) (D.r v g) (w v)‖ * |(D.act g w v).1.im| ^ ((k v : ℝ) / 2)) := by rw [h6]; ring
    _ = _ := by congr 1

theorem kap_sum (hD : D.Ax) (hC : B1c) (hS : KapSum) (k : I → ℕ) (hk : ∀ v, 4 ≤ k v) (y : D.Y) :
    ∃ C : ℝ, ∀ (ω' : D.Om) (z : X I),
      Summable ({δ : PG F | δ • y.1 = ω'}.indicator fun δ => Kap k z (D.act δ.out y.2)) ∧
      ∑' δ, {δ : PG F | δ • y.1 = ω'}.indicator (fun δ => Kap k z (D.act δ.out y.2)) δ ≤ C := by
  obtain ⟨c₀, hc₀, hm⟩ := hD.mink
  obtain ⟨s, hs, hsy⟩ := hm y.2 (D.rep y.1)
  obtain ⟨C, hC'⟩ := hS F I Gf D hD k hk c₀ hc₀
  refine ⟨max (C * (1 + D.HtY s y)) 0, fun ω' z => ?_⟩
  have hb := hC' y s hs hsy ω' z
  simp only [smulX_out] at hb
  set f : PG F → ℝ := fun δ => Kap k z (D.act δ.out y.2) with hfdef
  have hf : ∀ δ, 0 ≤ f δ := fun δ => Kap_nonneg hC k _ _
  have hne : ∑' γ : {γ : PG F // γ • y.1 = ω'}, ENNReal.ofReal (f γ.1) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  have hsum : Summable fun γ : {γ : PG F // γ • y.1 = ω'} => f γ.1 := by
    have := ENNReal.summable_toReal hne
    simpa [ENNReal.toReal_ofReal (hf _)] using this
  have hsum' : Summable ({δ : PG F | δ • y.1 = ω'}.indicator f) :=
    (summable_subtype_iff_indicator (s := {δ : PG F | δ • y.1 = ω'})).mp hsum
  refine ⟨hsum', ?_⟩
  rw [← tsum_subtype]
  have h2 := ENNReal.ofReal_tsum_of_nonneg (fun γ : {γ : PG F // γ • y.1 = ω'} => hf γ.1) hsum
  have h3 : ENNReal.ofReal (∑' γ : {γ : PG F // γ • y.1 = ω'}, f γ.1) ≤ ENNReal.ofReal (max (C * (1 + D.HtY s y)) 0) := by
    rw [h2]
    exact hb.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  exact (ENNReal.ofReal_le_ofReal_iff (le_max_right _ _)).1 h3

theorem norm_tm_le (hD : D.Ax) (hB : B1b) (k : I → ℕ) (hk : ∀ v, 1 ≤ k v) (y : D.Y) (γ : PG F) (z : X I) (x : Gf) :
    ‖tm D k y.1 y.2 (z, x) γ.out‖ ≤ {δ : PG F | δ • y.1 = ((x : Gf) : Gf ⧸ D.H)}.indicator (fun δ => Kap k z (D.act δ.out y.2)) γ *
      (cst k * nrm k y.2 / nrm k z) := by
  by_cases hγ : γ • y.1 = ((x : Gf) : Gf ⧸ D.H)
  · have hγm : γ ∈ {δ : PG F | δ • y.1 = ((x : Gf) : Gf ⧸ D.H)} := hγ
    rw [Set.indicator_of_mem hγm]
    have hq := norm_qJ D hB k hk γ.out z y.2
    have hn := nrm_pos k z
    unfold tm
    rw [norm_mul]
    calc ‖D.ee ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * x)‖ * ‖qq k z (D.act γ.out y.2) * D.J k γ.out y.2‖
          ≤ 1 * ‖qq k z (D.act γ.out y.2) * D.J k γ.out y.2‖ :=
          mul_le_mul_of_nonneg_right (norm_ee_le D hD _) (norm_nonneg _)
      _ = _ := by rw [one_mul, eq_div_of_mul_eq hn.ne' hq]; ring
  · rw [tm_supp D k y.1 y.2 γ z x hγ]
    simp [Set.indicator_apply, hγ]

theorem bdd (hD : D.Ax) (hB : B1b) (hC : B1c) (hS : KapSum) (k : I → ℕ) (hk : ∀ v, 4 ≤ k v) (y : D.Y) :
    ∃ C, ∀ z x, ‖D.Kern k y (z, x)‖ * nrm k z ≤ C := by
  have hk1 : ∀ v, 1 ≤ k v := fun v => le_trans (by norm_num) (hk v)
  obtain ⟨C, hC'⟩ := kap_sum D hD hC hS k hk y
  refine ⟨C * (cst k * nrm k y.2), fun z x => ?_⟩
  obtain ⟨hs, hle⟩ := hC' ((x : Gf) : Gf ⧸ D.H) z
  have hn := nrm_pos k z
  have h1 : ‖D.Kern k y (z, x)‖ ≤ (∑' δ, {δ : PG F | δ • y.1 = ((x : Gf) : Gf ⧸ D.H)}.indicator
      (fun δ => Kap k z (D.act δ.out y.2)) δ) * (cst k * nrm k y.2 / nrm k z) := by
    rw [kern_eq]
    exact tsum_of_norm_bounded (hs.hasSum.mul_right _) (fun γ => norm_tm_le D hD hB k hk1 y γ z x)
  have hc : 0 ≤ cst k * nrm k y.2 := mul_nonneg (cst_nonneg k hk1) (nrm_pos k _).le
  calc ‖D.Kern k y (z, x)‖ * nrm k z ≤ (∑' δ, {δ : PG F | δ • y.1 = ((x : Gf) : Gf ⧸ D.H)}.indicator
      (fun δ => Kap k z (D.act δ.out y.2)) δ) * (cst k * nrm k y.2 / nrm k z) * nrm k z := mul_le_mul_of_nonneg_right h1 hn.le
    _ = (∑' δ, {δ : PG F | δ • y.1 = ((x : Gf) : Gf ⧸ D.H)}.indicator
      (fun δ => Kap k z (D.act δ.out y.2)) δ) * (cst k * nrm k y.2) := by field_simp
    _ ≤ C * (cst k * nrm k y.2) := mul_le_mul_of_nonneg_right hle hc

theorem near_bd (hD : D.Ax) (hB : B1b) (hC : B1c) (hI : KapInt) (k : I → ℕ) (hk : ∀ v, 4 ≤ k v) (y : D.Y) (x : Gf) (z₀ : X I) :
    ∃ U : Set (X I), IsOpen U ∧ z₀ ∈ U ∧ ∃ M : ℝ, ∀ z ∈ U, ∀ γ : PG F,
      ‖tm D k y.1 y.2 (z, x) γ.out‖ ≤ {δ : PG F | δ • y.1 = ((x : Gf) : Gf ⧸ D.H)}.indicator (fun δ => Kap k z₀ (D.act δ.out y.2)) γ * M := by
  have hk1 : ∀ v, 1 ≤ k v := fun v => le_trans (by norm_num) (hk v)
  obtain ⟨C', A, hA⟩ := hI I k hk
  have hn0 := nrm_pos k z₀
  refine ⟨(⋂ v, {z : X I | 1 / 2 < kap (z v) (z₀ v)}) ∩ {z | nrm k z₀ / 2 < nrm k z}, ?_, ?_,
    A * (cst k * nrm k y.2 / (nrm k z₀ / 2)), ?_⟩
  · refine (isOpen_iInter_of_finite fun v => isOpen_lt continuous_const ?_).inter (isOpen_lt continuous_const (nrm_cont k))
    exact hC.2.2.2.2.1.comp (((continuous_apply v).prodMk continuous_const : Continuous fun z : X I => (z v, z₀ v)))
  · refine ⟨Set.mem_iInter.2 fun v => ?_, ?_⟩
    · change 1 / 2 < kap (z₀ v) (z₀ v)
      rw [hC.2.1]
      norm_num
    · change nrm k z₀ / 2 < nrm k z₀
      linarith
  · rintro z ⟨hz1, hz2⟩ γ
    have hz1' : ∀ v, 1 / 2 < kap (z v) (z₀ v) := fun v => Set.mem_iInter.1 hz1 v
    have hz2' : nrm k z₀ / 2 < nrm k z := hz2
    refine (norm_tm_le D hD hB k hk1 y γ z x).trans ?_
    by_cases hγ : γ • y.1 = ((x : Gf) : Gf ⧸ D.H)
    · have hγm : γ ∈ {δ : PG F | δ • y.1 = ((x : Gf) : Gf ⧸ D.H)} := hγ
      rw [Set.indicator_of_mem hγm, Set.indicator_of_mem hγm]
      have hK : Kap k z (D.act γ.out y.2) ≤ A * Kap k z₀ (D.act γ.out y.2) := by
        rw [Kap_symm hC k z, Kap_symm hC k z₀]
        exact ((hA (D.act γ.out y.2)).2.2.2 z z₀ fun v => (hz1' v).le).1
      have hc : 0 ≤ cst k * nrm k y.2 := mul_nonneg (cst_nonneg k hk1) (nrm_pos k _).le
      have hd : cst k * nrm k y.2 / nrm k z ≤ cst k * nrm k y.2 / (nrm k z₀ / 2) :=
        div_le_div_of_nonneg_left hc (by linarith) hz2'.le
      calc Kap k z (D.act γ.out y.2) * (cst k * nrm k y.2 / nrm k z)
            ≤ (A * Kap k z₀ (D.act γ.out y.2)) * (cst k * nrm k y.2 / (nrm k z₀ / 2)) :=
            mul_le_mul hK hd (div_nonneg hc (nrm_pos k z).le) (mul_nonneg A.2 (Kap_nonneg hC k _ _))
        _ = _ := by ring
    · simp [Set.indicator_apply, hγ]

theorem tm_cont (hB : B1b) (k : I → ℕ) (ω : D.Om) (w : X I) (x : Gf) (g : GL (Fin 2) F) :
    Continuous fun z : X I => tm D k ω w (z, x) g := by
  have h1 : Continuous fun z : X I => qq k z (D.act g w) := by
    unfold qq
    exact continuous_finsetProd _ fun v _ =>
      (hB.2.2.2.2.2.2.2.1 (k v)).comp (((continuous_apply v).prodMk continuous_const : Continuous fun z : X I => (z v, D.act g w v)))
  show Continuous fun z : X I => D.ee ((D.rep ω)⁻¹ * (D.j g)⁻¹ * x) * (qq k z (D.act g w) * D.J k g w)
  exact continuous_const.mul (h1.mul continuous_const)

theorem cont (hD : D.Ax) (hB : B1b) (hC : B1c) (hS : KapSum) (hI : KapInt) (k : I → ℕ) (hk : ∀ v, 4 ≤ k v) (y : D.Y) (x : Gf) :
    Continuous fun z => D.Kern k y (z, x) := by
  obtain ⟨C, hC'⟩ := kap_sum D hD hC hS k hk y
  refine continuous_iff_continuousAt.2 fun z₀ => ?_
  obtain ⟨U, hU, hz₀, M, hM⟩ := near_bd D hD hB hC hI k hk y x z₀
  have h := continuousOn_tsum (fun γ : PG F => (tm_cont D hB k y.1 y.2 x γ.out).continuousOn)
    ((hC' ((x : Gf) : Gf ⧸ D.H) z₀).1.mul_right M) (fun γ z hz => hM z hz γ)
  exact h.continuousAt (hU.mem_nhds hz₀)

theorem qq_update (k : I → ℕ) (z w : X I) (v : I) (t : P) :
    qq k (Function.update z v t) w = (∏ u ∈ Finset.univ.erase v, q1 (k u) (z u) (w u)) * q1 (k v) t (w v) := by
  unfold qq
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ v), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun u hu => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hu)]

theorem extendHalfPlane_coe_point (f : P → ℂ) (s : P) : ext1 f s.1 = f s := by
  unfold ext1
  rw [dif_pos s.2]
  rfl

theorem hol_tsum {ι : Type} (f : ι → P → ℂ) (hf : ∀ i, Hol1 (f i))
    (hloc : ∀ t₀ : P, ∃ U : Set P, IsOpen U ∧ t₀ ∈ U ∧ ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ t ∈ U, ‖f i t‖ ≤ u i) :
    Hol1 fun t => ∑' i, f i t := by
  intro t₀ ht₀
  have ht₀' : t₀.im ≠ 0 := ht₀
  obtain ⟨U, hU, hmem, u, hu, hb⟩ := hloc ⟨t₀, ht₀'⟩
  have hPo : IsOpen {t : ℂ | t.im ≠ 0} := isOpen_ne_fun Complex.continuous_im continuous_const
  set V : Set ℂ := (fun s : P => s.1) '' U with hVdef
  have hV : IsOpen V := hPo.isOpenMap_subtype_val U hU
  have hVsub : V ⊆ {t : ℂ | t.im ≠ 0} := by
    rintro _ ⟨s, -, rfl⟩
    exact s.2
  have hd : DifferentiableOn ℂ (fun t => ∑' i, ext1 (f i) t) V :=
    Complex.differentiableOn_tsum_of_summable_norm hu (fun i => (hf i).mono hVsub) hV (by
      rintro i _ ⟨s, hs, rfl⟩
      rw [extendHalfPlane_coe_point]
      exact hb i s hs)
  have hin : t₀ ∈ V := ⟨⟨t₀, ht₀'⟩, hmem, rfl⟩
  have heq : ext1 (fun t => ∑' i, f i t) =ᶠ[𝓝 t₀] fun t => ∑' i, ext1 (f i) t := by
    filter_upwards [hV.mem_nhds hin] with t ht
    obtain ⟨s, -, rfl⟩ := ht
    simp only [extendHalfPlane_coe_point]
  exact ((hd.differentiableAt (hV.mem_nhds hin)).congr_of_eventuallyEq heq).differentiableWithinAt

theorem tm_hol (hB : B1b) (k : I → ℕ) (ω : D.Om) (w : X I) (x : Gf) (g : GL (Fin 2) F) (z : X I) (v : I) :
    Hol1 fun t => tm D k ω w (Function.update z v t, x) g := by
  have e1 : ∀ s : P, tm D k ω w (Function.update z v s, x) g =
      (D.ee ((D.rep ω)⁻¹ * (D.j g)⁻¹ * x) * (∏ u ∈ Finset.univ.erase v, q1 (k u) (z u) (D.act g w u)) * D.J k g w) *
        q1 (k v) s (D.act g w v) := by
    intro s
    unfold tm
    dsimp only
    rw [qq_update]
    ring
  have e : ext1 (fun t => tm D k ω w (Function.update z v t, x) g) = fun t =>
      (D.ee ((D.rep ω)⁻¹ * (D.j g)⁻¹ * x) * (∏ u ∈ Finset.univ.erase v, q1 (k u) (z u) (D.act g w u)) * D.J k g w) *
        ext1 (fun s => q1 (k v) s (D.act g w v)) t := by
    funext t
    unfold ext1
    split_ifs with ht
    · exact e1 _
    · rw [mul_zero]
  unfold Hol1
  rw [e]
  exact (hB.2.2.2.2.2.2.2.2 (k v) (D.act g w v)).const_mul _

theorem hol (hD : D.Ax) (hB : B1b) (hC : B1c) (hS : KapSum) (hI : KapInt) (k : I → ℕ) (hk : ∀ v, 4 ≤ k v) (y : D.Y) (x : Gf)
    (z : X I) (v : I) : Hol1 fun t => D.Kern k y (Function.update z v t, x) := by
  obtain ⟨C, hC'⟩ := kap_sum D hD hC hS k hk y
  refine hol_tsum (fun (γ : PG F) t => tm D k y.1 y.2 (Function.update z v t, x) γ.out)
    (fun γ => tm_hol D hB k y.1 y.2 x γ.out z v) fun t₀ => ?_
  obtain ⟨U, hU, hz₀, M, hM⟩ := near_bd D hD hB hC hI k hk y x (Function.update z v t₀)
  exact ⟨(fun t => Function.update z v t) ⁻¹' U, hU.preimage (continuous_const.update v continuous_id), hz₀, _,
    (hC' ((x : Gf) : Gf ⧸ D.H) _).1.mul_right M, fun γ t ht => hM _ ht γ⟩

end UpperTheory.Esk.KernelLevelTransform

namespace UpperTheory.Esk.KernelLevelTransform

open UpperTheory.Esk

theorem main (hB : B1b) (hC : B1c) (hS : KapSum) (hI : KapInt) : E4 := by
  intro F I Gf _ _ _ D hD k hk hc y
  refine ⟨fun x => ⟨cont D hD hB hC hS hI k hk y x, fun z v => hol D hD hB hC hS hI k hk y x z v⟩,
    fun γ z x => ?_, fun z x h => ?_, bdd D hD hB hC hS k hk y⟩
  · rw [kern_eq, kern_eq, ← Equiv.tsum_eq (Equiv.mulLeft (γ : PG F)), ← tsum_mul_left]
    refine tsum_congr fun δ => ?_
    refine (tm_mk D hB k hc y.1 y.2 _ _ (γ * δ.out) ?_).trans (tm_aut D hB k y.1 y.2 γ δ.out z x)
    rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq']
    rfl
  · rw [kern_eq, kern_eq, ← tsum_mul_left]
    exact tsum_congr fun δ => tm_lev D k y.1 y.2 δ.out z x h

end UpperTheory.Esk.KernelLevelTransform

theorem UpperTheory.Esk.kernel_level_transform_proof : UpperTheory.Esk.B1a → UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.E0d → UpperTheory.Esk.KapSum → UpperTheory.Esk.KapInt → UpperTheory.Esk.E4 :=
  fun _ hB hC _ hS hI => UpperTheory.Esk.KernelLevelTransform.main hB hC hS hI
