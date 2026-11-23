import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.KernelInverseSymmetry

open UpperTheory.Esk

variable {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf)

def cK (k : I → ℕ) : ℝ := ∏ v, ((k v : ℝ) - 1) / (4 * Real.pi)

def T (k : I → ℕ) (p : X I × Gf) (γ : PG F) (y : D.Y) : ℂ :=
  D.ee ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * p.2) * (qq k p.1 (D.act γ.out y.2) * D.J k γ.out y.2)

theorem cK_nonneg (k : I → ℕ) (hk : ∀ v, 4 ≤ k v) : 0 ≤ cK k :=
  Finset.prod_nonneg fun v _ => div_nonneg (by
    have h : (4 : ℝ) ≤ k v := by exact_mod_cast hk v
    linarith) (by positivity)

theorem nrm_pos (k : I → ℕ) (z : X I) : 0 < nrm k z :=
  Finset.prod_pos fun v _ => Real.rpow_pos_of_pos (abs_pos.2 (z v).2) _

theorem act_out (γ : PG F) (z : D.Xs) : D.act γ.out z = γ • z := by
  rw [← D.mk_smulX]
  congr 1
  exact Quotient.out_eq γ

theorem norm_qj (hB : B1b) (k : ℕ) (hk : 1 ≤ k) (g : GL (Fin 2) ℝ) (z w : P) :
    ‖q1 k z (g • w)‖ * ‖j1 k g w‖ * |z.1.im| ^ ((k : ℝ) / 2) =
      ((k : ℝ) - 1) / (4 * Real.pi) * kap z (g • w) ^ ((k : ℝ) / 2) * |w.1.im| ^ ((k : ℝ) / 2) := by
  obtain ⟨-, -, -, -, hj, hq, -⟩ := hB
  have e1 := hq k z (g • w) hk
  have e2 := hj k g w
  calc _ = (‖q1 k z (g • w)‖ * |z.1.im| ^ ((k : ℝ) / 2)) * ‖j1 k g w‖ := by ring
    _ = _ := by rw [e1, ← e2]; ring

theorem norm_term (hB : B1b) (k : I → ℕ) (hk : ∀ v, 1 ≤ k v) (g : GL (Fin 2) F) (z w : X I) :
    ‖qq k z (D.act g w) * D.J k g w‖ * nrm k z = cK k * Kap k z (D.act g w) * nrm k w := by
  simp only [qq, Dat.J, Kap, nrm, cK, norm_mul, norm_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  exact norm_qj hB (k v) (hk v) (D.r v g) (z v) (w v)

theorem Kap_smul (hB : B1b) (k : I → ℕ) (δ : PG F) (z w : D.Xs) :
    Kap k (δ • z : D.Xs) (δ • w : D.Xs) = Kap k z w := by
  obtain ⟨-, -, -, hkap, -⟩ := hB
  rw [← act_out, ← act_out]
  unfold Kap
  refine Finset.prod_congr rfl fun v _ => ?_
  show kap (D.r v δ.out • z v) (D.r v δ.out • w v) ^ _ = _
  rw [hkap]

theorem Kap_symm (hBc : B1c) (k : I → ℕ) (z w : X I) : Kap k z w = Kap k w z := by
  obtain ⟨hsym, -⟩ := hBc
  unfold Kap
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [(hsym _ _).2.2]

theorem Kap_swap (hB : B1b) (hBc : B1c) (k : I → ℕ) (γ : PG F) (z w : D.Xs) :
    Kap k z (γ • w : D.Xs) = Kap k w (γ⁻¹ • z : D.Xs) := by
  rw [← Kap_smul D hB k γ⁻¹ z (γ • w), inv_smul_smul]
  exact Kap_symm hBc k _ _

theorem ee_mem (x : Gf) (h : D.ee x ≠ 0) : x ∈ D.H := by
  unfold Dat.ee at h
  split_ifs at h with hx
  · exact hx
  · exact absurd rfl h

theorem norm_ee (hAx : D.Ax) (x : Gf) : ‖D.ee x‖ ≤ 1 := by
  unfold Dat.ee
  split_ifs with hx
  · rw [hAx.χn]
  · simp

theorem supp (γ : PG F) (ω : D.Om) (x : Gf) (h : D.ee ((D.rep ω)⁻¹ * (D.j γ.out)⁻¹ * x) ≠ 0) :
    γ • ω = (show D.Om from (x : Gf ⧸ D.H)) := by
  have hm := ee_mem D _ h
  rw [mul_assoc] at hm
  have e : ((D.rep ω : Gf) : Gf ⧸ D.H) = (((D.j γ.out)⁻¹ * x : Gf) : Gf ⧸ D.H) := QuotientGroup.eq.2 hm
  have hω : ((D.rep ω : Gf) : Gf ⧸ D.H) = ω := Quotient.out_eq ω
  have hγ : ((γ.out : GL (Fin 2) F) : PG F) = γ := Quotient.out_eq γ
  have key : ((γ.out : GL (Fin 2) F) : PG F) • (show D.Om from (((D.j γ.out)⁻¹ * x : Gf) : Gf ⧸ D.H)) =
      (show D.Om from (x : Gf ⧸ D.H)) := by
    rw [D.mk_smulO, mul_inv_cancel_left]
  rw [← hω, e]
  rw [hγ] at key
  exact key

def xH (_D : Dat F I Gf) (p : X I × Gf) : _D.Om := (p.2 : Gf ⧸ _D.H)

def zX (_D : Dat F I Gf) (p : X I × Gf) : _D.Xs := p.1

def invEquiv (ω x : D.Om) : {γ : PG F // γ • ω = x} ≃ {δ : PG F // δ • x = ω} where
  toFun γ := ⟨γ.1⁻¹, by rw [inv_smul_eq_iff, γ.2]⟩
  invFun δ := ⟨δ.1⁻¹, by rw [inv_smul_eq_iff, δ.2]⟩
  left_inv γ := Subtype.ext (inv_inv _)
  right_inv δ := Subtype.ext (inv_inv _)

theorem T_le (hB : B1b) (hBc : B1c) (hAx : D.Ax) (k : I → ℕ) (hk : ∀ v, 4 ≤ k v) (p : X I × Gf) (γ : PG F) (y : D.Y) :
    ‖T D k p γ y‖ₑ ≤ {γ : PG F | γ • y.1 = (xH D p)}.indicator
      (fun γ => ENNReal.ofReal (cK k / nrm k p.1 * nrm k y.2) *
        ENNReal.ofReal (Kap k y.2 (γ⁻¹ • (zX D p) : D.Xs))) γ := by
  by_cases hγ : γ • y.1 = (xH D p)
  · rw [Set.indicator_of_mem (show γ ∈ {γ : PG F | γ • y.1 = (xH D p)} from hγ)]
    rw [← ENNReal.ofReal_mul (mul_nonneg (div_nonneg (cK_nonneg k hk) (nrm_pos k p.1).le) (nrm_pos k y.2).le),
      ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    have hn := norm_term D hB k (fun v => le_trans (by norm_num) (hk v)) γ.out p.1 y.2
    have hK : Kap k p.1 (D.act γ.out y.2) = Kap k y.2 (γ⁻¹ • (zX D p) : D.Xs) := by
      rw [act_out]
      exact Kap_swap D hB hBc k γ p.1 y.2
    rw [hK] at hn
    have hN := eq_div_of_mul_eq (nrm_pos k p.1).ne' hn
    have he := norm_ee D hAx ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * p.2)
    unfold T
    rw [norm_mul]
    calc _ ≤ 1 * ‖qq k p.1 (D.act γ.out y.2) * D.J k γ.out y.2‖ := mul_le_mul_of_nonneg_right he (norm_nonneg _)
      _ = _ := by rw [hN]; ring
  · rw [Set.indicator_of_notMem (show γ ∉ {γ : PG F | γ • y.1 = (xH D p)} from hγ)]
    have h0 : D.ee ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * p.2) = 0 := by
      by_contra hne
      exact hγ (supp D γ y.1 p.2 hne)
    simp [T, h0]

theorem tsum_le (hB : B1b) (hBc : B1c) (hAx : D.Ax) (k : I → ℕ) (hk : ∀ v, 4 ≤ k v) (p : X I × Gf) (Bnd : ℝ)
    (hS : ∀ (ω : D.Om) (w : X I), ∑' δ : {δ : PG F // δ • (xH D p) = ω},
      ENNReal.ofReal (Kap k w (δ.1 • (zX D p) : D.Xs)) ≤ ENNReal.ofReal Bnd) (y : D.Y) :
    ∑' γ, ‖T D k p γ y‖ₑ ≤ ENNReal.ofReal (cK k / nrm k p.1 * nrm k y.2) * ENNReal.ofReal Bnd := by
  have h1 := ENNReal.tsum_le_tsum fun γ => T_le D hB hBc hAx k hk p γ y
  rw [← tsum_subtype] at h1
  beta_reduce at h1
  rw [ENNReal.tsum_mul_left] at h1
  refine h1.trans (mul_le_mul' le_rfl (Eq.trans_le ?_ (hS y.1 y.2)))
  exact Equiv.tsum_eq (invEquiv D y.1 (xH D p))
    (fun δ => ENNReal.ofReal (Kap k y.2 (δ.1 • (zX D p) : D.Xs)))

theorem main (hB1a : B1a) (hB : B1b) (hBc : B1c) (hE0a : E0a) (hKS : KapSum) (hAx : D.Ax)
    (k : I → ℕ) (hk : ∀ v, 4 ≤ k v) (p : X I × Gf) :
    (∀ y : D.Y, Summable fun γ : PG F => ‖D.ee ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * p.2) *
      (qq k p.1 (D.act γ.out y.2) * D.J k γ.out y.2)‖) ∧
    Measurable (fun y => D.Kern k y p) ∧ ∃ C, ∀ y, ‖D.Kern k y p‖ ≤ C * nrm k y.2 := by
  obtain ⟨hcount, -, -, -, -, -, hborel, -⟩ := hE0a F I Gf D hAx
  obtain ⟨c₀, hc₀, hmink⟩ := hAx.mink
  obtain ⟨C, hCb⟩ := hKS F I Gf D hAx k hk c₀ hc₀
  obtain ⟨s, hs, hsle⟩ := hmink p.1 (D.rep (xH D p))
  obtain ⟨Bnd, hBnd, hS⟩ : ∃ Bnd : ℝ, 0 ≤ Bnd ∧ ∀ (ω : D.Om) (w : X I),
      ∑' δ : {δ : PG F // δ • (xH D p) = ω},
        ENNReal.ofReal (Kap k w (δ.1 • (zX D p) : D.Xs)) ≤ ENNReal.ofReal Bnd :=
    ⟨max (C * (1 + D.HtY s ((xH D p), p.1))) 0, le_max_right _ _, fun ω w =>
      (hCb ((xH D p), p.1) s hs hsle ω w).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩
  have hT := fun y => tsum_le D hB hBc hAx k hk p Bnd hS y
  have hfin : ∀ y : D.Y, ∑' γ, ‖T D k p γ y‖ₑ ≠ ⊤ := fun y =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) (hT y)
  have hsumm : ∀ y : D.Y, Summable fun γ => ‖T D k p γ y‖ := fun y => by
    simpa only [toReal_enorm] using ENNReal.summable_toReal (hfin y)
  have hc0 : 0 ≤ cK k / nrm k p.1 := div_nonneg (cK_nonneg k hk) (nrm_pos k p.1).le
  have hbound : ∀ y : D.Y, ∑' γ, ‖T D k p γ y‖ ≤ cK k / nrm k p.1 * Bnd * nrm k y.2 := fun y => by
    have h1 : ∑' γ, ‖T D k p γ y‖ = (∑' γ, ‖T D k p γ y‖ₑ).toReal := by
      rw [ENNReal.tsum_toReal_eq (fun γ => enorm_ne_top)]
      simp only [toReal_enorm]
    rw [h1]
    refine ENNReal.toReal_le_of_le_ofReal (mul_nonneg (mul_nonneg hc0 hBnd) (nrm_pos k y.2).le) ?_
    calc _ ≤ _ := hT y
      _ = ENNReal.ofReal (cK k / nrm k p.1 * Bnd * nrm k y.2) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hc0 (nrm_pos k y.2).le)]
        congr 1
        ring
  refine ⟨hsumm, ?_, ⟨cK k / nrm k p.1 * Bnd, fun y => (norm_tsum_le_tsum_norm (hsumm y)).trans (hbound y)⟩⟩
  haveI := hcount
  haveI := hborel
  obtain ⟨-, -, -, -, -, -, hjc, hqc, -⟩ := hB
  have hgc : ∀ g : GL (Fin 2) ℝ, Continuous fun z : P => g • z := fun g => (hB1a.2.2 g).1
  have hTm : ∀ γ : PG F, Measurable (T D k p γ) := fun γ => by
    have hG : Continuous fun w : D.Xs => qq k p.1 (D.act γ.out w) * D.J k γ.out w := by
      refine Continuous.mul ?_ ?_
      · refine continuous_finsetProd _ fun v _ => ?_
        exact (hqc (k v)).comp (continuous_const.prodMk ((hgc (D.r v γ.out)).comp (continuous_apply v)))
      · exact continuous_finsetProd _ fun v _ => (hjc (k v) (D.r v γ.out)).comp (continuous_apply v)
    exact ((Measurable.of_discrete (f := fun ω : D.Om => D.ee ((D.rep ω)⁻¹ * (D.j γ.out)⁻¹ * p.2))).comp
      measurable_fst).mul (hG.measurable.comp measurable_snd)
  have hlim : Tendsto (fun (s : Finset (PG F)) (y : D.Y) => ∑ γ ∈ s, T D k p γ y) atTop
      (𝓝 fun y => ∑' γ, T D k p γ y) :=
    tendsto_pi_nhds.2 fun y => ((hsumm y).of_norm).hasSum
  exact measurable_of_tendsto_metrizable' atTop (fun s => Finset.measurable_sum s fun γ _ => hTm γ) hlim

end UpperTheory.Esk.KernelInverseSymmetry

theorem UpperTheory.Esk.kernel_inverse_symmetry : UpperTheory.Esk.B1a → UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.E0a → UpperTheory.Esk.E0d → UpperTheory.Esk.KapSum → UpperTheory.Esk.faceMap_zero_comp_eq_one := by
  intro hB1a hB1b hB1c hE0a _ hKS F I Gf _ _ _ D hAx k hk _ p
  exact UpperTheory.Esk.KernelInverseSymmetry.main D hB1a hB1b hB1c hE0a hKS hAx k hk p
