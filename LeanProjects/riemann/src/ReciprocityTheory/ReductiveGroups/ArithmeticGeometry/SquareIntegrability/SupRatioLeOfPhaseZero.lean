import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaS
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.DimStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ContDiffOfDifferentiableFd

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex NumberField

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem HC_one {dim : (E →+* ℂ) → ℕ} (v w : Vsp dim) :
    HC (n := 1) (fun _ => v) (fun _ => w) = Hf v w := by
  simp [HC]

theorem Hf_self_re {ι : Type} [Fintype ι] (v : EuclideanSpace ℂ ι) : (Hf v v).re = ‖v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Hf, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

namespace PT

variable (X : PT E)

def toGT : GT (Idx X.dim) where
  b := X.b
  integral := X.integral
  perfect := X.perfect
  ka := fun x => (X.eps x : ℂ)
  ka_abs := fun x hx => by
    rcases X.eps_pm x hx with h | h <;> simp [h]

def col1 (s : (Fin 1 → Vsp X.dim) → ℂ) : Vsp X.dim → ℂ := fun v => s fun _ => v

theorem column_mem_sections {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) : X.col1 s ∈ X.toGT.Sec 1 := by
  obtain ⟨hd, hf⟩ := hs
  refine (show Differentiable ℂ (X.col1 s) ∧ ∀ γ ∈ lat X.toGT.b, ∀ v, X.col1 s (v + γ) =
      X.toGT.ka γ * cexp (((1 : ℕ) : ℂ) * Real.pi * Hf v γ + ((1 : ℕ) : ℂ) * Real.pi * Hf γ γ / 2) *
        X.col1 s v from ⟨?_, ?_⟩)
  · exact hd.comp (differentiable_pi.mpr fun _ => differentiable_id)
  · intro γ hγ v
    have h := hf (fun _ => γ) (fun _ => hγ) (fun _ => v)
    simp only [HC_one, Fin.prod_univ_one, pow_one] at h
    exact h

theorem pointNormSq_column (s : (Fin 1 → Vsp X.dim) → ℂ) (a : Vsp X.dim) :
    X.ptN2 1 s (fun _ => a) = X.toGT.ptN2 1 (X.col1 s) a := by
  simp only [PT.ptN2, GT.ptN2, PT.col1, HC_one, Hf_self_re]

theorem l2_one_eq_toGT_l2_col1 (s : (Fin 1 → Vsp X.dim) → ℂ) : X.l2 1 s = X.toGT.l2 1 (X.col1 s) := by
  have hfd : X.fd 1 = (MeasurableEquiv.funUnique (Fin 1) (Vsp X.dim)) ⁻¹'
      ZSpan.fundamentalDomain X.b := by
    ext v
    simp only [PT.fd, Set.mem_setOf_eq, Set.mem_preimage]
    exact ⟨fun h => h default, fun h k => by rwa [Subsingleton.elim k default]⟩
  have hf : ∀ v : Fin 1 → Vsp X.dim, X.ptN2 1 s v =
      X.toGT.ptN2 1 (X.col1 s) (MeasurableEquiv.funUnique (Fin 1) (Vsp X.dim) v) := by
    intro v
    have hv : v = fun _ => v default := funext fun k => by rw [Subsingleton.elim k default]
    rw [hv, pointNormSq_column]
    rfl
  have hmp := MeasureTheory.volume_preserving_funUnique (Fin 1) (Vsp X.dim)
  have he := (MeasurableEquiv.funUnique (Fin 1) (Vsp X.dim)).measurableEmbedding
  unfold PT.l2 GT.l2
  rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq, hfd]
  simp only [MeasureTheory.measureReal_def]
  erw [hmp.measure_preimage_emb he]
  simp_rw [hf]
  erw [hmp.setIntegral_preimage_emb he (X.toGT.ptN2 1 (X.col1 s))]
  rfl

theorem card_idx [IsCMField E] : Fintype.card (Idx X.dim) = X.gA := by
  have hinv : Function.Involutive
      (NumberField.ComplexEmbedding.conjugate : (E →+* ℂ) → (E →+* ℂ)) :=
    fun φ => RingHom.ext fun x => by simp [NumberField.ComplexEmbedding.conjugate_coe_eq]
  have hsum : ∑ τ, X.dim (NumberField.ComplexEmbedding.conjugate τ) = ∑ τ, X.dim τ :=
    Equiv.sum_comp (Function.Involutive.toPerm _ hinv) X.dim
  have h2 : 2 * ∑ τ, X.dim τ = Fintype.card (E →+* ℂ) * X.r := by
    rw [two_mul]
    nth_rewrite 2 [← hsum]
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun τ _ => X.dim_conj τ), Finset.sum_const,
      Finset.card_univ, smul_eq_mul]
  haveI : NumberField.IsTotallyComplex E := NumberField.IsCMField.to_isTotallyComplex
  rw [NumberField.Embeddings.card, NumberField.IsTotallyComplex.finrank] at h2
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  unfold PT.gA PT.f
  rw [NumberField.IsTotallyComplex.finrank, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  linarith

theorem firstMinimum_toTorus : X.toGT.la1 = X.la1 := rfl

end PT

theorem f_pos {X : PT E} {DF : ℕ} (P : Par X DF) : 1 ≤ PT.f E := by
  have h := P.hfr
  rcases Nat.eq_zero_or_pos (PT.f E) with h0 | h0
  · rw [h0, zero_mul] at h
    omega
  · exact h0

theorem firstMinimum_pos_bis [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) : 0 < X.la1 := by
  rw [← X.firstMinimum_toTorus]
  apply firstMinimum_pos
  rw [X.card_idx]
  have h := P.hfr
  unfold PT.gA
  omega

theorem threshold_le_firstMinimum [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) (h0 : P.ph = 0) :
    th (E := E) P.q P.R0 ≤ X.la1 := by
  by_contra hlt
  push_neg at hlt
  have hp : P.ph = 2 * PT.f E / (PT.rd E ^ 2 * X.la1 ^ 2) := by
    simp only [Par.ph, PT.ph, if_pos hlt]
  rw [hp] at h0
  have hla := firstMinimum_pos_bis P
  have hf : (1 : ℝ) ≤ PT.f E := by exact_mod_cast f_pos P
  have hrd : (16 : ℝ) ≤ PT.rd E := P.hrd
  have hpos : 0 < 2 * (PT.f E : ℝ) / (PT.rd E ^ 2 * X.la1 ^ 2) :=
    div_pos (by linarith) (mul_pos (pow_pos (by linarith) 2) (pow_pos hla 2))
  linarith

theorem one_le_sqrt_q_th {X : PT E} {DF : ℕ} (P : Par X DF) :
    1 ≤ Real.sqrt P.q * th (E := E) P.q P.R0 := by
  have hq : (0 : ℝ) < P.q := by exact_mod_cast P.hq
  have hf : (1 : ℝ) ≤ PT.f E := by exact_mod_cast f_pos P
  have hR : (270 : ℝ) ≤ P.R0 ^ 2 := P.hR0.1
  have hrd : (16 : ℝ) ≤ PT.rd E := P.hrd
  have hRR : 1 ≤ RR (E := E) := by
    unfold RR
    exact one_le_pow₀ (by linarith)
  have h3 : 1 ≤ RR (E := E) ^ 3 := one_le_pow₀ hRR
  unfold th
  rw [← Real.sqrt_mul hq.le]
  have hA : (P.q : ℝ) * (PT.f E * P.R0 ^ 2 * RR (E := E) ^ 3 / P.q) =
      PT.f E * P.R0 ^ 2 * RR (E := E) ^ 3 := by
    field_simp
  rw [hA, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  apply Real.sqrt_le_sqrt
  have h1 : (270 : ℝ) ≤ PT.f E * P.R0 ^ 2 := by nlinarith
  nlinarith

theorem sup_ratio_le_of_phase_zero [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) (hS : GSupStatement)
    {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) (h0 : P.ph = 0) (a : Vsp X.dim) :
    Real.sqrt (X.ptN2 1 s fun _ => a) / Real.sqrt (X.l2 1 s) ≤ Real.exp P.p1 := by
  have hN : Fintype.card (Idx X.dim) = X.gA := X.card_idx
  have hth := threshold_le_firstMinimum P h0
  have hsq := one_le_sqrt_q_th P
  have hla : 0 < X.la1 := firstMinimum_pos_bis P
  have hq : (0 : ℝ) < P.q := by exact_mod_cast P.hq
  have hsqrtq : 0 < Real.sqrt P.q := Real.sqrt_pos.mpr hq
  have hB := hS (Idx X.dim) X.toGT 1 le_rfl (X.col1 s) (X.column_mem_sections hs) a
  rw [← X.pointNormSq_column, ← X.l2_one_eq_toGT_l2_col1, X.firstMinimum_toTorus, hN] at hB
  simp only [Nat.cast_one, one_pow, one_mul, mul_one] at hB
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 1 + 6 * Real.sqrt (X.gA * P.q) := ⟨_, rfl⟩
  have hspi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hspi1 : 1 ≤ Real.sqrt Real.pi := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  have hs2 : Real.sqrt 2 ≤ 1.5 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have h1 : 1 ≤ Real.sqrt P.q * X.la1 :=
    le_trans hsq (mul_le_mul_of_nonneg_left hth hsqrtq.le)
  have hsN := Real.sqrt_nonneg (X.gA : ℝ)
  have hterm : 4 * Real.sqrt (2 * X.gA) / (Real.sqrt Real.pi * X.la1) ≤
      6 * Real.sqrt (X.gA * P.q) := by
    rw [div_le_iff₀ (mul_pos hspi hla), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_mul (Nat.cast_nonneg _)]
    have e1 : 4 * (Real.sqrt 2 * Real.sqrt X.gA) ≤ Real.sqrt X.gA * (6 * Real.sqrt Real.pi) := by
      nlinarith
    have e2 : Real.sqrt X.gA * (6 * Real.sqrt Real.pi) ≤
        Real.sqrt X.gA * (6 * Real.sqrt Real.pi) * (Real.sqrt P.q * X.la1) :=
      le_mul_of_one_le_right (by positivity) h1
    nlinarith
  have hBC : 1 + 4 * Real.sqrt (2 * X.gA) / (Real.sqrt Real.pi * X.la1) ≤ C := by
    rw [hC]; linarith
  have hB0 : 0 ≤ 1 + 4 * Real.sqrt (2 * X.gA) / (Real.sqrt Real.pi * X.la1) := by positivity
  have hCpos : 0 < C := by rw [hC]; positivity
  rcases le_or_gt (X.l2 1 s) 0 with hL | hL
  · rw [Real.sqrt_eq_zero'.mpr hL, div_zero]
    exact (Real.exp_pos _).le
  · have hpow := pow_le_pow_left₀ hB0 hBC (2 * X.gA)
    have hA : X.ptN2 1 s (fun _ => a) ≤ 2 * C ^ (2 * X.gA) * X.l2 1 s := by
      refine hB.trans ?_
      gcongr
    have hexp : Real.exp P.p1 = Real.exp 1 * C ^ X.gA := by
      unfold Par.p1
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by rw [← hC]; exact hCpos), hC]
    have he2 : Real.sqrt 2 ≤ Real.exp 1 := by
      have := Real.add_one_le_exp 1
      linarith
    rw [div_le_iff₀ (Real.sqrt_pos.mpr hL), hexp]
    have hsplit : Real.sqrt (2 * C ^ (2 * X.gA) * X.l2 1 s) =
        Real.sqrt 2 * C ^ X.gA * Real.sqrt (X.l2 1 s) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
        show C ^ (2 * X.gA) = (C ^ X.gA) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    calc Real.sqrt (X.ptN2 1 s fun _ => a) ≤ Real.sqrt (2 * C ^ (2 * X.gA) * X.l2 1 s) :=
          Real.sqrt_le_sqrt hA
      _ = Real.sqrt 2 * C ^ X.gA * Real.sqrt (X.l2 1 s) := hsplit
      _ ≤ Real.exp 1 * C ^ X.gA * Real.sqrt (X.l2 1 s) := by gcongr

end

end ReciprocityTheory.ChartRestriction.G.I2
