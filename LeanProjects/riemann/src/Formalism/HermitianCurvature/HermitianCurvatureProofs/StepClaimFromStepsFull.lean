import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaEprimeFromSteps

namespace Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
noncomputable section

theorem ds_zero {B : Base} (S : Step B) (Y : ℝ) : S.ds Y 0 = S.gX Y := dS_zero B _ _

theorem meas_iterDeriv {Ω : Type} [MeasurableSpace Ω] (F : ℝ → Ω → ℂ)
    (hsm : ∀ ω, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s => F s ω)) (hm : ∀ s, Measurable (F s)) :
    ∀ (p : ℕ) (s : ℝ), Measurable (fun ω => iteratedDeriv p (fun s => F s ω) s) := by
  intro p
  induction p with
  | zero => intro s; simpa using hm s
  | succ p ih =>
    intro s
    have hlim : ∀ ω, Tendsto (fun n : ℕ => ((1 : ℝ) / ((n : ℝ) + 1))⁻¹ •
        (iteratedDeriv p (fun s => F s ω) (s + 1 / ((n : ℝ) + 1)) - iteratedDeriv p (fun s => F s ω) s)) atTop
        (𝓝 (iteratedDeriv (p + 1) (fun s => F s ω) s)) := by
      intro ω
      have hd : Differentiable ℝ (iteratedDeriv p (fun s => F s ω)) :=
        (hsm ω).differentiable_iteratedDeriv p (by exact_mod_cast WithTop.coe_lt_top _)
      have h1 := (hd s).hasDerivAt.tendsto_slope_zero
      rw [iteratedDeriv_succ]
      refine h1.comp ?_
      refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
      exact Filter.Eventually.of_forall (fun n => by
        have : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        exact this.ne')
    refine measurable_of_tendsto_metrizable (f := fun (n : ℕ) ω => ((1 : ℝ) / ((n : ℝ) + 1))⁻¹ •
        (iteratedDeriv p (fun s => F s ω) (s + 1 / ((n : ℝ) + 1)) - iteratedDeriv p (fun s => F s ω) s)) ?_ ?_
    · intro n
      exact ((ih _).sub (ih _)).const_smul (((1 : ℝ) / ((n : ℝ) + 1))⁻¹)
    · exact tendsto_pi_nhds.2 hlim

theorem dsMeas : DsMeas := by
  intro B S hMeas hI4 Y hY p k
  obtain ⟨c, hc⟩ := hI4 Y hY
  have := meas_iterDeriv (fun s ω => S.gs Y s ω k) (fun ω => by
      have : (fun s : ℝ => S.gs Y s ω k) = fun s : ℝ => ∑ q ∈ range (S.r + 1 + 1), (s : ℂ) ^ q * c q ω k := by
        funext s; exact hc s ω k
      rw [this]
      apply ContDiff.sum
      intro q _
      exact (Complex.ofRealCLM.contDiff.pow q).mul contDiff_const)
    (fun s => (hMeas.2.2 Y hY).2 s k) p 0
  exact this

theorem stepClaimFromSteps (hDs : DsMeas) : StepClaimFromSteps := by
  intro hCauchy hMarkovV hTF hTR hTS hTB hTL hCT hLeib hTZ hCI hAdj hEF hCS hSh hMk hTermB hGeom hES hAbs hUB hFat hDom
  intro B S c σ CR Cd CP h4 hCR hCd hCP hL hLbig hImp hInt Y hY
  have hImp' := hImp
  obtain ⟨hMeas, hWPos, hPReg, hI3, hAdjB, hJet, hI4, hI4', hI5a, hRes, hWR, hPR⟩ := hImp
  have hσ : (0:ℝ) ≤ σ := by linarith
  have hStar : S.Star σ := hAdj hCauchy hLeib hCT hCI hTS hTR B S c σ h4 hMeas hWPos hI3 hAdjB hJet hI4 hI4' hInt
  have hUni : Uniform B S σ CR Cd CP :=
    hUB hAdj hTermB hES hAbs hEF hSh hMk hCS hCI hTZ hGeom hTR hTS hTB hLeib hCT hCauchy hMarkovV
      B S c σ CR Cd CP h4 hCR hCd hCP hL hLbig hImp' hInt
  have hCoef : S.CoefInt σ := hCI B S σ hσ hMeas hWPos hI4 hI4'
  have hF : ∀ p : ℕ, Integrable (LE.sq B (S.d Y) (S.ds Y p)) B.μ := by
    intro p
    exact (hFat hTR hTL B (Bool × S.ι) (S.d Y) (S.ds Y p) σ _ hσ (fun ω a => (hWPos.2 Y hY ω a).le)
      (fun a => (hMeas.2.2 Y hY).1 a) (fun a => hDs B S hMeas hI4 Y hY p a)
      (fun ε hε => hCoef ε hε Y hY p) (fun ε hε => hUni ε hε Y hY p)).1
  refine ⟨?_, hDom hTR hTL hTB hTZ hCauchy B S σ h4 hMeas hWPos hI4 hStar hInt Y hY hF⟩
  have := hF 0
  rwa [ds_zero] at this

theorem en_le_esup {B : Base} (S : Step B) (ε σ : ℝ) (hb : BddAbove (S.Eset ε σ)) (hP : S.PReg) (Y : ℝ) (hY : Y ∈ S.J) :
    S.En ε σ Y ≤ S.Esup ε σ * |S.P Y| := by
  have h1 : S.En ε σ Y / |S.P Y| ≤ S.Esup ε σ := le_csSup hb ⟨Y, hY, rfl⟩
  have hpos : 0 < |S.P Y| := abs_pos.mpr (hP.2 Y hY)
  rwa [div_le_iff₀ hpos] at h1

theorem termBound : TermBound := by
  intro hCS hSh hMk hCI hEF hTB hCauchy hMarkovV B S c σ ε CR Cd CP h4 hε hCR hCd hCP hL hImp Y hY p
  obtain ⟨hMeas, hWPos, hPReg, hI3, hAdjB, hJet, hI4, hI4', hI5a, hRes, hWR, hPR⟩ := hImp
  have hσ : (0:ℝ) ≤ σ := by linarith
  have hb := hEF B S σ ε hε hPReg hI4'
  have hCoef : S.CoefInt σ := hCI B S σ hσ hMeas hWPos hI4 hI4'
  have h1 := hCS hTB hCauchy B S σ ε h4 hε hMeas hWPos hI4 hI4' hCoef Y hY p
  have h2 := hSh B S σ ε CR Cd CP hσ hε hCR hCd hCP hMeas hWPos hPReg hI4' hI5a hRes hWR hPR hb
  have h3 := hMk hMarkovV B S σ ε (C7 CR Cd CP * S.Esup ε σ * |S.P Y|) hσ hε hL hMeas hWPos hI4 hI4' Y hY
    (fun s hs => h2 Y s hY hs) p
  have h4' := en_le_esup S ε σ hb hPReg Y hY
  have hEn0 : 0 ≤ S.En ε σ Y := by
    apply integral_nonneg
    intro ω
    apply mul_nonneg
    · exact Real.rpow_nonneg (div_nonneg (B.G_pos ω).le (by have := B.G_pos ω; linarith)) _
    · exact Finset.sum_nonneg (fun a _ => mul_nonneg (hWPos.2 Y hY ω a).le (by positivity))
  set Q := S.Esup ε σ * |S.P Y| with hQ
  have hQ0 : 0 ≤ Q := le_trans hEn0 h4'
  have hC7 : 0 ≤ C7 CR Cd CP := by unfold C7; positivity
  set m := 2 * ((S.r : ℝ) + 1) ^ 2 / S.L with hm
  have hm0 : 0 ≤ m := by rw [hm]; positivity
  have e1 : √(S.En ε σ Y) ≤ √Q := Real.sqrt_le_sqrt h4'
  have e2 : √(S.Dn ε σ Y p) ≤ m ^ p * (√(C7 CR Cd CP) * √Q) := by
    have : S.Dn ε σ Y p ≤ (m ^ p) ^ 2 * (C7 CR Cd CP * Q) := by
      have e : (m ^ p) ^ 2 * (C7 CR Cd CP * Q) = m ^ (2 * p) * (C7 CR Cd CP * S.Esup ε σ * |S.P Y|) := by
        rw [hQ, ← pow_mul, mul_comm p 2]; ring
      rw [e]; exact h3
    calc √(S.Dn ε σ Y p) ≤ √((m ^ p) ^ 2 * (C7 CR Cd CP * Q)) := Real.sqrt_le_sqrt this
      _ = m ^ p * (√(C7 CR Cd CP) * √Q) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), Real.sqrt_mul hC7]
  have hpre : 0 ≤ Real.exp 1 * (4 * σ) ^ p := by positivity
  calc ‖S.term ε σ Y p‖ ≤ Real.exp 1 * (4 * σ) ^ p * √(S.En ε σ Y) * √(S.Dn ε σ Y p) := h1
    _ ≤ Real.exp 1 * (4 * σ) ^ p * √Q * (m ^ p * (√(C7 CR Cd CP) * √Q)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left e1 hpre) e2 (Real.sqrt_nonneg _) (by positivity)
    _ = Real.exp 1 * √(C7 CR Cd CP) * (√Q * √Q) * ((4 * σ) * m) ^ p := by rw [mul_pow]; ring
    _ = Real.exp 1 * √(C7 CR Cd CP) * S.Esup ε σ * |S.P Y| * (8 * σ * ((S.r : ℝ) + 1) ^ 2 / S.L) ^ p := by
        rw [Real.mul_self_sqrt hQ0, hQ, hm]
        have : 4 * σ * (2 * ((S.r : ℝ) + 1) ^ 2 / S.L) = 8 * σ * ((S.r : ℝ) + 1) ^ 2 / S.L := by ring
        rw [this]; ring

theorem absorb : Absorb := by
  intro B S σ ε A hL hb h
  have hne : (S.Eset ε σ).Nonempty := ⟨_, S.a, ⟨le_refl _, by linarith⟩, rfl⟩
  have : S.Esup ε σ ≤ A + S.Esup ε σ / 2 := by
    apply csSup_le hne
    rintro _ ⟨Y, hY, rfl⟩
    exact h Y hY
  linarith

theorem uniformBound : UniformBound := by
  intro hAdj hTermB hES hAbs hEF hSh hMk hCS hCI hTZ hGeom hTR hTS hTB hLeib hCT hCauchy hMarkovV
  intro B S c σ CR Cd CP h4 hCR hCd hCP hL hLbig hImp hInt ε hε Y hY p
  have hImp' := hImp
  obtain ⟨hMeas, hWPos, hPReg, hI3, hAdjB, hJet, hI4, hI4', hI5a, hRes, hWR, hPR⟩ := hImp
  have hσ : (0:ℝ) ≤ σ := by linarith
  have hStar : S.Star σ := hAdj hCauchy hLeib hCT hCI hTS hTR B S c σ h4 hMeas hWPos hI3 hAdjB hJet hI4 hI4' hInt
  have hb := hEF B S σ ε hε hPReg hI4'
  have hT := hTermB hCS hSh hMk hCI hEF hTB hCauchy hMarkovV B S c σ ε CR Cd CP h4 hε hCR hCd hCP hL hImp'
  have hE := hES hTZ hGeom hTR B S c σ ε CR Cd CP h4 hε hCR hCd hCP hL hLbig hImp' hInt hStar hT
  have hA := hAbs B S σ ε S.A0 hL.le hb hE
  have h2 := hSh B S σ ε CR Cd CP hσ hε hCR hCd hCP hMeas hWPos hPReg hI4' hI5a hRes hWR hPR hb
  have h3 := hMk hMarkovV B S σ ε (C7 CR Cd CP * S.Esup ε σ * |S.P Y|) hσ hε hL hMeas hWPos hI4 hI4' Y hY
    (fun s hs => h2 Y s hY hs) p
  have hC7 : 0 ≤ C7 CR Cd CP := by unfold C7; positivity
  refine le_trans h3 ?_
  have hm : 0 ≤ (2 * ((S.r : ℝ) + 1) ^ 2 / S.L) ^ (2 * p) := by positivity
  have : C7 CR Cd CP * S.Esup ε σ * |S.P Y| ≤ C7 CR Cd CP * (2 * S.A0) * |S.P Y| := by
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    exact mul_le_mul_of_nonneg_left hA hC7
  calc _ ≤ (2 * ((S.r : ℝ) + 1) ^ 2 / S.L) ^ (2 * p) * (C7 CR Cd CP * (2 * S.A0) * |S.P Y|) :=
        mul_le_mul_of_nonneg_left this hm
    _ = _ := by ring

theorem geom_sum_mul_pred (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1/2) (R : ℕ) : ∑ p ∈ Icc 1 R, x ^ p ≤ 2 * x - 2 * x ^ (R + 1) := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have h1 : 0 ≤ x ^ (R + 1) := by positivity
    have h2 : x ^ (R + 1 + 1) = x ^ (R + 1) * x := pow_succ _ _
    nlinarith

theorem geomSum : GeomSum := by
  intro c x R hc hx0 hx
  set K := Real.exp 1 * √c with hK
  have hK0 : 0 ≤ K := by positivity
  have hden : 0 < 2 * (1 + 2 * Real.exp 1 * √c) := by positivity
  have hx2 : x ≤ 1 / 2 := by
    refine le_trans hx ?_
    rw [div_le_div_iff₀ hden (by norm_num)]
    nlinarith
  have h1 := geom_sum_mul_pred x hx0 hx2 R
  have h2 : 0 ≤ x ^ (R + 1) := by positivity
  have h3 : ∑ p ∈ Icc 1 R, x ^ p ≤ 2 * x := by linarith
  rw [← Finset.mul_sum]
  have h4 : x * (2 * (1 + 2 * K)) ≤ 1 := by
    have := hx
    rw [le_div_iff₀ hden] at this
    simpa [hK, mul_assoc] using this
  calc K * ∑ p ∈ Icc 1 R, x ^ p ≤ K * (2 * x) := mul_le_mul_of_nonneg_left h3 hK0
    _ ≤ 1 / 2 := by nlinarith

theorem termZero : TermZero := by
  intro B S ε σ Y
  unfold Step.term Step.En
  rw [ds_zero]
  simp only [Nat.factorial_zero, Nat.cast_one, div_one]
  rw [← integral_complex_ofReal]
  congr 1
  funext ω
  have hG := B.G_pos ω
  simp only [ld, iteratedDeriv_zero, Real.exp_log hG, pr, LE.sq]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem sum_Icc_one (f : ℕ → ℝ) (R : ℕ) : ∑ p ∈ Icc 1 R, f p = ∑ i ∈ range R, f (i + 1) := by
  induction R with
  | zero => simp
  | succ R ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem th_nonneg (B : Base) (ε σ : ℝ) (hε : 0 < ε) (ω : B.Ω) : 0 ≤ th ε σ (B.G ω) :=
  Real.rpow_nonneg (div_nonneg (B.G_pos ω).le (by have := B.G_pos ω; linarith)) _

theorem energyStep : EnergyStep := by
  intro hTZ hGeom hTR B S c σ ε CR Cd CP h4 hε hCR hCd hCP hL hLbig hImp hInt hStar hT Y hY
  obtain ⟨hMeas, hWPos, hPReg, hI3, hAdjB, hJet, hI4, hI4', hI5a, hRes, hWR, hPR⟩ := hImp
  have hσ : (0:ℝ) ≤ σ := by linarith
  have hP : 0 < |S.P Y| := abs_pos.mpr (hPReg.2 Y hY)
  have hC7 : 0 ≤ C7 CR Cd CP := by unfold C7; positivity
  have hsq0 : ∀ ω, 0 ≤ LE.sq B S.dw S.X ω := fun ω =>
    Finset.sum_nonneg (fun a _ => mul_nonneg (hWPos.1 ω a).le (by positivity))
  have hAth : S.Ath ε σ ≤ S.A0 := by
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall (fun ω => mul_nonneg (th_nonneg B ε σ hε ω) (hsq0 ω))
    · exact hInt
    · exact Filter.Eventually.of_forall (fun ω => by
        have := (hTR ε σ (B.G ω) hε hσ (B.G_pos ω)).2
        simpa using mul_le_mul_of_nonneg_right this (hsq0 ω))
  have hE0 : 0 ≤ S.Esup ε σ := by
    apply Real.sSup_nonneg
    rintro _ ⟨Y', hY', rfl⟩
    apply div_nonneg _ (abs_nonneg _)
    apply integral_nonneg
    intro ω
    exact mul_nonneg (th_nonneg B ε σ hε ω)
      (Finset.sum_nonneg (fun a _ => mul_nonneg (hWPos.2 Y' hY' ω a).le (by positivity)))
  set x := 8 * σ * ((S.r : ℝ) + 1) ^ 2 / S.L with hx
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hden : 0 < 2 * (1 + 2 * Real.exp 1 * √(C7 CR Cd CP)) := by positivity
  have hx1 : x ≤ 1 / (2 * (1 + 2 * Real.exp 1 * √(C7 CR Cd CP))) := by
    rw [le_div_iff₀ hden, hx, div_mul_eq_mul_div, div_le_one hL]
    linarith
  have hG := hGeom (C7 CR Cd CP) x (S.r + 1) hC7 hx0 hx1
  rw [sum_Icc_one] at hG
  have hs := hStar ε hε Y hY
  rw [Finset.sum_range_succ', hTZ] at hs
  have hnorm : ‖∑ i ∈ range (S.r + 1), S.term ε σ Y (i + 1)‖ ≤ S.Esup ε σ * |S.P Y| / 2 := by
    calc _ ≤ ∑ i ∈ range (S.r + 1), ‖S.term ε σ Y (i + 1)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ range (S.r + 1), (S.Esup ε σ * |S.P Y|) * (Real.exp 1 * √(C7 CR Cd CP) * x ^ (i + 1)) := by
          apply Finset.sum_le_sum
          intro i _
          have := hT Y hY (i + 1)
          calc _ ≤ _ := this
            _ = _ := by ring
      _ = (S.Esup ε σ * |S.P Y|) * ∑ i ∈ range (S.r + 1), (Real.exp 1 * √(C7 CR Cd CP) * x ^ (i + 1)) := by
          rw [Finset.mul_sum]
      _ ≤ (S.Esup ε σ * |S.P Y|) * (1 / 2) := mul_le_mul_of_nonneg_left hG (by positivity)
      _ = _ := by ring
  have hre : S.En ε σ Y = |S.P Y| * S.Ath ε σ - (∑ i ∈ range (S.r + 1), S.term ε σ Y (i + 1)).re := by
    have := congrArg Complex.re hs
    simp only [Complex.ofReal_re, Complex.add_re] at this
    linarith
  have hre2 : -(∑ i ∈ range (S.r + 1), S.term ε σ Y (i + 1)).re ≤ S.Esup ε σ * |S.P Y| / 2 := by
    have := Complex.abs_re_le_norm (∑ i ∈ range (S.r + 1), S.term ε σ Y (i + 1))
    have h2 := neg_abs_le (∑ i ∈ range (S.r + 1), S.term ε σ Y (i + 1)).re
    linarith
  rw [div_le_iff₀ hP]
  nlinarith

theorem eFinite : EFinite := by
  intro B S σ ε hε hP hI
  have hc : ContinuousOn (fun Y => S.En ε σ Y / |S.P Y|) S.J :=
    (hI ε hε).2.div (hP.1.abs) (fun Y hY => abs_ne_zero.mpr (hP.2 Y hY))
  exact (isCompact_Icc.image_of_continuousOn hc).bddAbove

theorem norm_add_sq_le (x y : ℂ) (c : ℝ) (hc : 0 ≤ c) : c * ‖x + y‖ ^ 2 ≤ c * (1 + c) * ‖x‖ ^ 2 + (1 + c) * ‖y‖ ^ 2 := by
  have h1 : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
  have h2 : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := by
    apply pow_le_pow_left₀ (norm_nonneg _) h1
  have h3 : 0 ≤ (c * ‖x‖ - ‖y‖) ^ 2 := sq_nonneg _
  have h4 : c * ‖x + y‖ ^ 2 ≤ c * (‖x‖ + ‖y‖) ^ 2 := mul_le_mul_of_nonneg_left h2 hc
  nlinarith

theorem shift_pt {B : Base} (S : Step B) (CR Cd : ℝ) (hCR : 0 ≤ CR) (hCd : 0 ≤ Cd) (hW : S.WPos) (h5 : S.ShiftFormula)
    (hRes : S.Residues CR) (hWR : S.WeightRatio Cd) (Y s : ℝ) (hY : Y ∈ S.J) (hYs : Y + s ∈ S.J) (ω : B.Ω) :
    LE.sq B (S.d Y) (S.gs Y s) ω ≤ (1 + CR) ^ 2 * (Cd * LE.sq B (S.d (Y + s)) (S.gX (Y + s)) ω) := by
  set u1 : S.ι → ℂ := fun i => S.gX (Y + s) ω (false, i) with hu1
  set u2 : S.ι → ℂ := fun i => S.gX (Y + s) ω (true, i) with hu2
  set t : S.ι → ℂ := fun i => ∑ j, (S.ee Y ω i j - S.ee (Y + s) ω i j) * u1 j with ht
  set A := ∑ i, S.d Y ω (false, i) * ‖u1 i‖ ^ 2 with hA
  set Bq := ∑ i, S.d Y ω (true, i) * ‖u2 i‖ ^ 2 with hBq
  set Tq := ∑ i, S.d Y ω (true, i) * ‖t i‖ ^ 2 with hTq
  set V := ∑ i, S.d Y ω (true, i) * ‖u2 i + t i‖ ^ 2 with hV
  have hd : ∀ k, 0 ≤ S.d Y ω k := fun k => (hW.2 Y hY ω k).le
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun i _ => mul_nonneg (hd _) (by positivity))
  have hB0 : 0 ≤ Bq := Finset.sum_nonneg (fun i _ => mul_nonneg (hd _) (by positivity))
  have hT : Tq ≤ CR ^ 2 * A := hRes Y s hY hYs ω u1
  have hL : LE.sq B (S.d Y) (S.gs Y s) ω = V + A := by
    unfold LE.sq
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    congr 1
    · apply Finset.sum_congr rfl; intro i _; rw [(h5 Y s hY hYs ω i).2]
    · apply Finset.sum_congr rfl; intro i _; rw [(h5 Y s hY hYs ω i).1]
  have hR : Bq + A ≤ Cd * LE.sq B (S.d (Y + s)) (S.gX (Y + s)) ω := by
    unfold LE.sq
    rw [Fintype.sum_prod_type, Fintype.sum_bool, mul_add, Finset.mul_sum, Finset.mul_sum]
    apply add_le_add
    · apply Finset.sum_le_sum; intro i _
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (hWR Y s hY hYs ω _) (by positivity)
    · apply Finset.sum_le_sum; intro i _
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (hWR Y s hY hYs ω _) (by positivity)
  have hVb : CR * V ≤ CR * (1 + CR) * Bq + (1 + CR) * Tq := by
    rw [hV, hBq, hTq, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro i _
    have := mul_le_mul_of_nonneg_left (norm_add_sq_le (u2 i) (t i) CR hCR) (hd (true, i))
    nlinarith
  have key : V + A ≤ (1 + CR) ^ 2 * (Bq + A) := by
    rcases hCR.eq_or_lt with h0 | hpos
    · have hT0 : Tq ≤ 0 := by rw [← h0] at hT; simpa using hT
      have hz : ∀ i ∈ (Finset.univ : Finset S.ι), S.d Y ω (true, i) * ‖t i‖ ^ 2 = 0 := by
        apply (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hd _) (by positivity))).1
        exact le_antisymm hT0 (Finset.sum_nonneg (fun i _ => mul_nonneg (hd _) (by positivity)))
      have hVB : V = Bq := by
        apply Finset.sum_congr rfl; intro i hi
        have h1 := hz i hi
        have h2 : t i = 0 := by
          rcases mul_eq_zero.1 h1 with h | h
          · exact absurd h (hW.2 Y hY ω _).ne'
          · simpa using h
        rw [h2, add_zero]
      rw [hVB, ← h0]; simp
    · have : CR * V ≤ CR * ((1 + CR) * Bq + (1 + CR) * CR * A) := by nlinarith
      have hV2 : V ≤ (1 + CR) * Bq + (1 + CR) * CR * A := le_of_mul_le_mul_left this hpos
      nlinarith
  rw [hL]
  exact le_trans key (mul_le_mul_of_nonneg_left hR (by positivity))

theorem gs_zero {B : Base} (S : Step B) (Y : ℝ) : S.gs Y 0 = S.gX Y := by
  funext ω a
  have h : mulF B (fun _ : ℝ => (1:ℝ)) S.X = S.X := by funext ω a; simp [mulF]
  simp [Step.gs, Step.gX, conjS, h]

theorem shiftBound : ShiftBound := by
  intro B S σ ε CR Cd CP hσ hε hCR hCd hCP hMeas hW hP hI4' h5 hRes hWR hPR hb Y s hY hYs
  have hint : Integrable (fun ω => th ε σ (B.G ω) * LE.sq B (S.d (Y + s)) (S.gX (Y + s)) ω) B.μ := by
    have := (hI4' ε hε).1 (Y + s) hYs 0
    rwa [gs_zero] at this
  have h1 : S.Ens ε σ Y s ≤ (1 + CR) ^ 2 * Cd * S.En ε σ (Y + s) := by
    unfold Step.Ens Step.En
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall (fun ω => mul_nonneg (th_nonneg B ε σ hε ω)
        (Finset.sum_nonneg (fun a _ => mul_nonneg (hW.2 Y hY ω a).le (by positivity))))
    · exact hint.const_mul _
    · exact Filter.Eventually.of_forall (fun ω => by
        have := mul_le_mul_of_nonneg_left (shift_pt S CR Cd hCR hCd hW h5 hRes hWR Y s hY hYs ω) (th_nonneg B ε σ hε ω)
        simp only
        calc _ ≤ _ := this
          _ = _ := by ring)
  have h2 : S.En ε σ (Y + s) / |S.P (Y + s)| ≤ S.Esup ε σ := le_csSup hb ⟨Y + s, hYs, rfl⟩
  have hpos : 0 < |S.P (Y + s)| := abs_pos.mpr (hP.2 _ hYs)
  rw [div_le_iff₀ hpos] at h2
  have hEn0 : 0 ≤ S.En ε σ (Y + s) := integral_nonneg (fun ω => mul_nonneg (th_nonneg B ε σ hε ω)
        (Finset.sum_nonneg (fun a _ => mul_nonneg (hW.2 _ hYs ω a).le (by positivity))))
  have hE0 : 0 ≤ S.Esup ε σ := by
    by_contra h
    push_neg at h
    nlinarith
  have h3 : S.Esup ε σ * |S.P (Y + s)| ≤ S.Esup ε σ * (CP * |S.P Y|) := mul_le_mul_of_nonneg_left (hPR Y s hY hYs) hE0
  have hk : 0 ≤ (1 + CR) ^ 2 * Cd := by positivity
  calc S.Ens ε σ Y s ≤ (1 + CR) ^ 2 * Cd * S.En ε σ (Y + s) := h1
    _ ≤ (1 + CR) ^ 2 * Cd * (S.Esup ε σ * (CP * |S.P Y|)) := mul_le_mul_of_nonneg_left (le_trans h2 h3) hk
    _ = C7 CR Cd CP * S.Esup ε σ * |S.P Y| := by unfold C7; ring

theorem stepClaimFromSteps_full : StepClaimFromSteps := stepClaimFromSteps dsMeas

end
end Formalism.FourierDecayAlt.P.LEx1
