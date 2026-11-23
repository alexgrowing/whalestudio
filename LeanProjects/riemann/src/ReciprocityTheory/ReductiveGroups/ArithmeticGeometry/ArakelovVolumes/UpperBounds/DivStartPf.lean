import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.JetsPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CoefficientConvolutionOfSubCoefficients
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DivSt

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem chi_zero {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) : X.χ 0 γ = 1 := by
  have h1 := X.χ_add 0 0 γ hγ
  rw [add_zero] at h1
  obtain ⟨n, hn, hpow⟩ := X.χ_fin 0
  have hne : X.χ 0 γ ≠ 0 := by
    intro h0
    have := hpow γ hγ
    rw [h0, zero_pow hn.ne'] at this
    exact zero_ne_one this
  have := mul_left_cancel₀ hne (h1.symm.trans (mul_one _).symm)
  exact this

theorem bchar_zero (b : Frame X.Ψ r) : bchar (0 : Wt X.Ψ r) b = 1 := by
  unfold bchar; simp

theorem sec_one : X.IsSec 0 (fun _ => (1 : ℂ)) := by
  refine ⟨differentiableOn_const _, fun x _ b _ => by rw [bchar_zero, one_mul], fun γ hγ x _ => by
    rw [chi_zero X hγ, one_mul]⟩

theorem sec_mul' {la la' : Wt X.Ψ r} {P Q : Frame X.Ψ r → ℂ} (hP : X.IsSec la P) (hQ : X.IsSec la' Q) :
    X.IsSec (la + la') (fun x => P x * Q x) :=
  PeriodLatticeMembership.sec_mul X hP hQ

theorem sec_zero (la : Wt X.Ψ r) : X.IsSec la (fun _ => (0 : ℂ)) :=
  ⟨differentiableOn_const _, fun _ _ _ _ => by ring, fun _ _ _ _ => by ring⟩

theorem sec_add {la : Wt X.Ψ r} {P Q : Frame X.Ψ r → ℂ} (hP : X.IsSec la P) (hQ : X.IsSec la Q) :
    X.IsSec la (fun x => P x + Q x) :=
  ⟨hP.1.add hQ.1, fun x hx b hb => by dsimp only; rw [hP.2.1 x hx b hb, hQ.2.1 x hx b hb]; ring,
    fun γ hγ x hx => by dsimp only; rw [hP.2.2 γ hγ x hx, hQ.2.2 γ hγ x hx]; ring⟩

theorem sec_sub {la : Wt X.Ψ r} {P Q : Frame X.Ψ r → ℂ} (hP : X.IsSec la P) (hQ : X.IsSec la Q) :
    X.IsSec la (fun x => P x - Q x) :=
  ⟨hP.1.sub hQ.1, fun x hx b hb => by dsimp only; rw [hP.2.1 x hx b hb, hQ.2.1 x hx b hb]; ring,
    fun γ hγ x hx => by dsimp only; rw [hP.2.2 γ hγ x hx, hQ.2.2 γ hγ x hx]; ring⟩

theorem sec_cmul {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (c : ℂ) (hP : X.IsSec la P) :
    X.IsSec la (fun x => c * P x) :=
  ⟨hP.1.const_mul c, fun x hx b hb => by dsimp only; rw [hP.2.1 x hx b hb]; ring,
    fun γ hγ x hx => by dsimp only; rw [hP.2.2 γ hγ x hx]; ring⟩

theorem sec_sum {ι : Type*} (s : Finset ι) {la : Wt X.Ψ r} {P : ι → Frame X.Ψ r → ℂ}
    (h : ∀ i ∈ s, X.IsSec la (P i)) : X.IsSec la (fun x => ∑ i ∈ s, P i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sec_zero X la
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact sec_add X (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem sec_pow {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P) (n : ℕ) :
    X.IsSec (n • la) (fun x => P x ^ n) := by
  induction n with
  | zero =>
    rw [zero_nsmul]
    have e : (fun x => P x ^ 0) = fun _ => (1 : ℂ) := funext fun x => pow_zero _
    rw [e]; exact sec_one X
  | succ n ih =>
    have := sec_mul' X ih hP
    rw [succ_nsmul]
    have e : (fun x => P x ^ (n + 1)) = fun x => P x ^ n * P x := funext fun x => pow_succ _ _
    rw [e]; exact this

theorem sec_prod {ι : Type*} (s : Finset ι) (la : ι → Wt X.Ψ r) {P : ι → Frame X.Ψ r → ℂ}
    (h : ∀ i ∈ s, X.IsSec (la i) (P i)) : X.IsSec (∑ i ∈ s, la i) (fun x => ∏ i ∈ s, P i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sec_one X
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    exact sec_mul' X (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem sec_lead {Xa : ArchInM X} (Fl : FlatM X Xa) {δ : ℕ} (t : Fin δ → Frame X.Ψ r → ℂ)
    (ht : ∀ k, X.IsSec Xa.Fp (t k)) (hs : ∀ k, X.IsSec Xa.L (Fl.s k)) (hw : X.IsSec Xa.L Fl.w0)
    (a0 : ℕ) (ha0 : a0 ≤ Xa.T) (cc : (Fin (nd X) → ℕ) → Fin δ → ℂ) :
    X.IsSec (Xa.Fp + Xa.T • Xa.L) (leadM X Fl.s Fl.w0 t Xa.T a0 cc) := by
  unfold leadM
  refine sec_sum X _ fun α hα => sec_sum X _ fun k _ => ?_
  have hα' : ∑ q, α q < a0 := ReciprocityTheory.ChartRestriction.G.AR.mem_multiLt_iff.mp hα
  have hm : X.IsSec ((∑ q, α q) • Xa.L) (monoM X Fl.s α) := by
    have := sec_prod X Finset.univ (fun q => α q • Xa.L) (P := fun q x => Fl.s q x ^ α q)
      (fun q _ => sec_pow X (hs q) (α q))
    rw [← Finset.sum_smul] at this
    exact this
  have h1 := sec_mul' X (sec_mul' X hm (sec_pow X hw (Xa.T - ∑ q, α q))) (ht k)
  have hwt : (∑ q, α q) • Xa.L + (Xa.T - ∑ q, α q) • Xa.L + Xa.Fp = Xa.Fp + Xa.T • Xa.L := by
    rw [← add_smul, Nat.add_sub_cancel' (by omega), add_comm]
  rw [hwt] at h1
  have h2 := sec_cmul X (cc α k) h1
  refine ⟨h2.1.congr fun x _ => by simp [mul_assoc], fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · have := h2.2.1 x hx b hb; simp only [mul_assoc] at this ⊢; exact this
  · have := h2.2.2 γ hγ x hx; simp only [mul_assoc] at this ⊢; exact this

theorem pnorm_eq' (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm la P x = ‖P x‖ * X.nfac la x := rfl

theorem nfac_nonneg' (la : Wt X.Ψ r) (x : Frame X.Ψ r) : 0 ≤ X.nfac la x :=
  Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _

theorem nfac_add {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la la' : Wt X.Ψ r) :
    X.nfac (la + la') x = X.nfac la x * X.nfac la' x := by
  unfold Data.nfac
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hpos : 0 < ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ :=
    norm_pos_iff.mpr (div_ne_zero (IW.dmin_ne_zero X hx τ _) (IW.dmin_ne_zero X hx τ _))
  rw [← Real.rpow_add hpos]
  congr 1
  simp only [Pi.add_apply]
  push_cast
  ring

theorem nfac_nsmul {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la : Wt X.Ψ r) (n : ℕ) :
    X.nfac (n • la) x = X.nfac la x ^ n := by
  induction n with
  | zero =>
    unfold Data.nfac
    simp
  | succ n ih => rw [succ_nsmul, nfac_add X hx, ih, pow_succ]

theorem lead_le {Xa : ArchInM X} (Fl : FlatM X Xa) {δ : ℕ} (t : Fin δ → Frame X.Ψ r → ℂ) (a0 : ℕ)
    (ha0 : a0 ≤ Xa.T) (cc : (Fin (nd X) → ℕ) → Fin δ → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    {A Ct : ℝ} (hA : 0 ≤ A) (hCt : 0 ≤ Ct) (hs : ∀ q, X.pnorm Xa.L (Fl.s q) x ≤ A)
    (hw : X.pnorm Xa.L Fl.w0 x ≤ A) (ht : ∀ k, X.pnorm Xa.Fp (t k) x ≤ Ct) :
    X.pnorm (Xa.Fp + Xa.T • Xa.L) (leadM X Fl.s Fl.w0 t Xa.T a0 cc) x ≤
      (∑ α ∈ ReciprocityTheory.ChartRestriction.G.AR.multiLt (nd X) a0, ∑ k, ‖cc α k‖) * Ct * A ^ Xa.T := by
  set nL := X.nfac Xa.L x with hnLdef
  set nF := X.nfac Xa.Fp x with hnFdef
  have hnL : 0 ≤ nL := nfac_nonneg' X Xa.L x
  have hnF : 0 ≤ nF := nfac_nonneg' X Xa.Fp x
  rw [pnorm_eq', nfac_add X hx, nfac_nsmul X hx]
  unfold leadM
  have hterm : ∀ α ∈ ReciprocityTheory.ChartRestriction.G.AR.multiLt (nd X) a0, ∀ k,
      ‖cc α k * monoM X Fl.s α x * Fl.w0 x ^ (Xa.T - ∑ q, α q) * t k x‖ * (nF * nL ^ Xa.T) ≤
        ‖cc α k‖ * Ct * A ^ Xa.T := by
    intro α hα k
    have hα' : ∑ q, α q < a0 := ReciprocityTheory.ChartRestriction.G.AR.mem_multiLt_iff.mp hα
    have hsplit : nL ^ Xa.T = (∏ q, nL ^ α q) * nL ^ (Xa.T - ∑ q, α q) := by
      rw [Finset.prod_pow_eq_pow_sum, ← pow_add, Nat.add_sub_cancel' (by omega)]
    have hAsplit : A ^ Xa.T = (∏ q, A ^ α q) * A ^ (Xa.T - ∑ q, α q) := by
      rw [Finset.prod_pow_eq_pow_sum, ← pow_add, Nat.add_sub_cancel' (by omega)]
    rw [norm_mul, norm_mul, norm_mul, norm_pow, monoM, norm_prod, hsplit, hAsplit]
    simp only [norm_pow]
    have e : ‖cc α k‖ * (∏ q, ‖Fl.s q x‖ ^ α q) * ‖Fl.w0 x‖ ^ (Xa.T - ∑ q, α q) * ‖t k x‖ *
        (nF * ((∏ q, nL ^ α q) * nL ^ (Xa.T - ∑ q, α q))) =
        ‖cc α k‖ * (∏ q, (‖Fl.s q x‖ * nL) ^ α q) * (‖Fl.w0 x‖ * nL) ^ (Xa.T - ∑ q, α q) *
          (‖t k x‖ * nF) := by
      simp only [mul_pow, Finset.prod_mul_distrib]
      ring
    rw [e]
    have h1 : ∏ q, (‖Fl.s q x‖ * nL) ^ α q ≤ ∏ q, A ^ α q :=
      Finset.prod_le_prod (fun q _ => pow_nonneg (mul_nonneg (norm_nonneg _) hnL) _)
        (fun q _ => pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) hnL) (hs q) _)
    have h2 : (‖Fl.w0 x‖ * nL) ^ (Xa.T - ∑ q, α q) ≤ A ^ (Xa.T - ∑ q, α q) :=
      pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) hnL) hw _
    have h3 : ‖t k x‖ * nF ≤ Ct := ht k
    have hp1 : 0 ≤ ∏ q, (‖Fl.s q x‖ * nL) ^ α q :=
      Finset.prod_nonneg fun q _ => pow_nonneg (mul_nonneg (norm_nonneg _) hnL) _
    have hp2 : 0 ≤ (‖Fl.w0 x‖ * nL) ^ (Xa.T - ∑ q, α q) := pow_nonneg (mul_nonneg (norm_nonneg _) hnL) _
    have hA1 : 0 ≤ ∏ q, A ^ α q := Finset.prod_nonneg fun q _ => pow_nonneg hA _
    calc ‖cc α k‖ * (∏ q, (‖Fl.s q x‖ * nL) ^ α q) * (‖Fl.w0 x‖ * nL) ^ (Xa.T - ∑ q, α q) *
          (‖t k x‖ * nF)
        ≤ ‖cc α k‖ * (∏ q, A ^ α q) * A ^ (Xa.T - ∑ q, α q) * Ct := by gcongr
      _ = ‖cc α k‖ * Ct * ((∏ q, A ^ α q) * A ^ (Xa.T - ∑ q, α q)) := by ring
  have hN : 0 ≤ nF * nL ^ Xa.T := mul_nonneg hnF (pow_nonneg hnL _)
  calc ‖∑ α ∈ ReciprocityTheory.ChartRestriction.G.AR.multiLt (nd X) a0, ∑ k,
        cc α k * monoM X Fl.s α x * Fl.w0 x ^ (Xa.T - ∑ q, α q) * t k x‖ * (nF * nL ^ Xa.T)
      ≤ (∑ α ∈ ReciprocityTheory.ChartRestriction.G.AR.multiLt (nd X) a0, ∑ k,
          ‖cc α k * monoM X Fl.s α x * Fl.w0 x ^ (Xa.T - ∑ q, α q) * t k x‖) * (nF * nL ^ Xa.T) := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => norm_sum_le _ _)
    _ = ∑ α ∈ ReciprocityTheory.ChartRestriction.G.AR.multiLt (nd X) a0, ∑ k,
          ‖cc α k * monoM X Fl.s α x * Fl.w0 x ^ (Xa.T - ∑ q, α q) * t k x‖ * (nF * nL ^ Xa.T) := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun α _ => Finset.sum_mul _ _ _
    _ ≤ ∑ α ∈ ReciprocityTheory.ChartRestriction.G.AR.multiLt (nd X) a0, ∑ k, ‖cc α k‖ * Ct * A ^ Xa.T :=
        Finset.sum_le_sum fun α hα => Finset.sum_le_sum fun k _ => hterm α hα k
    _ = _ := by
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun α _ => by rw [Finset.sum_mul, Finset.sum_mul]

theorem pnorm_sub_le' (la : Wt X.Ψ r) (f g : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm la (fun y => f y - g y) x ≤ X.pnorm la f x + X.pnorm la g x := by
  rw [pnorm_eq', pnorm_eq', pnorm_eq', ← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (nfac_nonneg' X la x)

theorem sq_add_le (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a - b)]

theorem key_real {pd pf pl e W A K c : ℝ} {T : ℕ} (hpd0 : 0 ≤ pd) (hpl0 : 0 ≤ pl) (he : 0 ≤ e)
    (hK : 0 ≤ K) (hW : 0 ≤ W) (hA : A = Real.sqrt K * Real.sqrt W) (hpd : pd ≤ pf + pl)
    (hl : pl ≤ c * A ^ T) (hWe : W ^ T * e ≤ 1) :
    pd ^ 2 * e ≤ 2 * (pf ^ 2 * e) + 2 * c ^ 2 * K ^ T := by
  have hAT : (A ^ T) ^ 2 = K ^ T * W ^ T := by
    rw [← pow_mul, mul_comm T 2, pow_mul, hA, mul_pow, Real.sq_sqrt hK, Real.sq_sqrt hW, mul_pow]
  have h1 : pd ^ 2 ≤ 2 * pf ^ 2 + 2 * pl ^ 2 := (pow_le_pow_left₀ hpd0 hpd 2).trans (sq_add_le pf pl)
  have h2 : pl ^ 2 ≤ c ^ 2 * (K ^ T * W ^ T) := by
    rw [← hAT]
    calc pl ^ 2 ≤ (c * A ^ T) ^ 2 := pow_le_pow_left₀ hpl0 hl 2
      _ = c ^ 2 * (A ^ T) ^ 2 := by ring
  have h3 : pl ^ 2 * e ≤ c ^ 2 * K ^ T := by
    calc pl ^ 2 * e ≤ c ^ 2 * (K ^ T * W ^ T) * e := mul_le_mul_of_nonneg_right h2 he
      _ = c ^ 2 * K ^ T * (W ^ T * e) := by ring
      _ ≤ c ^ 2 * K ^ T * 1 := mul_le_mul_of_nonneg_left hWe (by positivity)
      _ = _ := mul_one _
  calc pd ^ 2 * e ≤ (2 * pf ^ 2 + 2 * pl ^ 2) * e := mul_le_mul_of_nonneg_right h1 he
    _ = 2 * (pf ^ 2 * e) + 2 * (pl ^ 2 * e) := by ring
    _ ≤ 2 * (pf ^ 2 * e) + 2 * (c ^ 2 * K ^ T) := by gcongr
    _ = _ := by ring

end

open DivSt in
theorem divStart_of {E : Type} [Field E] [NumberField E] [IsCMField E]
    (hFM : FundSetMeasStatement (E := E)) : DivStartStatement (E := E) := by
  intro r X Xa Fl hPD hFin δ t ht x0 ho FF hFF f hf hint cc
  have hsB : ∀ q, X.IsBddSec Xa.L (Fl.s q) := fun q => (Fl.s_van q).1.1
  have hwB : X.IsBddSec Xa.L Fl.w0 := Fl.weightForm_vanishes.1.1
  have hfB : X.IsBddSec (Xa.Fp + Xa.T • Xa.L) f := hf.1
  choose Cs hCs using fun q => (hsB q).2
  obtain ⟨Cw, hCw⟩ := hwB.2
  choose Ct' hCt' using fun k => (ht k).2
  obtain ⟨Cf, hCf⟩ := hfB.2
  set A0 : ℝ := (∑ q, |Cs q|) + |Cw| with hA0
  set Ct : ℝ := ∑ k, |Ct' k| with hCtdef
  have hA0n : 0 ≤ A0 := by positivity
  have hCtn : 0 ≤ Ct := by positivity
  have hsA0 : ∀ x ∈ X.dom, ∀ q, X.pnorm Xa.L (Fl.s q) x ≤ A0 := fun x hx q =>
    (hCs q x hx).trans ((le_abs_self _).trans (le_add_of_le_of_nonneg
      (Finset.single_le_sum (f := fun q => |Cs q|) (fun _ _ => abs_nonneg _) (Finset.mem_univ q)) (abs_nonneg _)))
  have hwA0 : ∀ x ∈ X.dom, X.pnorm Xa.L Fl.w0 x ≤ A0 := fun x hx =>
    (hCw x hx).trans ((le_abs_self _).trans (le_add_of_nonneg_left (by positivity)))
  have htC : ∀ x ∈ X.dom, ∀ k, X.pnorm Xa.Fp (t k) x ≤ Ct := fun x hx k =>
    (hCt' k x hx).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun k => |Ct' k|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)))
  set C1 : ℝ := ∑ α ∈ ReciprocityTheory.ChartRestriction.G.AR.multiLt (nd X) (Xa.T - nd X), ∑ k, ‖cc α k‖ with hC1
  have hC1n : 0 ≤ C1 := by positivity
  have hsec := sec_lead X Fl t (fun k => (ht k).1) (fun q => (hsB q).1) hwB.1 (Xa.T - nd X) (Nat.sub_le _ _) cc
  refine ⟨⟨sec_sub X hfB.1 hsec, Cf + C1 * Ct * A0 ^ Xa.T, fun x hx => ?_⟩, ?_⟩
  · exact (pnorm_sub_le' X _ _ _ x).trans (add_le_add (hCf x hx)
      (lead_le X Fl t _ (Nat.sub_le _ _) cc hx hA0n hCtn (hsA0 x hx) (hwA0 x hx) (htC x hx)))

  obtain ⟨Ks, hKs⟩ := Fl.s_le_w
  obtain ⟨Kw, hKw⟩ := Fl.denom_le_family
  set K : ℝ := |Ks| + |Kw| with hKdef
  have hK : 0 ≤ K := by positivity
  have hT : 0 < Xa.T := lt_of_lt_of_le (Nat.mul_pos (by norm_num) (pow_pos (by have := Xa.n_ge; omega) 2)) Xa.T_ge
  set B : ℝ := 2 * (C1 * Ct) ^ 2 * K ^ Xa.T with hBdef
  have hB : 0 ≤ B := by positivity
  have hpt : ∀ z ∈ FF, ENNReal.ofReal (X.pnorm (Xa.Fp + Xa.T • Xa.L)
        (fun x => f x - leadM X Fl.s Fl.w0 t Xa.T (Xa.T - nd X) cc x) (cpt X x0 z) ^ 2 *
        (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(Xa.T : ℝ))) ≤
      2 * ENNReal.ofReal (X.pnorm (Xa.Fp + Xa.T • Xa.L) f (cpt X x0 z) ^ 2 *
        (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(Xa.T : ℝ))) + ENNReal.ofReal B := by
    intro z hz
    have hx : cpt X x0 z ∈ X.dom := (hFF.2.1 hz)
    set x := cpt X x0 z with hxdef
    clear_value x
    set W := ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 with hWdef
    have hW : 0 ≤ W := by positivity
    set e := W ^ (-(Xa.T : ℝ)) with hedef
    have he : 0 ≤ e := Real.rpow_nonneg hW _
    have hWe : W ^ Xa.T * e ≤ 1 := by
      rcases eq_or_lt_of_le hW with h0 | h0
      · rw [hedef, ← h0, Real.zero_rpow (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hT.ne')), mul_zero]
        norm_num
      · rw [hedef, Real.rpow_neg hW, Real.rpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ h0.ne')]
    set A := Real.sqrt K * Real.sqrt W with hAdef
    have hA : 0 ≤ A := by positivity
    have hsA : ∀ q, X.pnorm Xa.L (Fl.s q) x ≤ A := by
      intro q
      have h1 : X.pnorm Xa.L (Fl.s q) x ^ 2 ≤ K * W := by
        calc X.pnorm Xa.L (Fl.s q) x ^ 2 ≤ ∑ q', X.pnorm Xa.L (Fl.s q') x ^ 2 :=
              Finset.single_le_sum (f := fun q' => X.pnorm Xa.L (Fl.s q') x ^ 2) (fun _ _ => sq_nonneg _)
                (Finset.mem_univ q)
          _ ≤ Ks * W := hKs x hx
          _ ≤ K * W := mul_le_mul_of_nonneg_right ((le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))) hW
      rw [hAdef, ← Real.sqrt_mul hK]
      exact Real.le_sqrt_of_sq_le h1
    have hwA : X.pnorm Xa.L Fl.w0 x ≤ A := by
      have h1 : X.pnorm Xa.L Fl.w0 x ^ 2 ≤ K * W :=
        (hKw x hx).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))) hW)
      rw [hAdef, ← Real.sqrt_mul hK]
      exact Real.le_sqrt_of_sq_le h1
    have hl := lead_le X Fl t (Xa.T - nd X) (Nat.sub_le Xa.T (nd X)) cc hx hA hCtn hsA hwA (htC x hx)
    have hpf := DivSt.pnorm_sub_le' X (Xa.Fp + Xa.T • Xa.L) f (leadM X Fl.s Fl.w0 t Xa.T (Xa.T - nd X) cc) x
    set pf := X.pnorm (Xa.Fp + Xa.T • Xa.L) f x
    set pl := X.pnorm (Xa.Fp + Xa.T • Xa.L) (leadM X Fl.s Fl.w0 t Xa.T (Xa.T - nd X) cc) x
    set pd := X.pnorm (Xa.Fp + Xa.T • Xa.L) (fun x => f x - leadM X Fl.s Fl.w0 t Xa.T (Xa.T - nd X) cc x) x
    have hpd0 : 0 ≤ pd := mul_nonneg (norm_nonneg _) (nfac_nonneg' X _ _)
    have hpf0 : 0 ≤ pf := mul_nonneg (norm_nonneg _) (nfac_nonneg' X _ _)
    have hpl0 : 0 ≤ pl := mul_nonneg (norm_nonneg _) (nfac_nonneg' X _ _)
    clear_value pd pf pl
    have hreal : pd ^ 2 * e ≤ 2 * (pf ^ 2 * e) + B := by
      have := key_real hpd0 hpl0 he hK hW hAdef hpf hl hWe
      rw [hBdef]
      calc pd ^ 2 * e ≤ _ := this
        _ = _ := by ring
    calc ENNReal.ofReal (pd ^ 2 * e) ≤ ENNReal.ofReal (2 * (pf ^ 2 * e) + B) := ENNReal.ofReal_le_ofReal hreal
      _ ≤ ENNReal.ofReal (2 * (pf ^ 2 * e)) + ENNReal.ofReal B := ENNReal.ofReal_add_le
      _ = 2 * ENNReal.ofReal (pf ^ 2 * e) + ENNReal.ofReal B := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  have hmeas : MeasurableSet FF := hFF.1
  have hfin := hFM r X x0 FF ho hFF hFin
  calc ∫⁻ z in FF, _ ∂muF X x0 ≤ ∫⁻ z in FF, (2 * ENNReal.ofReal (X.pnorm (Xa.Fp + Xa.T • Xa.L) f (cpt X x0 z) ^ 2 *
        (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(Xa.T : ℝ))) + ENNReal.ofReal B) ∂muF X x0 :=
        setLIntegral_mono' hmeas hpt
    _ = 2 * ∫⁻ z in FF, ENNReal.ofReal (X.pnorm (Xa.Fp + Xa.T • Xa.L) f (cpt X x0 z) ^ 2 *
        (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(Xa.T : ℝ))) ∂muF X x0 +
          ENNReal.ofReal B * muF X x0 FF := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ (by norm_num), setLIntegral_const]
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (by norm_num) hint, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin⟩

end ReciprocityTheory.ChartRestriction.G.AR.Up.DivSt
