import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfK
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfG

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ContDiff ENNReal

noncomputable section

section V

variable {n : ℕ} {U : Set (V n)}

def twoLog {N M : ℕ} (a c : ℝ) (w : Fin N → V n → ℂ) (s : Fin M → V n → ℂ) (y : V n) : ℝ :=
  a * Real.log (∑ k, Complex.normSq (w k y)) + c * Real.log (∑ k, Complex.normSq (s k y))

theorem sumSq_cdAt {N : ℕ} (hU : IsOpen U) {w : Fin N → V n → ℂ} (hw : ∀ k, DifferentiableOn ℂ (w k) U)
    {y : V n} (hy : y ∈ U) : ContDiffAt ℝ ∞ (fun v => ∑ k, Complex.normSq (w k v)) y :=
  ContDiffAt.sum fun k _ => HE.normSq_contDiffAt (HE.contDiffAt_of_punct hU (hw k) hy)

theorem twoLog_cdAt {N M : ℕ} (hU : IsOpen U) {w : Fin N → V n → ℂ} {s : Fin M → V n → ℂ}
    (hw : ∀ k, DifferentiableOn ℂ (w k) U) (hs : ∀ k, DifferentiableOn ℂ (s k) U) (a c : ℝ)
    {y : V n} (hy : y ∈ U) (hwp : 0 < ∑ k, Complex.normSq (w k y)) (hsp : 0 < ∑ k, Complex.normSq (s k y)) :
    ContDiffAt ℝ ∞ (twoLog a c w s) y := by
  unfold twoLog
  exact (contDiffAt_const.mul ((sumSq_cdAt hU hw hy).log hwp.ne')).add
    (contDiffAt_const.mul ((sumSq_cdAt hU hs hy).log hsp.ne'))

theorem logSum_levi_nonneg {N : ℕ} (hU : IsOpen U) {w : Fin N → V n → ℂ}
    (hw : ∀ k, DifferentiableOn ℂ (w k) U) (hwp : ∀ y ∈ U, 0 < ∑ k, Complex.normSq (w k y))
    {y : V n} (hy : y ∈ U) (ξ : Fin n → ℂ) :
    0 ≤ (leviV n (fun v => ((Real.log (∑ k, Complex.normSq (w k v)) : ℝ) : ℂ)) y ξ).re :=
  lseV n N U (fun k v => Complex.normSq (w k v)) hU
    (fun k => Or.inr ⟨w k, ((contDiffOn_of_differentiableOn n (w k) U hU (hw k)).of_le HE.two_le_inf),
      fun _ _ => rfl⟩) hwp y hy ξ

theorem twoLog_levi_nonneg {N M : ℕ} (hU : IsOpen U) {w : Fin N → V n → ℂ} {s : Fin M → V n → ℂ}
    (hw : ∀ k, DifferentiableOn ℂ (w k) U) (hs : ∀ k, DifferentiableOn ℂ (s k) U)
    (hwp : ∀ y ∈ U, 0 < ∑ k, Complex.normSq (w k y)) (hsp : ∀ y ∈ U, 0 < ∑ k, Complex.normSq (s k y))
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) {y : V n} (hy : y ∈ U) (ξ : Fin n → ℂ) :
    0 ≤ (leviV n (fun v => ((twoLog a c w s v : ℝ) : ℂ)) y ξ).re := by
  have h1 : ContDiffAt ℝ 2 (fun v => Real.log (∑ k, Complex.normSq (w k v))) y :=
    ((sumSq_cdAt hU hw hy).log (hwp y hy).ne').of_le HE.two_le_inf
  have h2 : ContDiffAt ℝ 2 (fun v => Real.log (∑ k, Complex.normSq (s k v))) y :=
    ((sumSq_cdAt hU hs hy).log (hsp y hy).ne').of_le HE.two_le_inf
  have e : (fun v => ((twoLog a c w s v : ℝ) : ℂ)) = fun v =>
      ((a * Real.log (∑ k, Complex.normSq (w k v)) + c * Real.log (∑ k, Complex.normSq (s k v)) : ℝ) : ℂ) := rfl
  rw [e, Y.LocalMaximumSecondDerivative.leviV_ofReal_add (contDiffAt_const.mul h1) (contDiffAt_const.mul h2),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h1, Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h2, Complex.add_re,
    Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  have := logSum_levi_nonneg hU hw hwp hy ξ
  have := logSum_levi_nonneg hU hs hsp hy ξ
  positivity

end V

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OW

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem pnorm_eq (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm la P x = ‖P x‖ * X.nfac la x := rfl

theorem exp_neg_phla (la : Wt X.Ψ r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Real.exp (-phla X la x) = X.nfac la x ^ 2 := by
  have hn : 0 < X.nfac la x := by
    unfold Data.nfac
    refine Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos ?_ _
    exact norm_pos_iff.mpr (div_ne_zero (IW.dmin_ne_zero X hx τ _) (IW.dmin_ne_zero X hx τ _))
  unfold phla
  rw [neg_mul, neg_neg, show 2 * Real.log (X.nfac la x) = Real.log (X.nfac la x ^ 2) by
    rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]

theorem pnorm_sq (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.pnorm la P x ^ 2 = Complex.normSq (P x) * Real.exp (-phla X la x) := by
  rw [pnorm_eq, mul_pow, exp_neg_phla X la hx, Complex.normSq_eq_norm_sq]

theorem sum_pnorm_sq {N : ℕ} (la : Wt X.Ψ r) (P : Fin N → Frame X.Ψ r → ℂ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) :
    ∑ k, X.pnorm la (P k) x ^ 2 = (∑ k, Complex.normSq (P k x)) * Real.exp (-phla X la x) := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun k _ => pnorm_sq X la (P k) hx)

theorem phla_add_nsmul {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la1 la2 : Wt X.Ψ r) (k : ℕ) :
    phla X (la1 + k • la2) x = phla X la1 x + k * phla X la2 x := by
  rw [IW.phla_eq X hx, IW.phla_eq X hx, IW.phla_eq X hx, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply]
  simp only [nsmul_eq_mul]
  push_cast
  ring

variable {X}

def PsK (Xa : ArchInM X) (Fl : FlatM X Xa) (x : Frame X.Ψ r) : ℝ :=
  phla X (Xa.Fp + Xa.T • Xa.L) x + (Xa.T : ℝ) * Real.log (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) +
    ((Xa.T : ℝ) - 1 / 2) * Real.log ((∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) / ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2)

theorem sumw_pos (Xa : ArchInM X) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    0 < ∑ k, Complex.normSq (Xa.w k x) := by
  obtain ⟨k, hk⟩ := Xa.w_nz x hx
  exact lt_of_lt_of_le (Complex.normSq_pos.2 hk)
    (Finset.single_le_sum (f := fun k => Complex.normSq (Xa.w k x)) (fun k _ => Complex.normSq_nonneg _)
      (Finset.mem_univ k))

theorem sums_pos {Xa : ArchInM X} (Fl : FlatM X Xa) {x : Frame X.Ψ r} {k0 : Fin (nd X)}
    (h : Fl.s k0 x ≠ 0) : 0 < ∑ k, Complex.normSq (Fl.s k x) :=
  lt_of_lt_of_le (Complex.normSq_pos.mpr h)
    (Finset.single_le_sum (f := fun k => Complex.normSq (Fl.s k x)) (fun k _ => Complex.normSq_nonneg _)
      (Finset.mem_univ k0))

theorem PsK_eq (Xa : ArchInM X) (Fl : FlatM X Xa) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hs : 0 < ∑ k, Complex.normSq (Fl.s k x)) :
    PsK Xa Fl x = phla X Xa.Fp x + ((1 / 2 : ℝ) * Real.log (∑ k, Complex.normSq (Xa.w k x)) +
      ((Xa.T : ℝ) - 1 / 2) * Real.log (∑ k, Complex.normSq (Fl.s k x))) := by
  have hw := sumw_pos Xa hx
  have he : 0 < Real.exp (-phla X Xa.L x) := Real.exp_pos _
  unfold PsK
  rw [sum_pnorm_sq X _ _ hx, sum_pnorm_sq X _ _ hx, phla_add_nsmul X hx, mul_div_mul_right _ _ he.ne',
    Real.log_mul hw.ne' he.ne', Real.log_exp, Real.log_div hs.ne' hw.ne']
  ring

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OW

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem WSk_eq_exp (Xa : ArchInM X) (Fl : FlatM X Xa) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hs : 0 < ∑ k, Complex.normSq (Fl.s k x)) :
    WSk X Xa Fl x = ENNReal.ofReal (Real.exp (-PsK Xa Fl x)) := by
  have hw := sumw_pos Xa hx
  have he : 0 < Real.exp (-phla X Xa.L x) := Real.exp_pos _
  have hA : 0 < ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 := by
    rw [sum_pnorm_sq X _ _ hx]; positivity
  have hS : 0 < ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 := by
    rw [sum_pnorm_sq X _ _ hx]; positivity
  have hR : 0 < (∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) / ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 := div_pos hS hA
  unfold WSk
  rw [if_pos hx, ENNReal.ofReal_rpow_of_pos hA, ENNReal.ofReal_rpow_of_pos hR,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.rpow_def_of_pos hA, Real.rpow_def_of_pos hR, ← Real.exp_add, ← Real.exp_add]
  congr 1
  unfold PsK
  ring

def Uk {Xa : ArchInM X} (Fl : FlatM X Xa) (x0 : Frame X.Ψ r) (k0 : Fin (nd X)) : Set (V (nd X)) :=
  {z | z ∈ OmF X x0 ∧ Fl.s k0 (cpt X x0 z) ≠ 0}

theorem s_diffOn {Xa : ArchInM X} (Fl : FlatM X Xa) (k : Fin (nd X)) : DifferentiableOn ℂ (Fl.s k) X.dom :=
  (Fl.s_van k).1.1.1.1

theorem w_diffOn (Xa : ArchInM X) (k : Fin Xa.N) : DifferentiableOn ℂ (Xa.w k) X.dom :=
  (Xa.w_van k).1.1.1.1

theorem isOpen_Uk {Xa : ArchInM X} (Fl : FlatM X Xa) (x0 : Frame X.Ψ r) (k0 : Fin (nd X)) :
    IsOpen (Uk Fl x0 k0) :=
  HE.isOpen_punct (ExF.isOpen_OmF X x0) (IW.comp_cpt_diffOn X (s_diffOn Fl k0) x0)

theorem PsK_cpt_eventually {Xa : ArchInM X} (Fl : FlatM X Xa) (x0 : Frame X.Ψ r) (k0 : Fin (nd X))
    {z : V (nd X)} (hz : z ∈ Uk Fl x0 k0) :
    (fun v => PsK Xa Fl (cpt X x0 v)) =ᶠ[𝓝 z] fun v => phla X Xa.Fp (cpt X x0 v) +
      twoLog (1 / 2) ((Xa.T : ℝ) - 1 / 2) (fun k v => Xa.w k (cpt X x0 v)) (fun k v => Fl.s k (cpt X x0 v)) v := by
  filter_upwards [(isOpen_Uk Fl x0 k0).mem_nhds hz] with v hv
  rw [PsK_eq Xa Fl hv.1 (sums_pos Fl hv.2)]
  rfl

theorem twoLog_cpt_cdAt {Xa : ArchInM X} (Fl : FlatM X Xa) (x0 : Frame X.Ψ r) (k0 : Fin (nd X))
    {z : V (nd X)} (hz : z ∈ Uk Fl x0 k0) (a c : ℝ) :
    ContDiffAt ℝ ∞ (twoLog a c (fun k v => Xa.w k (cpt X x0 v)) (fun k v => Fl.s k (cpt X x0 v))) z :=
  twoLog_cdAt (ExF.isOpen_OmF X x0) (fun k => IW.comp_cpt_diffOn X (w_diffOn Xa k) x0)
    (fun k => IW.comp_cpt_diffOn X (s_diffOn Fl k) x0) a c hz.1 (sumw_pos Xa hz.1) (sums_pos Fl hz.2)

theorem PsK_cpt_cdAt {Xa : ArchInM X} (Fl : FlatM X Xa) (x0 : Frame X.Ψ r) (k0 : Fin (nd X))
    {z : V (nd X)} (hz : z ∈ Uk Fl x0 k0) : ContDiffAt ℝ ∞ (fun v => PsK Xa Fl (cpt X x0 v)) z :=
  ((IW.phla_cpt_cdAt X x0 hz.1 Xa.Fp).add (twoLog_cpt_cdAt Fl x0 k0 hz _ _)).congr_of_eventuallyEq
    (PsK_cpt_eventually Fl x0 k0 hz)

theorem PsK_levi {Xa : ArchInM X} (Fl : FlatM X Xa) (x0 : Frame X.Ψ r) (k0 : Fin (nd X)) (m : ℝ)
    (hm : ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ)
    {z : V (nd X)} (hz : z ∈ Uk Fl x0 k0) (ξ : Fin (nd X) → ℂ) :
    m * (leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) z ξ).re ≤
      (leviV (nd X) (fun w => ((PsK Xa Fl (cpt X x0 w) - Real.log (densF X x0 w) : ℝ) : ℂ)) z ξ).re := by
  have hT : (0 : ℝ) ≤ (Xa.T : ℝ) - 1 / 2 := by
    have : (1 : ℝ) ≤ Xa.T := by
      have h1 := Xa.T_ge
      have h2 := Xa.n_ge
      have : 1 ≤ Xa.T := by nlinarith
      exact_mod_cast this
    linarith
  set tl := twoLog (1 / 2) ((Xa.T : ℝ) - 1 / 2) (fun k v => Xa.w k (cpt X x0 v))
    (fun k v => Fl.s k (cpt X x0 v)) with htl
  have hev : (fun w => ((PsK Xa Fl (cpt X x0 w) - Real.log (densF X x0 w) : ℝ) : ℂ)) =ᶠ[𝓝 z]
      fun w => (((phla X Xa.Fp (cpt X x0 w) + (-1) * Real.log (densF X x0 w)) + tl w : ℝ) : ℂ) := by
    filter_upwards [PsK_cpt_eventually Fl x0 k0 hz] with w hw
    rw [hw]
    push_cast
    ring
  have h1 := (IW.phla_cpt_cdAt X x0 hz.1 Xa.Fp).of_le HE.two_le_inf
  have h2 := (IW.logDens_cdAt X x0 hz.1).of_le HE.two_le_inf
  have h3 := (twoLog_cpt_cdAt Fl x0 k0 hz (1 / 2) ((Xa.T : ℝ) - 1 / 2)).of_le HE.two_le_inf
  have hU := isOpen_Uk Fl x0 k0
  have hpos : 0 ≤ (leviV (nd X) (fun v => ((tl v : ℝ) : ℂ)) z ξ).re :=
    twoLog_levi_nonneg hU (fun k => (IW.comp_cpt_diffOn X (w_diffOn Xa k) x0).mono fun v hv => hv.1)
      (fun k => (IW.comp_cpt_diffOn X (s_diffOn Fl k) x0).mono fun v hv => hv.1)
      (fun v hv => sumw_pos Xa hv.1) (fun v hv => sums_pos Fl hv.2) (by norm_num) hT hz ξ
  have hmz := hm z hz.1 ξ
  rw [leviV_congr hev, Y.LocalMaximumSecondDerivative.leviV_ofReal_add (h1.add (contDiffAt_const.mul h2)) h3,
    Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 (contDiffAt_const.mul h2), Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h2]
  simp only [Complex.add_re, Complex.re_ofReal_mul]
  unfold leviRh leviO leviM leviDens at hmz
  linarith

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OW
