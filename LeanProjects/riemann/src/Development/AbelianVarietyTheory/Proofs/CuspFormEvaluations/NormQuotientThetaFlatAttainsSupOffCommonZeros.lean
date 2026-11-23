import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BigStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.VanishAtSStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldPfC

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

noncomputable section

namespace GlobalTheory.QuotientMax

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem sat_open (X : Data E r) {x1 : Frame X.Ψ r} (hx1 : x1 ∈ X.dom) :
    ∃ ρ0 : ℝ, 0 < ρ0 ∧ ∀ ρ : ℝ, ρ ≤ ρ0 →
      IsOpen {x | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z' ∈ Metric.ball (0 : V (nd X)) ρ,
        x = lact γ (rmul (cpt X x1 z') b)} := by
  obtain ⟨x1', ho', b1, hb1, rfl⟩ := ortho_holds r X x1 hx1
  obtain ⟨D⟩ := ExtFPf.luData_of lu_holds X x1' ho'
  obtain ⟨ρ2, hρ2, hball2⟩ :=
    Metric.isOpen_iff.mp (ExF.isOpen_OmF X x1') 0 (IW.zero_mem_OmF X x1' ho')
  exact ⟨ρ2, hρ2, fun ρ hρ => LUB.isOpen_sat D ho' hb1 ((Metric.ball_subset_ball hρ).trans hball2)⟩

theorem pnorm_nonneg (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) : 0 ≤ X.pnorm la P x :=
  mul_nonneg (norm_nonneg _) (BoundedSectionAlgebra.nfac_pos X hx la).le

variable (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (f : Frame X.Ψ r → ℂ)

def thetaFac (x : Frame X.Ψ r) : ℝ :=
  X.pnorm ((nd X + 4) • Xa.L - Xa.Fp) Xa.th2 x ^ 2 * X.pnorm (2 • Xa.L - Xa.de) Xa.th1 x ^ 2 *
    (X.pnorm ((Xa.i * (Xa.g0 / 2)) • Xa.de) Xa.et x ^ 2) ^ ((1 : ℝ) / (Xa.i * (Xa.g0 / 2) : ℕ))

def sumSq (x : Frame X.Ψ r) : ℝ := ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2

def quot (x : Frame X.Ψ r) : ℝ :=
  X.pnorm (Xa.Fp + Xa.T • Xa.L) f x ^ 2 * thetaFac X Xa x /
    sumSq X Xa Fl x ^ ((Xa.T : ℝ) + nd X + 6 + 1 / 2)

theorem thetaFac_nonneg (x : Frame X.Ψ r) : 0 ≤ thetaFac X Xa x :=
  mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Real.rpow_nonneg (sq_nonneg _) _)

theorem sumSq_nonneg (x : Frame X.Ψ r) : 0 ≤ sumSq X Xa Fl x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem quot_inv (hf : X.IsSec (Xa.Fp + Xa.T • Xa.L) f) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    quot X Xa Fl f (lact γ (rmul x b)) = quot X Xa Fl f x := by
  unfold quot thetaFac sumSq
  rw [pointwiseNorm_invariance_holds r X _ _ Xa.et_sec γ hγ x hx b hb, pointwiseNorm_invariance_holds r X _ _ hf γ hγ x hx b hb,
    pointwiseNorm_invariance_holds r X _ _ Xa.firstTheta_vanishes.1.1.1 γ hγ x hx b hb,
    pointwiseNorm_invariance_holds r X _ _ Xa.secondTheta_vanishes.1.1.1 γ hγ x hx b hb]
  congr 2
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pointwiseNorm_invariance_holds r X _ _ (Fl.s_van k).1.1.1 γ hγ x hx b hb]

theorem quot_contOn (hf : X.IsSec (Xa.Fp + Xa.T • Xa.L) f) {A : Set (Frame X.Ψ r)} (hA : A ⊆ X.dom)
    (hS : ∀ x ∈ A, 0 < sumSq X Xa Fl x) : ContinuousOn (quot X Xa Fl f) A := by
  have h1 : ContinuousOn (thetaFac X Xa) X.dom :=
    (((BigB.pnorm_contOn X _ Xa.secondTheta_vanishes.1.1.1).pow 2).mul
      ((BigB.pnorm_contOn X _ Xa.firstTheta_vanishes.1.1.1).pow 2)).mul
      (((BigB.pnorm_contOn X _ Xa.et_sec).pow 2).rpow_const fun _ _ => Or.inr (by positivity))
  have h2 : ContinuousOn (sumSq X Xa Fl) X.dom :=
    continuousOn_finsetSum _ fun k _ => (BigB.pnorm_contOn X _ (Fl.s_van k).1.1.1).pow 2
  refine ContinuousOn.div ((((BigB.pnorm_contOn X _ hf).pow 2).mul h1).mono hA)
    ((h2.mono hA).rpow_const fun _ _ => Or.inr (by positivity)) fun x hx => ?_
  exact (Real.rpow_pos_of_pos (hS x hx) _).ne'

theorem thetaFac_le : ∃ C : ℝ, 0 < C ∧ ∀ x ∈ X.dom,
    thetaFac X Xa x ≤ C * Real.exp (-(4 / (Xa.g0 : ℝ)) * Xa.ph x) := by
  obtain ⟨K4, hK4⟩ := Xa.p4
  obtain ⟨C1, hC1⟩ := Xa.firstTheta_vanishes.1.1.2
  obtain ⟨C2, hC2⟩ := Xa.secondTheta_vanishes.1.1.2
  obtain ⟨g2, hg2⟩ := Xa.genus_even
  have hg0 : Xa.g0 = 2 * g2 := by omega
  have hg2p : 1 ≤ g2 := by have := Xa.genus_pos; omega
  have hdiv : Xa.g0 / 2 = g2 := by omega
  have hi : (1 : ℝ) ≤ Xa.i := by exact_mod_cast Xa.i_pos
  have hg2r : (1 : ℝ) ≤ g2 := by exact_mod_cast hg2p
  have hg : (2 : ℝ) ≤ Xa.g0 := by rw [hg0]; push_cast; linarith
  have hk0e : ((Xa.i * (Xa.g0 / 2) : ℕ) : ℝ) = Xa.i * ((Xa.g0 : ℝ) / 2) := by
    rw [hdiv, hg0]; push_cast; ring
  set k0 : ℝ := ((Xa.i * (Xa.g0 / 2) : ℕ) : ℝ) with hk0
  have hk0p : 0 < k0 := by rw [hk0e]; positivity
  refine ⟨(max C2 1) ^ 2 * (max C1 1) ^ 2 * (max K4 1) ^ (1 / k0), by positivity, fun x hx => ?_⟩
  have hA : (X.pnorm ((Xa.i * (Xa.g0 / 2)) • Xa.de) Xa.et x ^ 2) ^ (1 / k0) ≤
      (max K4 1) ^ (1 / k0) * Real.exp (-(4 / (Xa.g0 : ℝ)) * Xa.ph x) := by
    have h1 := (hK4 x hx).trans (mul_le_mul_of_nonneg_right (le_max_left K4 1) (Real.exp_pos _).le)
    have h2 := Real.rpow_le_rpow (sq_nonneg _) h1 (by positivity : (0 : ℝ) ≤ 1 / k0)
    rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul] at h2
    convert h2 using 3
    rw [hk0e]; field_simp; ring
  have h1 := pow_le_pow_left₀ (pnorm_nonneg X _ _ hx) ((hC1 x hx).trans (le_max_left C1 1)) 2
  have h2 := pow_le_pow_left₀ (pnorm_nonneg X _ _ hx) ((hC2 x hx).trans (le_max_left C2 1)) 2
  rw [mul_assoc]
  exact mul_le_mul (mul_le_mul h2 h1 (sq_nonneg _) (sq_nonneg _)) hA
    (Real.rpow_nonneg (sq_nonneg _) _) (by positivity)

theorem thetaFac_bdd : ∃ C : ℝ, 0 < C ∧ ∀ x ∈ X.dom, thetaFac X Xa x ≤ C := by
  obtain ⟨C, hC, h⟩ := thetaFac_le X Xa
  refine ⟨C, hC, fun x hx => (h x hx).trans (mul_le_of_le_one_right hC.le ?_)⟩
  rw [Real.exp_le_one_iff]
  have := Xa.ph_nonneg x hx
  have h2 : (0 : ℝ) ≤ 4 / (Xa.g0 : ℝ) := by positivity
  nlinarith

theorem sumSq_lower (j : Fin Fl.δ) : ∃ d : ℝ, 0 < d ∧ ∀ᶠ z in 𝓝 (0 : V (nd X)),
    d * ‖z‖ ^ 2 ≤ sumSq X Xa Fl (cpt X (Fl.xs j) z) := by
  have hx := Fl.xs_mem j
  have hn : 0 < nd X := by have := Xa.n_ge; omega
  have hs0 : ∀ k, Fl.s k (Fl.xs j) = 0 := (Fl.S_eq _ hx).mpr
    ⟨j, 1, X.Γ.one_mem, ExtFPf.oneF X, ExtFPf.oneF_mem X, by rw [ExtFPf.rmul_oneF, KU.lact_one]⟩
  set σ : V (nd X) → V (nd X) := fun z => WithLp.toLp 2 fun k =>
    Fl.s k (cpt X (Fl.xs j) z) / Fl.w0 (cpt X (Fl.xs j) z) with hσ
  have hσ0 : σ 0 = 0 := by
    simp [hσ, VanishPf.cpt_zero, hs0]
    rfl
  obtain ⟨c, hc, ev2⟩ := VanishPf.lower_of_det hn hσ0 (Fl.coord j)
  have ha : 0 < X.pnorm Xa.L Fl.w0 (Fl.xs j) :=
    mul_pos (norm_pos_iff.mpr (Fl.w0_ne j)) (BoundedSectionAlgebra.nfac_pos X hx _)
  set a := X.pnorm Xa.L Fl.w0 (Fl.xs j) with hadef
  have hc0 : Filter.Tendsto (cpt X (Fl.xs j)) (𝓝 0) (𝓝 (Fl.xs j)) := by
    have := (KU.cont_cpt X (Fl.xs j)).tendsto 0
    rwa [VanishPf.cpt_zero] at this
  have hca : ContinuousAt (X.pnorm Xa.L Fl.w0) (Fl.xs j) :=
    (BigB.pnorm_contOn X _ Fl.weightForm_vanishes.1.1.1).continuousAt ((PoinPf.isOpenDom X).mem_nhds hx)
  have ev1 : ∀ᶠ z in 𝓝 (0 : V (nd X)), a / 2 < X.pnorm Xa.L Fl.w0 (cpt X (Fl.xs j) z) :=
    (hca.tendsto.comp hc0).eventually (Ioi_mem_nhds (by linarith))
  refine ⟨(a / 2 * c) ^ 2, by positivity, ?_⟩
  filter_upwards [ev1, ev2] with z h1 h2
  set y := cpt X (Fl.xs j) z with hy
  have hw : Fl.w0 y ≠ 0 := by
    intro h0
    have : X.pnorm Xa.L Fl.w0 y = 0 := by unfold Data.pnorm; rw [h0, norm_zero, zero_mul]
    linarith
  have hS : sumSq X Xa Fl y = X.pnorm Xa.L Fl.w0 y ^ 2 * ‖σ z‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    show (‖Fl.s k y‖ * X.nfac Xa.L y) ^ 2 =
      (‖Fl.w0 y‖ * X.nfac Xa.L y) ^ 2 * ‖Fl.s k y / Fl.w0 y‖ ^ 2
    have := norm_pos_iff.mpr hw
    rw [norm_div]
    field_simp
  rw [hS, ← mul_pow, ← mul_pow, mul_assoc]
  exact pow_le_pow_left₀ (by positivity) (mul_le_mul h1.le h2 (by positivity) (by linarith)) 2

theorem quot_near (j : Fin Fl.δ)
    (hO : (fun z : V (nd X) => f (cpt X (Fl.xs j) z)) =O[𝓝 0] fun z => ‖z‖ ^ (Xa.T + nd X + 7))
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ z in 𝓝 (0 : V (nd X)),
      cpt X (Fl.xs j) z ∈ X.dom ∧ quot X Xa Fl f (cpt X (Fl.xs j) z) < ε := by
  have hx := Fl.xs_mem j
  obtain ⟨d, hd, ev1⟩ := sumSq_lower X Xa Fl j
  obtain ⟨C, hC, ev2⟩ := hO.exists_pos
  obtain ⟨B, hB, hBle⟩ := thetaFac_bdd X Xa
  have hc0 : Filter.Tendsto (cpt X (Fl.xs j)) (𝓝 0) (𝓝 (Fl.xs j)) := by
    have := (KU.cont_cpt X (Fl.xs j)).tendsto 0
    rwa [VanishPf.cpt_zero] at this
  have hnb := (PoinPf.isOpenDom X).mem_nhds hx
  set N := X.nfac (Xa.Fp + Xa.T • Xa.L) (Fl.xs j) + 1 with hN
  have hN0 : 0 < N := by have := BoundedSectionAlgebra.nfac_pos X hx (Xa.Fp + Xa.T • Xa.L); linarith
  have ev3 : ∀ᶠ z in 𝓝 (0 : V (nd X)), X.nfac (Xa.Fp + Xa.T • Xa.L) (cpt X (Fl.xs j) z) < N :=
    (((ExtFPf.nfac_contOn X _).continuousAt hnb).tendsto.comp hc0).eventually
      (Iio_mem_nhds (by linarith))
  set p : ℝ := (Xa.T : ℝ) + nd X + 6 + 1 / 2 with hp
  have hp0 : 0 < p := by positivity
  set K : ℝ := (C * N) ^ 2 * B / d ^ p with hK
  have hK0 : 0 < K := by positivity
  have ev4 : ∀ᶠ z in 𝓝 (0 : V (nd X)), ‖z‖ < ε / K := by
    filter_upwards [Metric.ball_mem_nhds (0 : V (nd X)) (div_pos hε hK0)] with z hz
    simpa using hz
  filter_upwards [ev1, ev2.bound, ev3, ev4, hc0.eventually hnb] with z h1 h2 h3 h4 hy
  refine ⟨hy, ?_⟩
  set y := cpt X (Fl.xs j) z with hydef
  rw [Real.norm_of_nonneg (by positivity)] at h2
  have hf : X.pnorm (Xa.Fp + Xa.T • Xa.L) f y ≤ C * ‖z‖ ^ (Xa.T + nd X + 7) * N :=
    mul_le_mul h2 h3.le (BoundedSectionAlgebra.nfac_pos X hy _).le (by positivity)
  have hnum : X.pnorm (Xa.Fp + Xa.T • Xa.L) f y ^ 2 * thetaFac X Xa y ≤
      (C * ‖z‖ ^ (Xa.T + nd X + 7) * N) ^ 2 * B :=
    mul_le_mul (pow_le_pow_left₀ (pnorm_nonneg X _ _ hy) hf 2) (hBle y hy) (thetaFac_nonneg X Xa y)
      (by positivity)
  rcases (norm_nonneg z).eq_or_lt with h0 | h0
  · have h5 : X.pnorm (Xa.Fp + Xa.T • Xa.L) f y ^ 2 * thetaFac X Xa y ≤ 0 := by
      rw [← h0] at hnum
      simpa using hnum
    exact lt_of_le_of_lt (div_nonpos_of_nonpos_of_nonneg h5
      (Real.rpow_nonneg (sumSq_nonneg X Xa Fl y) _)) hε
  · have hden : d ^ p * ‖z‖ ^ (2 * (Xa.T + nd X) + 13) ≤ sumSq X Xa Fl y ^ p := by
      refine le_trans (le_of_eq ?_) (Real.rpow_le_rpow (by positivity) h1 hp0.le)
      rw [Real.mul_rpow hd.le (by positivity), ← Real.rpow_natCast ‖z‖ 2, ← Real.rpow_mul h0.le,
        ← Real.rpow_natCast]
      congr 2
      rw [hp]; push_cast; ring
    have h6 : quot X Xa Fl f y ≤ (C * ‖z‖ ^ (Xa.T + nd X + 7) * N) ^ 2 * B /
        (d ^ p * ‖z‖ ^ (2 * (Xa.T + nd X) + 13)) :=
      div_le_div₀ (by positivity) hnum (by positivity) hden
    have h7 : (C * ‖z‖ ^ (Xa.T + nd X + 7) * N) ^ 2 * B /
        (d ^ p * ‖z‖ ^ (2 * (Xa.T + nd X) + 13)) = ‖z‖ * K := by
      rw [hK]
      have : 0 < d ^ p := by positivity
      field_simp
      ring
    rw [h7] at h6
    exact h6.trans_lt ((lt_div_iff₀ hK0).mp h4)

theorem sumSq_far {U : Set (Frame X.Ψ r)} (hU : IsOpen U) (hxs : ∀ j, Fl.xs j ∈ U)
    (hsat : ∀ x ∈ U, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ U) :
    ∃ d : ℝ, 0 < d ∧ ∀ x ∈ X.dom, x ∉ U →
      d * Real.exp (-(2 * Xa.c * Xa.ph x)) ≤ sumSq X Xa Fl x := by
  obtain ⟨K1, hK1⟩ := Fl.family_le_coords U hU hxs hsat
  obtain ⟨K3, hK3⟩ := Xa.p3
  refine ⟨(max K3 1 * max K1 1)⁻¹, by positivity, fun x hx hxU => ?_⟩
  rw [inv_mul_le_iff₀ (by positivity), mul_assoc (max K3 1)]
  have h1 := (hK1 x hx hxU).trans
    (mul_le_mul_of_nonneg_right (le_max_left K1 1) (sumSq_nonneg X Xa Fl x))
  have h2 := (hK3 x hx).trans
    (mul_le_mul_of_nonneg_right (le_max_left K3 1) (BigB.S_pos X Xa hx).le)
  exact h2.trans (mul_le_mul_of_nonneg_left h1 (by positivity))

theorem rate_pos : 0 < 4 / (Xa.g0 : ℝ) - 2 * Xa.c * ((Xa.T : ℝ) + nd X + 6 + 1 / 2) := by
  have hg : (1 : ℝ) ≤ Xa.g0 := by exact_mod_cast Xa.genus_pos
  have hc := Xa.c_pos
  have hT : (nd X : ℝ) + 7 ≤ Xa.T := by
    have h1 := Xa.T_ge
    have h2 := Xa.n_ge
    have : nd X + 7 ≤ Xa.T := by nlinarith
    exact_mod_cast this
  have h1 : (Xa.T : ℝ) * Xa.c ≤ 1 / Xa.g0 := by
    rw [le_div_iff₀ (by linarith)]; exact Xa.Tcg0
  have h2 : 4 / (Xa.g0 : ℝ) = 4 * (1 / Xa.g0) := by ring
  rw [h2]
  nlinarith

theorem quot_far (hf : X.IsBddSec (Xa.Fp + Xa.T • Xa.L) f) {A : Set (Frame X.Ψ r)} {d : ℝ}
    (hd : 0 < d) (hA : ∀ x ∈ X.dom, x ∈ A → d * Real.exp (-(2 * Xa.c * Xa.ph x)) ≤ sumSq X Xa Fl x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ X.dom, x ∈ A → X.la1 x < δ → quot X Xa Fl f x < ε := by
  obtain ⟨Cf, hCf⟩ := hf.2
  obtain ⟨B, hB, hBle⟩ := thetaFac_le X Xa
  obtain ⟨ca, ε0, hca, hε0, hp1⟩ := Xa.p1
  have hβ := rate_pos X Xa
  set p : ℝ := (Xa.T : ℝ) + nd X + 6 + 1 / 2 with hp
  have hp0 : 0 < p := by positivity
  set β : ℝ := 4 / (Xa.g0 : ℝ) - 2 * Xa.c * p with hβdef
  set K : ℝ := (max Cf 1) ^ 2 * B / d ^ p with hK
  have hK0 : 0 < K := by positivity
  set M : ℝ := K / (ε * β) with hM
  have hM0 : 0 < M := by positivity
  refine ⟨min ε0 (Real.sqrt (ca / M)), lt_min hε0 (Real.sqrt_pos.mpr (by positivity)),
    fun x hx hxA hl => ?_⟩
  have hlpos : 0 < X.la1 x := ModeHalfC.first_minimum_pos X hx (BigB.lam_ne X Xa)
  have hph : ca / X.la1 x ^ 2 ≤ Xa.ph x := hp1 x hx (lt_of_lt_of_le hl (min_le_left _ _))
  have hl2 : X.la1 x ^ 2 < ca / M :=
    (Real.lt_sqrt hlpos.le).mp (lt_of_lt_of_le hl (min_le_right _ _))
  have hbig : M < Xa.ph x := by
    refine lt_of_lt_of_le ?_ hph
    rw [lt_div_iff₀ (by positivity)]
    rw [lt_div_iff₀ hM0] at hl2
    linarith
  have hnum : X.pnorm (Xa.Fp + Xa.T • Xa.L) f x ^ 2 * thetaFac X Xa x ≤
      (max Cf 1) ^ 2 * (B * Real.exp (-(4 / (Xa.g0 : ℝ)) * Xa.ph x)) :=
    mul_le_mul (pow_le_pow_left₀ (pnorm_nonneg X _ _ hx) ((hCf x hx).trans (le_max_left _ _)) 2)
      (hBle x hx) (thetaFac_nonneg X Xa x) (by positivity)
  have hden : d ^ p * Real.exp (-(2 * Xa.c * Xa.ph x) * p) ≤ sumSq X Xa Fl x ^ p := by
    refine le_trans (le_of_eq ?_) (Real.rpow_le_rpow (by positivity) (hA x hx hxA) hp0.le)
    rw [Real.mul_rpow hd.le (Real.exp_pos _).le, ← Real.exp_mul]
  have h6 : quot X Xa Fl f x ≤ (max Cf 1) ^ 2 * (B * Real.exp (-(4 / (Xa.g0 : ℝ)) * Xa.ph x)) /
      (d ^ p * Real.exp (-(2 * Xa.c * Xa.ph x) * p)) :=
    div_le_div₀ (by positivity) hnum (by positivity) hden
  have h7 : (max Cf 1) ^ 2 * (B * Real.exp (-(4 / (Xa.g0 : ℝ)) * Xa.ph x)) /
      (d ^ p * Real.exp (-(2 * Xa.c * Xa.ph x) * p)) = K / Real.exp (β * Xa.ph x) := by
    have e : Real.exp (-(2 * Xa.c * Xa.ph x) * p) =
        Real.exp (-(4 / (Xa.g0 : ℝ)) * Xa.ph x) * Real.exp (β * Xa.ph x) := by
      rw [← Real.exp_add]; congr 1; rw [hβdef]; ring
    have : 0 < d ^ p := by positivity
    rw [e, hK]
    field_simp
  rw [h7] at h6
  refine h6.trans_lt ?_
  rw [div_lt_iff₀ (Real.exp_pos _)]
  have h8 := Real.add_one_le_exp (β * Xa.ph x)
  rw [hM, div_lt_iff₀ (by positivity)] at hbig
  nlinarith

theorem exists_max (hf : X.IsBddSec (Xa.Fp + Xa.T • Xa.L) f)
    (hO : ∀ j, (fun z : V (nd X) => f (cpt X (Fl.xs j) z)) =O[𝓝 0] fun z => ‖z‖ ^ (Xa.T + nd X + 7))
    (hpos : ∃ x ∈ X.dom, 0 < quot X Xa Fl f x) :
    ∃ x0 ∈ X.dom, (∃ k, Fl.s k x0 ≠ 0) ∧ 0 < quot X Xa Fl f x0 ∧
      ∀ x ∈ X.dom, quot X Xa Fl f x ≤ quot X Xa Fl f x0 := by
  obtain ⟨x1, hx1, hε⟩ := hpos
  have hρ : ∀ j, ∃ ρ : ℝ, 0 < ρ ∧
      IsOpen {x | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z' ∈ Metric.ball (0 : V (nd X)) ρ,
        x = lact γ (rmul (cpt X (Fl.xs j) z') b)} ∧
      ∀ z ∈ Metric.ball (0 : V (nd X)) ρ, cpt X (Fl.xs j) z ∈ X.dom ∧
        quot X Xa Fl f (cpt X (Fl.xs j) z) < quot X Xa Fl f x1 := by
    intro j
    obtain ⟨ρ0, hρ0, hop⟩ := sat_open X (Fl.xs_mem j)
    obtain ⟨ρ1, hρ1, h1⟩ := Metric.eventually_nhds_iff_ball.mp (quot_near X Xa Fl f j (hO j) hε)
    exact ⟨min ρ0 ρ1, lt_min hρ0 hρ1, hop _ (min_le_left _ _),
      fun z hz => h1 z (Metric.ball_subset_ball (min_le_right _ _) hz)⟩
  choose ρ hρ0 hop hsm using hρ
  set U : Set (Frame X.Ψ r) := ⋃ j, {x | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r,
    ∃ z' ∈ Metric.ball (0 : V (nd X)) (ρ j), x = lact γ (rmul (cpt X (Fl.xs j) z') b)} with hUdef
  have hU : IsOpen U := isOpen_iUnion hop
  have hxs : ∀ j, Fl.xs j ∈ U := fun j => Set.mem_iUnion.mpr
    ⟨j, 1, X.Γ.one_mem, ExtFPf.oneF X, ExtFPf.oneF_mem X, 0, Metric.mem_ball_self (hρ0 j), by
      rw [ExtFPf.rmul_oneF, KU.lact_one, VanishPf.cpt_zero]⟩
  have hsat : ∀ x ∈ U, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ U := by
    intro x hx γ hγ b hb
    obtain ⟨j, γ', hγ', b', hb', z, hz, rfl⟩ := Set.mem_iUnion.mp hx
    refine Set.mem_iUnion.mpr ⟨j, γ * γ', X.Γ.mul_mem hγ hγ', rmul b' b, ExtFPf.mul_mem X hb' hb,
      z, hz, ?_⟩
    rw [← PoinPf.lact_rmul', KU.lact_lact, ExtFPf.rmul_assoc]
  have hUsm : ∀ x ∈ U, quot X Xa Fl f x < quot X Xa Fl f x1 := by
    intro x hx
    obtain ⟨j, γ', hγ', b', hb', z, hz, rfl⟩ := Set.mem_iUnion.mp hx
    rw [quot_inv X Xa Fl f hf.1 hγ' (hsm j z hz).1 hb']
    exact (hsm j z hz).2
  obtain ⟨d, hd, hfar⟩ := sumSq_far X Xa Fl hU hxs hsat
  obtain ⟨δ, hδ, hsmall⟩ := quot_far X Xa Fl f hf (A := Uᶜ) hd hfar hε
  obtain ⟨Kc, hKc, hKsub, hrep⟩ := reductionTheory_holds r X δ hδ
  have hSpos : ∀ x ∈ Kc \ U, 0 < sumSq X Xa Fl x := fun x hx =>
    lt_of_lt_of_le (by positivity) (hfar x (hKsub hx.1) hx.2)
  have hmove : ∀ x ∈ X.dom, quot X Xa Fl f x1 ≤ quot X Xa Fl f x →
      ∃ y ∈ Kc \ U, quot X Xa Fl f y = quot X Xa Fl f x := by
    intro x hx hle
    have hxU : x ∉ U := fun h => absurd (hUsm x h) (not_lt.mpr hle)
    have hl : δ ≤ X.la1 x := by
      by_contra h
      exact absurd (hsmall x hx hxU (not_le.mp h)) (not_lt.mpr hle)
    obtain ⟨γ, hγ, b, hb, hy⟩ := hrep x hx hl
    have he := quot_inv X Xa Fl f hf.1 hγ hx hb
    exact ⟨_, ⟨hy, fun h => absurd (he ▸ hUsm _ h) (not_lt.mpr hle)⟩, he⟩
  obtain ⟨y1, hy1, he1⟩ := hmove x1 hx1 le_rfl
  obtain ⟨x0, hx0, hmax⟩ := (hKc.diff hU).exists_isMaxOn ⟨y1, hy1⟩
    (quot_contOn X Xa Fl f hf.1 (fun x hx => hKsub hx.1) hSpos)
  have hge : quot X Xa Fl f x1 ≤ quot X Xa Fl f x0 := he1 ▸ hmax hy1
  refine ⟨x0, hKsub hx0.1, ?_, hε.trans_le hge, fun x hx => ?_⟩
  · by_contra h
    push Not at h
    have h0 := hSpos x0 hx0
    simp [sumSq, Data.pnorm, h] at h0
  · rcases le_or_gt (quot X Xa Fl f x1) (quot X Xa Fl f x) with hle | hlt
    · obtain ⟨y, hy, he⟩ := hmove x hx hle
      exact he ▸ hmax hy
    · exact hlt.le.trans hge

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (f : Frame X.Ψ r → ℂ), X.IsBddSec (Xa.Fp + Xa.T • Xa.L) f → (∀ j, (fun z : V (nd X) => f (cpt X (Fl.xs j) z)) =O[𝓝 0] fun z => ‖z‖ ^ (Xa.T + nd X + 7)) → let Φ : Frame X.Ψ r → ℝ := fun x => X.pnorm (Xa.Fp + Xa.T • Xa.L) f x ^ 2 * X.pnorm ((nd X + 4) • Xa.L - Xa.Fp) Xa.th2 x ^ 2 * X.pnorm (2 • Xa.L - Xa.de) Xa.th1 x ^ 2 * (X.pnorm ((Xa.i * (Xa.g0 / 2)) • Xa.de) Xa.et x ^ 2) ^ ((1 : ℝ) / (Xa.i * (Xa.g0 / 2) : ℕ)) / (∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) ^ ((Xa.T : ℝ) + nd X + 6 + 1 / 2); (∃ x ∈ X.dom, 0 < Φ x) → ∃ x0 ∈ X.dom, (∃ k, Fl.s k x0 ≠ 0) ∧ 0 < Φ x0 ∧ ∀ x ∈ X.dom, Φ x ≤ Φ x0 := by
  intro E _ _ _ r X Xa Fl f hf hO Φ hpos
  have he : Φ = quot X Xa Fl f := by
    funext x
    simp only [Φ, quot, thetaFac, sumSq, mul_assoc]
  rw [he] at hpos ⊢
  exact exists_max X Xa Fl f hf hO hpos

end GlobalTheory.QuotientMax
