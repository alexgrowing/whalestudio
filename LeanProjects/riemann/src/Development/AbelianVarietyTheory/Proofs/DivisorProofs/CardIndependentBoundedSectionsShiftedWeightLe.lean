import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormQuotientThetaFlatAttainsSupOffCommonZeros
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.QuotientNoPositiveMaxOffCommonZeros
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsMulNe

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares GlobalTheory.QuotientMax GlobalTheory.QuotNoMax
open scoped ContDiff ENNReal Matrix
open Filter Asymptotics

noncomputable section

namespace GlobalTheory.UpperShift

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

section
variable (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (T : ℕ) (f : Frame X.Ψ r → ℂ)

def quotT (x : Frame X.Ψ r) : ℝ :=
  X.pnorm (Xa.Fp + T • Xa.L) f x ^ 2 * thetaFac X Xa x /
    sumSq X Xa Fl x ^ ((T : ℝ) + nd X + 6 + 1 / 2)

theorem quotT_inv (hf : X.IsSec (Xa.Fp + T • Xa.L) f) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    quotT X Xa Fl T f (lact γ (rmul x b)) = quotT X Xa Fl T f x := by
  unfold quotT thetaFac sumSq
  rw [pointwiseNorm_invariance_holds r X _ _ Xa.et_sec γ hγ x hx b hb, pointwiseNorm_invariance_holds r X _ _ hf γ hγ x hx b hb,
    pointwiseNorm_invariance_holds r X _ _ Xa.firstTheta_vanishes.1.1.1 γ hγ x hx b hb,
    pointwiseNorm_invariance_holds r X _ _ Xa.secondTheta_vanishes.1.1.1 γ hγ x hx b hb]
  congr 2
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pointwiseNorm_invariance_holds r X _ _ (Fl.s_van k).1.1.1 γ hγ x hx b hb]

theorem quotT_contOn (hf : X.IsSec (Xa.Fp + T • Xa.L) f) {A : Set (Frame X.Ψ r)} (hA : A ⊆ X.dom)
    (hS : ∀ x ∈ A, 0 < sumSq X Xa Fl x) : ContinuousOn (quotT X Xa Fl T f) A := by
  have h1 : ContinuousOn (thetaFac X Xa) X.dom :=
    (((BigB.pnorm_contOn X _ Xa.secondTheta_vanishes.1.1.1).pow 2).mul
      ((BigB.pnorm_contOn X _ Xa.firstTheta_vanishes.1.1.1).pow 2)).mul
      (((BigB.pnorm_contOn X _ Xa.et_sec).pow 2).rpow_const fun _ _ => Or.inr (by positivity))
  have h2 : ContinuousOn (sumSq X Xa Fl) X.dom :=
    continuousOn_finsetSum _ fun k _ => (BigB.pnorm_contOn X _ (Fl.s_van k).1.1.1).pow 2
  refine ContinuousOn.div ((((BigB.pnorm_contOn X _ hf).pow 2).mul h1).mono hA)
    ((h2.mono hA).rpow_const fun _ _ => Or.inr (by positivity)) fun x hx => ?_
  exact (Real.rpow_pos_of_pos (hS x hx) _).ne'

theorem quotT_near (j : Fin Fl.δ)
    (hO : (fun z : V (nd X) => f (cpt X (Fl.xs j) z)) =O[𝓝 0] fun z => ‖z‖ ^ (T + nd X + 7))
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ z in 𝓝 (0 : V (nd X)),
      cpt X (Fl.xs j) z ∈ X.dom ∧ quotT X Xa Fl T f (cpt X (Fl.xs j) z) < ε := by
  have hx := Fl.xs_mem j
  obtain ⟨d, hd, ev1⟩ := sumSq_lower X Xa Fl j
  obtain ⟨C, hC, ev2⟩ := hO.exists_pos
  obtain ⟨B, hB, hBle⟩ := thetaFac_bdd X Xa
  have hc0 : Filter.Tendsto (cpt X (Fl.xs j)) (𝓝 0) (𝓝 (Fl.xs j)) := by
    have := (KU.cont_cpt X (Fl.xs j)).tendsto 0
    rwa [VanishPf.cpt_zero] at this
  have hnb := (PoinPf.isOpenDom X).mem_nhds hx
  set N := X.nfac (Xa.Fp + T • Xa.L) (Fl.xs j) + 1 with hN
  have hN0 : 0 < N := by have := BoundedSectionAlgebra.nfac_pos X hx (Xa.Fp + T • Xa.L); linarith
  have ev3 : ∀ᶠ z in 𝓝 (0 : V (nd X)), X.nfac (Xa.Fp + T • Xa.L) (cpt X (Fl.xs j) z) < N :=
    (((ExtFPf.nfac_contOn X _).continuousAt hnb).tendsto.comp hc0).eventually
      (Iio_mem_nhds (by linarith))
  set p : ℝ := (T : ℝ) + nd X + 6 + 1 / 2 with hp
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
  have hf : X.pnorm (Xa.Fp + T • Xa.L) f y ≤ C * ‖z‖ ^ (T + nd X + 7) * N :=
    mul_le_mul h2 h3.le (BoundedSectionAlgebra.nfac_pos X hy _).le (by positivity)
  have hnum : X.pnorm (Xa.Fp + T • Xa.L) f y ^ 2 * thetaFac X Xa y ≤
      (C * ‖z‖ ^ (T + nd X + 7) * N) ^ 2 * B :=
    mul_le_mul (pow_le_pow_left₀ (pnorm_nonneg X _ _ hy) hf 2) (hBle y hy) (thetaFac_nonneg X Xa y)
      (by positivity)
  rcases (norm_nonneg z).eq_or_lt with h0 | h0
  · have h5 : X.pnorm (Xa.Fp + T • Xa.L) f y ^ 2 * thetaFac X Xa y ≤ 0 := by
      rw [← h0] at hnum
      simpa using hnum
    exact lt_of_le_of_lt (div_nonpos_of_nonpos_of_nonneg h5
      (Real.rpow_nonneg (sumSq_nonneg X Xa Fl y) _)) hε
  · have hden : d ^ p * ‖z‖ ^ (2 * (T + nd X) + 13) ≤ sumSq X Xa Fl y ^ p := by
      refine le_trans (le_of_eq ?_) (Real.rpow_le_rpow (by positivity) h1 hp0.le)
      rw [Real.mul_rpow hd.le (by positivity), ← Real.rpow_natCast ‖z‖ 2, ← Real.rpow_mul h0.le,
        ← Real.rpow_natCast]
      congr 2
      rw [hp]; push_cast; ring
    have h6 : quotT X Xa Fl T f y ≤ (C * ‖z‖ ^ (T + nd X + 7) * N) ^ 2 * B /
        (d ^ p * ‖z‖ ^ (2 * (T + nd X) + 13)) :=
      div_le_div₀ (by positivity) hnum (by positivity) hden
    have h7 : (C * ‖z‖ ^ (T + nd X + 7) * N) ^ 2 * B /
        (d ^ p * ‖z‖ ^ (2 * (T + nd X) + 13)) = ‖z‖ * K := by
      rw [hK]
      have : 0 < d ^ p := by positivity
      field_simp
      ring
    rw [h7] at h6
    exact h6.trans_lt ((lt_div_iff₀ hK0).mp h4)

theorem quotT_far (hf : X.IsBddSec (Xa.Fp + T • Xa.L) f)
    (hrate : 0 < 4 / (Xa.g0 : ℝ) - 2 * Xa.c * ((T : ℝ) + nd X + 6 + 1 / 2)) {A : Set (Frame X.Ψ r)} {d : ℝ}
    (hd : 0 < d) (hA : ∀ x ∈ X.dom, x ∈ A → d * Real.exp (-(2 * Xa.c * Xa.ph x)) ≤ sumSq X Xa Fl x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ X.dom, x ∈ A → X.la1 x < δ → quotT X Xa Fl T f x < ε := by
  obtain ⟨Cf, hCf⟩ := hf.2
  obtain ⟨B, hB, hBle⟩ := thetaFac_le X Xa
  obtain ⟨ca, ε0, hca, hε0, hp1⟩ := Xa.p1
  have hβ := hrate
  set p : ℝ := (T : ℝ) + nd X + 6 + 1 / 2 with hp
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
  have hnum : X.pnorm (Xa.Fp + T • Xa.L) f x ^ 2 * thetaFac X Xa x ≤
      (max Cf 1) ^ 2 * (B * Real.exp (-(4 / (Xa.g0 : ℝ)) * Xa.ph x)) :=
    mul_le_mul (pow_le_pow_left₀ (pnorm_nonneg X _ _ hx) ((hCf x hx).trans (le_max_left _ _)) 2)
      (hBle x hx) (thetaFac_nonneg X Xa x) (by positivity)
  have hden : d ^ p * Real.exp (-(2 * Xa.c * Xa.ph x) * p) ≤ sumSq X Xa Fl x ^ p := by
    refine le_trans (le_of_eq ?_) (Real.rpow_le_rpow (by positivity) (hA x hx hxA) hp0.le)
    rw [Real.mul_rpow hd.le (Real.exp_pos _).le, ← Real.exp_mul]
  have h6 : quotT X Xa Fl T f x ≤ (max Cf 1) ^ 2 * (B * Real.exp (-(4 / (Xa.g0 : ℝ)) * Xa.ph x)) /
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

theorem exists_maxT (hf : X.IsBddSec (Xa.Fp + T • Xa.L) f)
    (hrate : 0 < 4 / (Xa.g0 : ℝ) - 2 * Xa.c * ((T : ℝ) + nd X + 6 + 1 / 2))
    (hO : ∀ j, (fun z : V (nd X) => f (cpt X (Fl.xs j) z)) =O[𝓝 0] fun z => ‖z‖ ^ (T + nd X + 7))
    (hpos : ∃ x ∈ X.dom, 0 < quotT X Xa Fl T f x) :
    ∃ x0 ∈ X.dom, (∃ k, Fl.s k x0 ≠ 0) ∧ 0 < quotT X Xa Fl T f x0 ∧
      ∀ x ∈ X.dom, quotT X Xa Fl T f x ≤ quotT X Xa Fl T f x0 := by
  obtain ⟨x1, hx1, hε⟩ := hpos
  have hρ : ∀ j, ∃ ρ : ℝ, 0 < ρ ∧
      IsOpen {x | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z' ∈ Metric.ball (0 : V (nd X)) ρ,
        x = lact γ (rmul (cpt X (Fl.xs j) z') b)} ∧
      ∀ z ∈ Metric.ball (0 : V (nd X)) ρ, cpt X (Fl.xs j) z ∈ X.dom ∧
        quotT X Xa Fl T f (cpt X (Fl.xs j) z) < quotT X Xa Fl T f x1 := by
    intro j
    obtain ⟨ρ0, hρ0, hop⟩ := sat_open X (Fl.xs_mem j)
    obtain ⟨ρ1, hρ1, h1⟩ := Metric.eventually_nhds_iff_ball.mp (quotT_near X Xa Fl T f j (hO j) hε)
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
  have hUsm : ∀ x ∈ U, quotT X Xa Fl T f x < quotT X Xa Fl T f x1 := by
    intro x hx
    obtain ⟨j, γ', hγ', b', hb', z, hz, rfl⟩ := Set.mem_iUnion.mp hx
    rw [quotT_inv X Xa Fl T f hf.1 hγ' (hsm j z hz).1 hb']
    exact (hsm j z hz).2
  obtain ⟨d, hd, hfar⟩ := sumSq_far X Xa Fl hU hxs hsat
  obtain ⟨δ, hδ, hsmall⟩ := quotT_far X Xa Fl T f hf hrate (A := Uᶜ) hd hfar hε
  obtain ⟨Kc, hKc, hKsub, hrep⟩ := reductionTheory_holds r X δ hδ
  have hSpos : ∀ x ∈ Kc \ U, 0 < sumSq X Xa Fl x := fun x hx =>
    lt_of_lt_of_le (by positivity) (hfar x (hKsub hx.1) hx.2)
  have hmove : ∀ x ∈ X.dom, quotT X Xa Fl T f x1 ≤ quotT X Xa Fl T f x →
      ∃ y ∈ Kc \ U, quotT X Xa Fl T f y = quotT X Xa Fl T f x := by
    intro x hx hle
    have hxU : x ∉ U := fun h => absurd (hUsm x h) (not_lt.mpr hle)
    have hl : δ ≤ X.la1 x := by
      by_contra h
      exact absurd (hsmall x hx hxU (not_le.mp h)) (not_lt.mpr hle)
    obtain ⟨γ, hγ, b, hb, hy⟩ := hrep x hx hl
    have he := quotT_inv X Xa Fl T f hf.1 hγ hx hb
    exact ⟨_, ⟨hy, fun h => absurd (he ▸ hUsm _ h) (not_lt.mpr hle)⟩, he⟩
  obtain ⟨y1, hy1, he1⟩ := hmove x1 hx1 le_rfl
  obtain ⟨x0, hx0, hmax⟩ := (hKc.diff hU).exists_isMaxOn ⟨y1, hy1⟩
    (quotT_contOn X Xa Fl T f hf.1 (fun x hx => hKsub hx.1) hSpos)
  have hge : quotT X Xa Fl T f x1 ≤ quotT X Xa Fl T f x0 := he1 ▸ hmax hy1
  refine ⟨x0, hKsub hx0.1, ?_, hε.trans_le hge, fun x hx => ?_⟩
  · by_contra h
    push Not at h
    have h0 := hSpos x0 hx0
    simp [sumSq, Data.pnorm, h] at h0
  · rcases le_or_gt (quotT X Xa Fl T f x1) (quotT X Xa Fl T f x) with hle | hlt
    · obtain ⟨y, hy, he⟩ := hmove x hx hle
      exact he ▸ hmax hy
    · exact hlt.le.trans hge

end

theorem mainT : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (T : ℕ) (f : Frame X.Ψ r → ℂ), 0 < 4 / (Xa.g0 : ℝ) - 2 * Xa.c * ((T : ℝ) + nd X + 6 + 1 / 2) → X.IsBddSec (Xa.Fp + T • Xa.L) f → (∀ j, (fun z : V (nd X) => f (cpt X (Fl.xs j) z)) =O[𝓝 0] fun z => ‖z‖ ^ (T + nd X + 7)) → let Φ : Frame X.Ψ r → ℝ := fun x => X.pnorm (Xa.Fp + T • Xa.L) f x ^ 2 * X.pnorm ((nd X + 4) • Xa.L - Xa.Fp) Xa.th2 x ^ 2 * X.pnorm (2 • Xa.L - Xa.de) Xa.th1 x ^ 2 * (X.pnorm ((Xa.i * (Xa.g0 / 2)) • Xa.de) Xa.et x ^ 2) ^ ((1 : ℝ) / (Xa.i * (Xa.g0 / 2) : ℕ)) / (∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) ^ ((T : ℝ) + nd X + 6 + 1 / 2); (∃ x ∈ X.dom, 0 < Φ x) → ∃ x0 ∈ X.dom, (∃ k, Fl.s k x0 ≠ 0) ∧ 0 < Φ x0 ∧ ∀ x ∈ X.dom, Φ x ≤ Φ x0 := by
  intro E _ _ _ r X Xa Fl T f hrate hf hO Φ hpos
  have he : Φ = quotT X Xa Fl T f := by
    funext x
    simp only [Φ, quotT, thetaFac, sumSq, mul_assoc]
  rw [he] at hpos ⊢
  exact exists_maxT X Xa Fl T f hf hrate hO hpos

theorem no_pos_maxT : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (T : ℕ) (f : Frame X.Ψ r → ℂ), X.IsSec (Xa.Fp + T • Xa.L) f → let Φ : Frame X.Ψ r → ℝ := fun x => X.pnorm (Xa.Fp + T • Xa.L) f x ^ 2 * X.pnorm ((nd X + 4) • Xa.L - Xa.Fp) Xa.th2 x ^ 2 * X.pnorm (2 • Xa.L - Xa.de) Xa.th1 x ^ 2 * (X.pnorm ((Xa.i * (Xa.g0 / 2)) • Xa.de) Xa.et x ^ 2) ^ ((1 : ℝ) / (Xa.i * (Xa.g0 / 2) : ℕ)) / (∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) ^ ((T : ℝ) + nd X + 6 + 1 / 2); ∀ x0 ∈ X.dom, (∃ k, Fl.s k x0 ≠ 0) → 0 < Φ x0 → ¬ ∀ x ∈ X.dom, Φ x ≤ Φ x0 := by
  intro E _ _ _ r X Xa Fl T f hf Φ x0 hx0 ⟨k0, hk0⟩ hpos hmax
  have hU : IsOpen (OmF X x0) := OntoB.isOpen_OmF X x0
  have h0U : (0 : V (nd X)) ∈ OmF X x0 := by show cpt X x0 0 ∈ X.dom; rw [IW.cpt_zero]; exact hx0
  set n1 : ℝ := ((Xa.i * (Xa.g0 / 2) : ℕ) : ℝ) with hn1
  have hn1p : 0 < n1 := by
    obtain ⟨g2, hg2⟩ := Xa.genus_even
    have h1 := Xa.i_pos
    have h2 := Xa.genus_pos
    have h3 : 1 ≤ Xa.g0 / 2 := by omega
    rw [hn1]
    have : 1 ≤ Xa.i * (Xa.g0 / 2) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    exact_mod_cast this
  have hz : ∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), P x0 = 0 → X.pnorm la P x0 ^ 2 = 0 := by
    intro la P h
    rw [OW.pnorm_eq, h]; simp
  have hf0 : f x0 ≠ 0 := fun h => by
    simp only [Φ, hz _ _ h, zero_mul, zero_div, lt_irrefl] at hpos
  have h20 : Xa.th2 x0 ≠ 0 := fun h => by
    simp only [Φ, hz _ _ h, zero_mul, mul_zero, zero_div, lt_irrefl] at hpos
  have h10 : Xa.th1 x0 ≠ 0 := fun h => by
    simp only [Φ, hz _ _ h, zero_mul, mul_zero, zero_div, lt_irrefl] at hpos
  have he0 : Xa.et x0 ≠ 0 := fun h => by
    have : (0 : ℝ) ^ ((1 : ℝ) / n1) = 0 := Real.zero_rpow (by positivity)
    simp only [Φ, hz _ _ h, ← hn1, this, mul_zero, zero_div, lt_irrefl] at hpos
  have hlog : ∀ x ∈ X.dom, f x ≠ 0 → Xa.th2 x ≠ 0 → Xa.th1 x ≠ 0 → Xa.et x ≠ 0 → Fl.s k0 x ≠ 0 →
      0 < Φ x ∧ Real.log (Φ x) = Real.log (Complex.normSq (f x)) + Real.log (Complex.normSq (Xa.th2 x)) +
      Real.log (Complex.normSq (Xa.th1 x)) + (1 / n1) * Real.log (Complex.normSq (Xa.et x)) +
      (-((T : ℝ) + nd X + 6 + 1 / 2)) * Real.log (∑ k, Complex.normSq (Fl.s k x)) +
      (1 / 2) * phla X Xa.L x := by
    intro x hx a1 a2 a3 a4 a5
    have hp : ∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), P x ≠ 0 → 0 < X.pnorm la P x ^ 2 := by
      intro la P h
      rw [OW.pnorm_sq X la P hx]
      exact mul_pos (Complex.normSq_pos.2 h) (Real.exp_pos _)
    have hsp := OW.sums_pos Fl a5
    have hS : 0 < ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 := by
      rw [OW.sum_pnorm_sq X _ _ hx]; exact mul_pos hsp (Real.exp_pos _)
    have p1 := hp (Xa.Fp + T • Xa.L) f a1
    have p2 := hp ((nd X + 4) • Xa.L - Xa.Fp) Xa.th2 a2
    have p3 := hp (2 • Xa.L - Xa.de) Xa.th1 a3
    have p4 := hp ((Xa.i * (Xa.g0 / 2)) • Xa.de) Xa.et a4
    have p5 := Real.rpow_pos_of_pos p4 (1 / n1)
    have p6 := Real.rpow_pos_of_pos hS ((T : ℝ) + nd X + 6 + 1 / 2)
    refine ⟨div_pos (mul_pos (mul_pos (mul_pos p1 p2) p3) p5) p6, ?_⟩
    simp only [Φ]
    rw [Real.log_div (mul_pos (mul_pos (mul_pos p1 p2) p3) p5).ne' p6.ne',
      Real.log_mul (mul_pos (mul_pos p1 p2) p3).ne' p5.ne', Real.log_mul (mul_pos p1 p2).ne' p3.ne',
      Real.log_mul p1.ne' p2.ne', Real.log_rpow p4, Real.log_rpow hS,
      BigC.log_pnorm_sq X hx a1, BigC.log_pnorm_sq X hx a2, BigC.log_pnorm_sq X hx a3,
      BigC.log_pnorm_sq X hx a4, OW.sum_pnorm_sq X _ _ hx, Real.log_mul hsp.ne' (Real.exp_pos _).ne',
      Real.log_exp, OW.phla_add_nsmul X hx, BigC.phla_sub X hx, BigC.phla_sub X hx,
      BigC.phla_nsmul X hx, BigC.phla_nsmul X hx, BigC.phla_nsmul X hx, ← hn1]
    push_cast
    field_simp
    ring
  have d1 := OntoB.hol_comp X x0 hf.1
  have d2 := OntoB.hol_comp X x0 Xa.secondTheta_vanishes.1.1.1.1
  have d3 := OntoB.hol_comp X x0 Xa.firstTheta_vanishes.1.1.1.1
  have d4 := OntoB.hol_comp X x0 Xa.et_sec.1
  have d5 := fun k => OntoB.hol_comp X x0 (OW.s_diffOn Fl k)
  have hc0 : cpt X x0 0 = x0 := IW.cpt_zero X x0
  have ev : ∀ {P : Frame X.Ψ r → ℂ}, DifferentiableOn ℂ (fun z => P (cpt X x0 z)) (OmF X x0) → P x0 ≠ 0 →
      ∀ᶠ z in 𝓝 (0 : V (nd X)), P (cpt X x0 z) ≠ 0 := fun hP h =>
    (hP.continuousOn.continuousAt (hU.mem_nhds h0U)).eventually_ne (by rw [hc0]; exact h)
  refine no_localMax hU h0U (a := fun z => f (cpt X x0 z)) (b := fun z => Xa.th2 (cpt X x0 z))
    (c := fun z => Xa.th1 (cpt X x0 z)) (d := fun z => Xa.et (cpt X x0 z)) d1 d2 d3 d4
    (by simpa only [hc0] using hf0) (by simpa only [hc0] using h20) (by simpa only [hc0] using h10)
    (by simpa only [hc0] using he0) (s := fun k z => Fl.s k (cpt X x0 z)) d5 (k0 := k0)
    (by simpa only [hc0] using hk0) (φ := fun z => phla X Xa.L (cpt X x0 z))
    ((IW.phla_cpt_cdAt X x0 h0U Xa.L).of_le HE.two_le_inf)
    (fun ξ hξ => Xa.posL x0 hx0 0 h0U ξ hξ) (1 / n1) (-((T : ℝ) + nd X + 6 + 1 / 2)) ?_
  filter_upwards [hU.mem_nhds h0U, ev d1 hf0, ev d2 h20, ev d3 h10, ev d4 he0, ev (d5 k0) hk0]
    with z hz a1 a2 a3 a4 a5
  obtain ⟨q1, q2⟩ := hlog _ hz a1 a2 a3 a4 a5
  obtain ⟨-, q3⟩ := hlog _ hx0 hf0 h20 h10 he0 hk0
  rw [hc0, ← q2, ← q3]
  exact Real.log_le_log q1 (hmax _ hz)

theorem rate_shift {X : Data E r} (Xa : ArchInM X) :
    0 < 4 / (Xa.g0 : ℝ) - 2 * Xa.c * (((Xa.T + (nd X + 4) : ℕ) : ℝ) + nd X + 6 + 1 / 2) := by
  have hg : (1 : ℝ) ≤ Xa.g0 := by exact_mod_cast Xa.genus_pos
  have hc := Xa.c_pos
  have hT : (2 * nd X : ℝ) + 11 ≤ Xa.T := by
    have h1 := Xa.T_ge
    have h2 := Xa.n_ge
    have : 2 * nd X + 11 ≤ Xa.T := by nlinarith
    exact_mod_cast this
  have hn : (0 : ℝ) ≤ nd X := Nat.cast_nonneg _
  have h1 : (Xa.T : ℝ) * Xa.c * Xa.g0 ≤ 1 := Xa.Tcg0
  set y : ℝ := Xa.c * Xa.g0 with hy
  have hy0 : 0 < y := by positivity
  have h2 : y * (2 * nd X + 21 / 2) < y * Xa.T := mul_lt_mul_of_pos_left (by linarith) hy0
  have h3 : 2 * y * ((Xa.T : ℝ) + 2 * nd X + 21 / 2) < 4 := by nlinarith
  have h4 : 4 / (Xa.g0 : ℝ) - 2 * Xa.c * (((Xa.T + (nd X + 4) : ℕ) : ℝ) + nd X + 6 + 1 / 2) =
      (4 - 2 * y * ((Xa.T : ℝ) + 2 * nd X + 21 / 2)) / Xa.g0 := by
    rw [hy]; push_cast; field_simp; ring
  rw [h4]
  exact div_pos (by linarith) (by linarith)

end GlobalTheory.UpperShift

namespace GlobalTheory.UpperShift

open GlobalTheory.UpperModel GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

theorem upper_shift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (m : ℕ) (f : Fin m → Frame X.Ψ r → ℂ), (∀ q, X.IsBddSec (Xa.Fp + (Xa.T + (nd X + 4)) • Xa.L) (f q)) → (∀ u : Fin m → ℂ, (∀ x ∈ X.dom, ∑ q, u q * f q x = 0) → u = 0) → m ≤ Fl.δ * (Xa.T + 3 * nd X + 10).choose (nd X) := by
  intro E _ _ _ r X Xa Fl m f hf hind
  by_contra hm
  obtain ⟨u, hu, hO⟩ := exists_comb Fl (Xa.T + (nd X + 4) + nd X + 6) m f (fun q => (hf q).1.1) (by
    rw [show Xa.T + (nd X + 4) + nd X + 6 + nd X = Xa.T + 3 * nd X + 10 by ring]; omega)
  have hg := isBddSec_sum X hf u
  have hg0 : ∃ x ∈ X.dom, ∑ q, u q * f q x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hu (hind u h)
  obtain ⟨k, hk⟩ := exists_s_ne Fl
  have d1 := hg.1.1
  have d2 := Xa.secondTheta_vanishes.1.1.1.1
  have d3 := Xa.firstTheta_vanishes.1.1.1.1
  have d4 := Xa.et_sec.1
  have d5 := (Fl.s_van k).1.1.1.1
  obtain ⟨x, hx, hne⟩ := exists_mul_ne (((d1.mul d2).mul d3).mul d4) d5
    (exists_mul_ne ((d1.mul d2).mul d3) d4 (exists_mul_ne (d1.mul d2) d3
      (exists_mul_ne d1 d2 hg0 Xa.secondTheta_ne_zero) Xa.firstTheta_ne_zero) Xa.et_ne) hk
  simp only [Pi.mul_apply, ne_eq, mul_eq_zero, not_or] at hne
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hne
  obtain ⟨x0, hx0, hs0, hpos, hmax⟩ := mainT E r X Xa Fl (Xa.T + (nd X + 4)) _ (rate_shift Xa) hg hO ⟨x, hx, by
    have p1 := pnorm_pos X (Xa.Fp + (Xa.T + (nd X + 4)) • Xa.L) (P := fun x => ∑ q, u q * f q x) hx h1
    have p2 := pnorm_pos X ((nd X + 4) • Xa.L - Xa.Fp) hx h2
    have p3 := pnorm_pos X (2 • Xa.L - Xa.de) hx h3
    have p4 := pnorm_pos X ((Xa.i * (Xa.g0 / 2)) • Xa.de) hx h4
    have p5 : 0 < ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 :=
      Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨k, Finset.mem_univ _, pow_pos (pnorm_pos X _ hx h5) 2⟩
    positivity⟩
  exact no_pos_maxT E r X Xa Fl _ _ hg.1 x0 hx0 hs0 hpos hmax

end GlobalTheory.UpperShift
