import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BigStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoWeightStatementPfA
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DerivDerivNonposOfIsLocalMax
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LeviLogSumSqFibreZeroAndNonposAtMaxStatement

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.QuotNoMax

theorem exists_dir {n : ℕ} (s : Fin n → V n → ℂ) (k0 : Fin n) (z0 : V n) (hc : ContinuousAt (s k0) z0)
    (h0 : s k0 z0 ≠ 0) :
    ∃ ξ : Fin n → ℂ, ξ ≠ 0 ∧ ∀ k, fderiv ℂ (fun z => s k z / s k0 z) z0 (WithLp.toLp 2 ξ) = 0 := by
  classical

  let L : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    LinearMap.pi fun k => (fderiv ℂ (fun z => s k z / s k0 z) z0).toLinearMap ∘ₗ
      (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm.toLinearMap
  have hL : ∀ ξ k, L ξ k = fderiv ℂ (fun z => s k z / s k0 z) z0 (WithLp.toLp 2 ξ) :=
    fun _ _ => rfl

  have hk0 : ∀ ξ, L ξ k0 = 0 := by
    intro ξ
    rw [hL]
    have hev : (fun z => s k0 z / s k0 z) =ᶠ[𝓝 z0] fun _ => (1 : ℂ) := by
      filter_upwards [hc.eventually_ne h0] with z hz using div_self hz
    rw [hev.fderiv_eq]
    simp

  have hns : ¬ Function.Surjective L := by
    intro hsurj
    obtain ⟨ξ, hξ⟩ := hsurj (Pi.single k0 1)
    have h1 := congrFun hξ k0
    rw [hk0] at h1
    simp at h1
  have hni : ¬ Function.Injective L := fun h => hns (LinearMap.injective_iff_surjective.mp h)
  obtain ⟨a, b, hab, hne⟩ : ∃ a b, L a = L b ∧ a ≠ b := by
    by_contra hcon
    push_neg at hcon
    exact hni fun a b h => hcon a b h
  refine ⟨a - b, sub_ne_zero.mpr hne, fun k => ?_⟩
  have h2 := congrFun (show L (a - b) = 0 by rw [map_sub, hab, sub_self]) k
  rw [hL, Pi.zero_apply] at h2
  exact h2

private theorem contDiffAt_two_log_sum_normSq {n : ℕ} {U : Set (V n)} (hU : IsOpen U) {z0 : V n} (hz : z0 ∈ U) {M : ℕ}
    {w : Fin M → V n → ℂ} (hw : ∀ k, DifferentiableOn ℂ (w k) U)
    (hp : 0 < ∑ k, Complex.normSq (w k z0)) :
    ContDiffAt ℝ 2 (fun z => Real.log (∑ k, Complex.normSq (w k z))) z0 := by
  have h := (OW.sumSq_cdAt hU hw hz).log hp.ne'
  exact_mod_cast contDiffAt_infty.mp h 2

private theorem re_leviV_add {n : ℕ} {f g : V n → ℝ} {x : V n} (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) {ξ : Fin n → ℂ} :
    (leviV n (fun y => ((f y + g y : ℝ) : ℂ)) x ξ).re =
      (leviV n (fun y => (f y : ℂ)) x ξ).re + (leviV n (fun y => (g y : ℂ)) x ξ).re := by
  rw [ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_add hf hg, Complex.add_re]

private theorem exists_pow_mul_mul_mem_subring {n : ℕ} {f : V n → ℝ} {x : V n} (c : ℝ) (hf : ContDiffAt ℝ 2 f x)
    {ξ : Fin n → ℂ} :
    (leviV n (fun y => ((c * f y : ℝ) : ℂ)) x ξ).re = c * (leviV n (fun y => (f y : ℂ)) x ξ).re := by
  rw [ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul c hf, Complex.re_ofReal_mul]

theorem no_localMax {n : ℕ} {U : Set (V n)} (hU : IsOpen U) {z0 : V n} (hz : z0 ∈ U) {a b c d : V n → ℂ}
    (ha : DifferentiableOn ℂ a U) (hb : DifferentiableOn ℂ b U) (hc : DifferentiableOn ℂ c U)
    (hd : DifferentiableOn ℂ d U) (ha0 : a z0 ≠ 0) (hb0 : b z0 ≠ 0) (hc0 : c z0 ≠ 0) (hd0 : d z0 ≠ 0)
    {s : Fin n → V n → ℂ} (hs : ∀ k, DifferentiableOn ℂ (s k) U) {k0 : Fin n} (hs0 : s k0 z0 ≠ 0)
    {φ : V n → ℝ} (hφ : ContDiffAt ℝ 2 φ z0)
    (hpos : ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < (leviV n (fun w => ((φ w : ℝ) : ℂ)) z0 ξ).re) (t e : ℝ) :
    ¬ IsLocalMax (fun z => Real.log (Complex.normSq (a z)) + Real.log (Complex.normSq (b z)) +
      Real.log (Complex.normSq (c z)) + t * Real.log (Complex.normSq (d z)) +
      e * Real.log (∑ k, Complex.normSq (s k z)) + (1 / 2) * φ z) z0 := by
  intro hmax
  have hUz : U ∈ 𝓝 z0 := hU.mem_nhds hz
  have hev : ∀ {f : V n → ℂ}, DifferentiableOn ℂ f U → ∀ᶠ z in 𝓝 z0, DifferentiableAt ℂ f z := by
    intro f hf
    filter_upwards [hUz] with z hzU using hf.differentiableAt (hU.mem_nhds hzU)
  obtain ⟨ξ, hξ0, hξ⟩ := exists_dir s k0 z0 ((hs k0).differentiableAt hUz).continuousAt hs0
  have hT := GlobalTheory.T.levi_log_sum_sq_fibre_zero_and_nonpos_at_max n z0 ξ

  have hone : ∀ {f : V n → ℂ}, DifferentiableOn ℂ f U → f z0 ≠ 0 →
      (leviV n (fun z => ((Real.log (Complex.normSq (f z)) : ℝ) : ℂ)) z0 ξ).re = 0 := by
    intro f hf hf0
    have hq : ∀ _k : Fin 1, fderiv ℂ (fun z => f z / f z) z0 (WithLp.toLp 2 ξ) = 0 := by
      intro _
      have hc1 : (fun z => f z / f z) =ᶠ[𝓝 z0] fun _ => (1 : ℂ) := by
        filter_upwards [((hf.differentiableAt hUz).continuousAt).eventually_ne hf0] with z hz
          using div_self hz
      rw [hc1.fderiv_eq]
      simp
    have h1 := hT.1 1 (fun _ => f) 0 (fun _ => hev hf) hf0 hq
    have heq : (fun z => ((Real.log (Complex.normSq (f z)) : ℝ) : ℂ)) =
        fun z => ((Real.log (∑ k : Fin 1, ‖(fun _ => f) k z‖ ^ 2) : ℝ) : ℂ) := by
      funext z
      rw [Fin.sum_univ_one, Complex.normSq_eq_norm_sq]
    rw [heq]
    exact h1

  have hS : (leviV n (fun z => ((Real.log (∑ k, Complex.normSq (s k z)) : ℝ) : ℂ)) z0 ξ).re = 0 := by
    have h1 := hT.1 n s k0 (fun k => hev (hs k)) hs0 hξ
    have heq : (fun z => ((Real.log (∑ k, Complex.normSq (s k z)) : ℝ) : ℂ)) =
        fun z => ((Real.log (∑ k, ‖s k z‖ ^ 2) : ℝ) : ℂ) := by
      funext z
      simp only [Complex.normSq_eq_norm_sq]
    rw [heq]
    exact h1

  have cone : ∀ {f : V n → ℂ}, DifferentiableOn ℂ f U → f z0 ≠ 0 →
      ContDiffAt ℝ 2 (fun z => Real.log (Complex.normSq (f z))) z0 := by
    intro f hf hf0
    have h := contDiffAt_two_log_sum_normSq hU hz (w := fun _ : Fin 1 => f) (fun _ => hf)
      (by simpa using Complex.normSq_pos.mpr hf0)
    simpa using h
  have hsp : 0 < ∑ k, Complex.normSq (s k z0) :=
    lt_of_lt_of_le (Complex.normSq_pos.mpr hs0)
      (Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (s k z0)) (Finset.mem_univ k0))
  have cA := cone ha ha0
  have cB := cone hb hb0
  have cC := cone hc hc0
  have cD := cone hd hd0
  have cS := contDiffAt_two_log_sum_normSq hU hz hs hsp
  have cDt : ContDiffAt ℝ 2 (fun z => t * Real.log (Complex.normSq (d z))) z0 :=
    contDiffAt_const.mul cD
  have cSe : ContDiffAt ℝ 2 (fun z => e * Real.log (∑ k, Complex.normSq (s k z))) z0 :=
    contDiffAt_const.mul cS
  have cH : ContDiffAt ℝ 2 (fun z => (1 / 2 : ℝ) * φ z) z0 := contDiffAt_const.mul hφ
  have cF := ((((cA.add cB).add cC).add cDt).add cSe).add cH
  have hle := hT.2 _ cF hmax
  rw [re_leviV_add ((((cA.add cB).add cC).add cDt).add cSe) cH,
    re_leviV_add (((cA.add cB).add cC).add cDt) cSe,
    re_leviV_add ((cA.add cB).add cC) cDt,
    re_leviV_add (cA.add cB) cC, re_leviV_add cA cB,
    exists_pow_mul_mul_mem_subring t cD, exists_pow_mul_mul_mem_subring e cS, exists_pow_mul_mul_mem_subring (1 / 2) hφ,
    hone ha ha0, hone hb hb0, hone hc hc0, hone hd hd0, hS] at hle
  have hp := hpos ξ hξ0
  linarith

private theorem logq_lemma_4 {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (Xa : ArchInM X) (Fl : FlatM X Xa) (f : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hf : f x ≠ 0) (h2 : Xa.th2 x ≠ 0) (h1 : Xa.th1 x ≠ 0) (he : Xa.et x ≠ 0)
    (hs : 0 < ∑ k, Complex.normSq (Fl.s k x)) :
    0 < X.pnorm (Xa.Fp + Xa.T • Xa.L) f x ^ 2 * X.pnorm ((nd X + 4) • Xa.L - Xa.Fp) Xa.th2 x ^ 2 *
      X.pnorm (2 • Xa.L - Xa.de) Xa.th1 x ^ 2 *
      (X.pnorm ((Xa.i * (Xa.g0 / 2)) • Xa.de) Xa.et x ^ 2) ^ ((1 : ℝ) / (Xa.i * (Xa.g0 / 2) : ℕ)) /
      (∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) ^ ((Xa.T : ℝ) + nd X + 6 + 1 / 2) ∧
    Real.log (X.pnorm (Xa.Fp + Xa.T • Xa.L) f x ^ 2 * X.pnorm ((nd X + 4) • Xa.L - Xa.Fp) Xa.th2 x ^ 2 *
      X.pnorm (2 • Xa.L - Xa.de) Xa.th1 x ^ 2 *
      (X.pnorm ((Xa.i * (Xa.g0 / 2)) • Xa.de) Xa.et x ^ 2) ^ ((1 : ℝ) / (Xa.i * (Xa.g0 / 2) : ℕ)) /
      (∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) ^ ((Xa.T : ℝ) + nd X + 6 + 1 / 2)) =
      Real.log (Complex.normSq (f x)) + Real.log (Complex.normSq (Xa.th2 x)) +
      Real.log (Complex.normSq (Xa.th1 x)) +
      ((1 : ℝ) / (Xa.i * (Xa.g0 / 2) : ℕ)) * Real.log (Complex.normSq (Xa.et x)) +
      (-((Xa.T : ℝ) + nd X + 6 + 1 / 2)) * Real.log (∑ k, Complex.normSq (Fl.s k x)) +
      (1 / 2) * phla X Xa.L x := by
  have hm : 0 < Xa.i * (Xa.g0 / 2) := by
    obtain ⟨k, hk⟩ := Xa.genus_even
    have := Xa.genus_pos
    have := Xa.i_pos
    exact Nat.mul_pos (by omega) (by omega)
  have hmR : ((Xa.i * (Xa.g0 / 2) : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [OW.pnorm_sq X _ f hx, OW.pnorm_sq X _ Xa.th2 hx, OW.pnorm_sq X _ Xa.th1 hx,
    OW.pnorm_sq X _ Xa.et hx, OW.sum_pnorm_sq X _ Fl.s hx]
  have pf := Complex.normSq_pos.mpr hf
  have p2 := Complex.normSq_pos.mpr h2
  have p1 := Complex.normSq_pos.mpr h1
  have pe := Complex.normSq_pos.mpr he
  refine ⟨by positivity, ?_⟩
  rw [Real.log_div, Real.log_rpow, Real.log_mul, Real.log_rpow, Real.log_mul, Real.log_mul,
    Real.log_mul, Real.log_mul, Real.log_mul, Real.log_mul, Real.log_mul]
  · simp only [Real.log_exp]
    rw [OW.phla_add_nsmul X hx, BigC.phla_sub X hx, BigC.phla_sub X hx, BigC.phla_nsmul X hx,
      BigC.phla_nsmul X hx, BigC.phla_nsmul X hx]
    field_simp
    push_cast
    ring
  all_goals positivity

private theorem contDiffAt_two_phla_cpt {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (la : Wt X.Ψ r) (x0 : Frame X.Ψ r) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    ContDiffAt ℝ 2 (fun w => phla X la (cpt X x0 w)) z := by
  have hO := (OntoB.isOpen_OmF X x0).mem_nhds hz
  have hlog : ∀ τ (i : Fin (r + 1)), ContDiffAt ℝ 2
      (fun w => Real.log ‖dmin X.Gm (cpt X x0 w) τ i‖) z := by
    intro τ i
    have hd : ContDiffAt ℝ 2 (fun w => dmin X.Gm (cpt X x0 w) τ i) z := by
      exact_mod_cast contDiffAt_infty.mp ((OntoB.cd_dmin X x0 τ i).contDiffAt) 2
    exact (hd.norm ℝ (OntoB.dmin_ne hz τ i)).log (norm_ne_zero_iff.mpr (OntoB.dmin_ne hz τ i))
  have hsum : ContDiffAt ℝ 2 (fun w => ∑ τ, ∑ i : Fin r, (la τ i : ℝ) *
      (Real.log ‖dmin X.Gm (cpt X x0 w) τ i.succ‖ -
        Real.log ‖dmin X.Gm (cpt X x0 w) τ i.castSucc‖)) z := by
    refine ContDiffAt.sum fun τ _ => ContDiffAt.sum fun i _ => ?_
    exact contDiffAt_const.mul ((hlog τ i.succ).sub (hlog τ i.castSucc))
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [hO] with w hw
  have hne : ∀ τ (i : Fin (r + 1)), dmin X.Gm (cpt X x0 w) τ i ≠ 0 :=
    fun τ i => OntoB.dmin_ne hw τ i
  have hq : ∀ τ (i : Fin r), 0 < ‖dmin X.Gm (cpt X x0 w) τ i.succ / dmin X.Gm (cpt X x0 w) τ i.castSucc‖ :=
    fun τ i => norm_pos_iff.mpr (div_ne_zero (hne _ _) (hne _ _))
  simp only [phla, Data.nfac]
  rw [Real.log_prod (fun τ _ => (Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hq τ i) _).ne'),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Real.log_prod (fun i _ => (Real.rpow_pos_of_pos (hq τ i) _).ne'), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.log_rpow (hq τ i), norm_div,
    Real.log_div (norm_ne_zero_iff.mpr (hne _ _)) (norm_ne_zero_iff.mpr (hne _ _))]
  ring

theorem no_pos_max : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (f : Frame X.Ψ r → ℂ), X.IsSec (Xa.Fp + Xa.T • Xa.L) f → let Φ : Frame X.Ψ r → ℝ := fun x => X.pnorm (Xa.Fp + Xa.T • Xa.L) f x ^ 2 * X.pnorm ((nd X + 4) • Xa.L - Xa.Fp) Xa.th2 x ^ 2 * X.pnorm (2 • Xa.L - Xa.de) Xa.th1 x ^ 2 * (X.pnorm ((Xa.i * (Xa.g0 / 2)) • Xa.de) Xa.et x ^ 2) ^ ((1 : ℝ) / (Xa.i * (Xa.g0 / 2) : ℕ)) / (∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) ^ ((Xa.T : ℝ) + nd X + 6 + 1 / 2); ∀ x0 ∈ X.dom, (∃ k, Fl.s k x0 ≠ 0) → 0 < Φ x0 → ¬ ∀ x ∈ X.dom, Φ x ≤ Φ x0 := by
  intro E _ _ _ r X Xa Fl f hf Φ x0 hx0 hk hΦ hmax
  obtain ⟨k0, hk0⟩ := hk
  have hU := OntoB.isOpen_OmF X x0
  have h0U : (0 : V (nd X)) ∈ OmF X x0 := by
    show cpt X x0 0 ∈ X.dom
    rw [DivLC.cpt_zero']
    exact hx0
  have d2 : DifferentiableOn ℂ Xa.th2 X.dom := Xa.secondTheta_vanishes.1.1.1.1
  have d1 : DifferentiableOn ℂ Xa.th1 X.dom := Xa.firstTheta_vanishes.1.1.1.1
  have de : DifferentiableOn ℂ Xa.et X.dom := Xa.et_sec.1
  have ha := OntoB.hol_comp X x0 hf.1
  have hb := OntoB.hol_comp X x0 d2
  have hc := OntoB.hol_comp X x0 d1
  have hd := OntoB.hol_comp X x0 de
  have hs : ∀ k, DifferentiableOn ℂ (fun z => Fl.s k (cpt X x0 z)) (OmF X x0) :=
    fun k => OntoB.hol_comp X x0 (OW.s_diffOn Fl k)

  have hi : Xa.i ≠ 0 := by have := Xa.i_pos; omega
  have hg : Xa.g0 / 2 ≠ 0 := by
    obtain ⟨k, hk⟩ := Xa.genus_even
    have := Xa.genus_pos
    omega
  have hΦ' : 0 < X.pnorm (Xa.Fp + Xa.T • Xa.L) f x0 ^ 2 * X.pnorm ((nd X + 4) • Xa.L - Xa.Fp) Xa.th2 x0 ^ 2 *
      X.pnorm (2 • Xa.L - Xa.de) Xa.th1 x0 ^ 2 *
      (X.pnorm ((Xa.i * (Xa.g0 / 2)) • Xa.de) Xa.et x0 ^ 2) ^ ((1 : ℝ) / (Xa.i * (Xa.g0 / 2) : ℕ)) /
      (∑ k, X.pnorm Xa.L (Fl.s k) x0 ^ 2) ^ ((Xa.T : ℝ) + nd X + 6 + 1 / 2) := hΦ
  have hf0 : f x0 ≠ 0 := by
    intro h0
    have hp : X.pnorm (Xa.Fp + Xa.T • Xa.L) f x0 = 0 := by rw [OW.pnorm_eq, h0, norm_zero, zero_mul]
    rw [hp] at hΦ'
    simp at hΦ'
  have h20 : Xa.th2 x0 ≠ 0 := by
    intro h0
    have hp : X.pnorm ((nd X + 4) • Xa.L - Xa.Fp) Xa.th2 x0 = 0 := by
      rw [OW.pnorm_eq, h0, norm_zero, zero_mul]
    rw [hp] at hΦ'
    simp at hΦ'
  have h10 : Xa.th1 x0 ≠ 0 := by
    intro h0
    have hp : X.pnorm (2 • Xa.L - Xa.de) Xa.th1 x0 = 0 := by rw [OW.pnorm_eq, h0, norm_zero, zero_mul]
    rw [hp] at hΦ'
    simp at hΦ'
  have he0 : Xa.et x0 ≠ 0 := by
    intro h0
    have hp : X.pnorm ((Xa.i * (Xa.g0 / 2)) • Xa.de) Xa.et x0 = 0 := by
      rw [OW.pnorm_eq, h0, norm_zero, zero_mul]
    rw [hp] at hΦ'
    simp [hi, hg] at hΦ'

  have cont : ∀ {g : Frame X.Ψ r → ℂ}, DifferentiableOn ℂ (fun z => g (cpt X x0 z)) (OmF X x0) →
      g x0 ≠ 0 → ∀ᶠ z in 𝓝 (0 : V (nd X)), g (cpt X x0 z) ≠ 0 := by
    intro g hg' hg0
    exact (hg'.continuousOn.continuousAt (hU.mem_nhds h0U)).eventually_ne
      (by simpa only [DivLC.cpt_zero'] using hg0)
  have hev : ∀ᶠ z in 𝓝 (0 : V (nd X)), cpt X x0 z ∈ X.dom ∧ f (cpt X x0 z) ≠ 0 ∧
      Xa.th2 (cpt X x0 z) ≠ 0 ∧ Xa.th1 (cpt X x0 z) ≠ 0 ∧ Xa.et (cpt X x0 z) ≠ 0 ∧
      Fl.s k0 (cpt X x0 z) ≠ 0 := by
    filter_upwards [hU.mem_nhds h0U, cont ha hf0, cont hb h20, cont hc h10, cont hd he0,
      cont (hs k0) hk0] with z h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  have hl0 := (logq_lemma_4 X Xa Fl f hx0 hf0 h20 h10 he0 (OW.sums_pos Fl hk0)).2

  have hLM : IsLocalMax (fun z => Real.log (Complex.normSq (f (cpt X x0 z))) +
      Real.log (Complex.normSq (Xa.th2 (cpt X x0 z))) + Real.log (Complex.normSq (Xa.th1 (cpt X x0 z))) +
      ((1 : ℝ) / (Xa.i * (Xa.g0 / 2) : ℕ)) * Real.log (Complex.normSq (Xa.et (cpt X x0 z))) +
      (-((Xa.T : ℝ) + nd X + 6 + 1 / 2)) * Real.log (∑ k, Complex.normSq (Fl.s k (cpt X x0 z))) +
      (1 / 2) * phla X Xa.L (cpt X x0 z)) 0 := by
    refine Filter.Eventually.mono hev ?_
    rintro z ⟨hzd, h2, h3, h4, h5, h6⟩
    obtain ⟨hpz, hlz⟩ := logq_lemma_4 X Xa Fl f hzd h2 h3 h4 h5 (OW.sums_pos Fl h6)
    have hle : Real.log (X.pnorm (Xa.Fp + Xa.T • Xa.L) f (cpt X x0 z) ^ 2 * X.pnorm ((nd X + 4) • Xa.L - Xa.Fp) Xa.th2 (cpt X x0 z) ^ 2 *
      X.pnorm (2 • Xa.L - Xa.de) Xa.th1 (cpt X x0 z) ^ 2 *
      (X.pnorm ((Xa.i * (Xa.g0 / 2)) • Xa.de) Xa.et (cpt X x0 z) ^ 2) ^ ((1 : ℝ) / (Xa.i * (Xa.g0 / 2) : ℕ)) /
      (∑ k, X.pnorm Xa.L (Fl.s k) (cpt X x0 z) ^ 2) ^ ((Xa.T : ℝ) + nd X + 6 + 1 / 2)) ≤ Real.log (X.pnorm (Xa.Fp + Xa.T • Xa.L) f x0 ^ 2 * X.pnorm ((nd X + 4) • Xa.L - Xa.Fp) Xa.th2 x0 ^ 2 *
      X.pnorm (2 • Xa.L - Xa.de) Xa.th1 x0 ^ 2 *
      (X.pnorm ((Xa.i * (Xa.g0 / 2)) • Xa.de) Xa.et x0 ^ 2) ^ ((1 : ℝ) / (Xa.i * (Xa.g0 / 2) : ℕ)) /
      (∑ k, X.pnorm Xa.L (Fl.s k) x0 ^ 2) ^ ((Xa.T : ℝ) + nd X + 6 + 1 / 2)) :=
      Real.log_le_log hpz (hmax _ hzd)
    simp only [DivLC.cpt_zero']
    linarith
  exact no_localMax hU h0U ha hb hc hd (by simpa only [DivLC.cpt_zero'] using hf0)
    (by simpa only [DivLC.cpt_zero'] using h20) (by simpa only [DivLC.cpt_zero'] using h10)
    (by simpa only [DivLC.cpt_zero'] using he0) hs (k0 := k0)
    (by simpa only [DivLC.cpt_zero'] using hk0) (contDiffAt_two_phla_cpt X Xa.L x0 h0U)
    (fun ξ hξ => Xa.posL x0 hx0 0 h0U ξ hξ) _ _ hLM

end GlobalTheory.QuotNoMax
