import Formalism.HermitianCurvature.StatementMA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateCommuteRaisingConstant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WordStatementsAllHold
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleRecOfAdmissibleWord
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InterlaceSignTwo
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Interlace
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DerivedCoefficientIntegrable

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx2.R2
open Formalism.FourierDecayAlt.MA

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.MAx1.An MeasureTheory
open scoped ComplexConjugate

noncomputable section

variable {τ : ℝ}

abbrev S (τ : ℝ) := SmQ 0 τ
def z : S τ := coordQ M.vz
def zb : S τ := coordQ M.vzb
def zi : S τ := Ring.inverse z
def zbi : S τ := Ring.inverse zb
def gg : S τ := (anQ 0 τ).gg τ
def ggi : S τ := Ring.inverse gg
def th : Module.End ℂ (S τ) := eulerQ M.vz
def thb : Module.End ℂ (S τ) := eulerQ M.vzb

def ev (f : S τ) (q : Qp 0 τ) : ℂ := f.1 q

@[simp] theorem ev_mul (f g : S τ) (q) : ev (f * g) q = ev f q * ev g q := rfl
@[simp] theorem ev_add (f g : S τ) (q) : ev (f + g) q = ev f q + ev g q := rfl
@[simp] theorem ev_sub (f g : S τ) (q) : ev (f - g) q = ev f q - ev g q := rfl
@[simp] theorem ev_neg (f : S τ) (q) : ev (-f) q = -ev f q := rfl
@[simp] theorem ev_smul (c : ℂ) (f : S τ) (q) : ev (c • f) q = c * ev f q := rfl
@[simp] theorem ev_one (q) : ev (1 : S τ) q = 1 := rfl
@[simp] theorem ev_zero (q) : ev (0 : S τ) q = 0 := rfl
theorem S_ext {f g : S τ} (h : ∀ q, ev f q = ev g q) : f = g := Subtype.ext (funext h)

theorem eval_zeta (q) : ev (z : S τ) q = q.1.2 := coordE_vz q.1
theorem ev_zb (q) : ev (zb : S τ) q = conj q.1.2 := coordE_vzb q.1
theorem ev_gg (q) : ev (gg : S τ) q = q.1.2 * conj q.1.2 - τ := by
  have := gg_apply (r := 0) (TT := τ) q
  rw [coordE_vz, coordE_vzb] at this
  exact this

theorem laws (hτ : 1 ≤ τ) : (anQ 0 τ).Laws τ := Formalism.FourierDecayAlt.P.analytic_laws 0 τ (by linarith)

theorem one_le (hτ : 1 ≤ τ) (q : Qp 0 τ) : 1 ≤ ‖q.1.2‖ := by
  have h : τ < Complex.normSq q.1.2 := q.2.2
  rw [Complex.normSq_eq_norm_sq] at h
  by_contra h1
  push Not at h1
  nlinarith [norm_nonneg q.1.2]

theorem z_ne (hτ : 1 ≤ τ) (q : Qp 0 τ) : q.1.2 ≠ 0 := by
  intro h; have := one_le hτ q; rw [h] at this; norm_num at this

theorem ev_inv (f : S τ) (hf : IsUnit f) (q) : ev (Ring.inverse f) q = (ev f q)⁻¹ := by
  have h : ev (f * Ring.inverse f) q = 1 := by rw [Ring.mul_inverse_cancel f hf]; rfl
  rw [ev_mul] at h
  exact (eq_inv_of_mul_eq_one_right h)

theorem ev_zi (hτ : 1 ≤ τ) (q) : ev (zi : S τ) q = (q.1.2)⁻¹ := by
  rw [zi, ev_inv z ((laws hτ).unit_alt_bis M.vz), eval_zeta]
theorem ev_zbi (hτ : 1 ≤ τ) (q) : ev (zbi : S τ) q = (conj q.1.2)⁻¹ := by
  rw [zbi, ev_inv zb ((laws hτ).unit_alt_bis M.vzb), ev_zb]
theorem ev_ggi (hτ : 1 ≤ τ) (q) : ev (ggi : S τ) q = (q.1.2 * conj q.1.2 - τ)⁻¹ := by
  rw [ggi, ev_inv gg (laws hτ).unit_gg, ev_gg]
theorem gg_ne' (q : Qp 0 τ) : q.1.2 * conj q.1.2 - τ ≠ 0 := by
  rw [← ev_gg]; exact gg_ne (r := 0) (TT := τ) q

theorem th_mul (f g : S τ) : th (f * g) = th f * g + f * th g := Formalism.FourierDecayAlt.P.analytic_leibniz 0 τ _ f g
theorem thb_mul (f g : S τ) : thb (f * g) = thb f * g + f * thb g := Formalism.FourierDecayAlt.P.analytic_leibniz 0 τ _ f g
theorem theta_zeta : th (z : S τ) = z := by
  have := Formalism.FourierDecayAlt.P.analytic_coordinates 0 τ M.vz M.vz; rwa [if_pos rfl] at this
theorem th_zb : th (zb : S τ) = 0 := by
  have := Formalism.FourierDecayAlt.P.analytic_coordinates 0 τ M.vz M.vzb; rwa [if_neg Formalism.FourierDecayAlt.P.MAx1.vz_ne] at this
theorem theta_bar_zeta : thb (z : S τ) = 0 := by
  have := Formalism.FourierDecayAlt.P.analytic_coordinates 0 τ M.vzb M.vz; rwa [if_neg Formalism.FourierDecayAlt.P.MAx1.vz_ne.symm] at this
theorem thb_zb : thb (zb : S τ) = zb := by
  have := Formalism.FourierDecayAlt.P.analytic_coordinates 0 τ M.vzb M.vzb; rwa [if_pos rfl] at this
theorem th_zi (hτ : 1 ≤ τ) : th (zi : S τ) = -zi := by
  have := Formalism.FourierDecayAlt.P.MAx1.eci (laws hτ) M.vz M.vz; rwa [if_pos rfl] at this
theorem th_zbi (hτ : 1 ≤ τ) : th (zbi : S τ) = 0 := by
  have := Formalism.FourierDecayAlt.P.MAx1.eci (laws hτ) M.vz M.vzb; rwa [if_neg Formalism.FourierDecayAlt.P.MAx1.vz_ne] at this
theorem thb_zi (hτ : 1 ≤ τ) : thb (zi : S τ) = 0 := by
  have := Formalism.FourierDecayAlt.P.MAx1.eci (laws hτ) M.vzb M.vz; rwa [if_neg Formalism.FourierDecayAlt.P.MAx1.vz_ne.symm] at this
theorem thb_zbi (hτ : 1 ≤ τ) : thb (zbi : S τ) = -zbi := by
  have := Formalism.FourierDecayAlt.P.MAx1.eci (laws hτ) M.vzb M.vzb; rwa [if_pos rfl] at this
theorem th_gg (hτ : 1 ≤ τ) : th (gg : S τ) = z * zb := Formalism.FourierDecayAlt.P.MAx1.euler_GG_z (laws hτ)
theorem thb_gg (hτ : 1 ≤ τ) : thb (gg : S τ) = z * zb := Formalism.FourierDecayAlt.P.MAx1.euler_gg_zb (laws hτ)
theorem thb_ggi (hτ : 1 ≤ τ) : thb (ggi : S τ) = -(ggi * ggi * (z * zb)) := by
  rw [← thb_gg hτ]; exact Formalism.FourierDecayAlt.P.MAx1.ev_inv (laws hτ) M.vzb gg (laws hτ).unit_gg
theorem th_one (hτ : 1 ≤ τ) : th (1 : S τ) = 0 := Formalism.FourierDecayAlt.P.MAx1.ev_one (laws hτ) M.vz
theorem thb_one (hτ : 1 ≤ τ) : thb (1 : S τ) = 0 := Formalism.FourierDecayAlt.P.MAx1.ev_one (laws hτ) M.vzb

theorem ext_conj (f : Qp 0 τ → ℂ) : ext (fun q => conj (f q)) = fun x => Complex.conjCLE (ext f x) := by
  funext x; by_cases hx : x ∈ Qset 0 τ <;> simp [ext, hx]

def cj (f : S τ) : S τ := ⟨fun q => conj (f.1 q), by
  show ContDiffOn ℝ sm (ext fun q => conj (f.1 q)) (Qset 0 τ)
  rw [ext_conj]
  exact Complex.conjCLE.contDiff.comp_contDiffOn f.2⟩

@[simp] theorem ev_cj (f : S τ) (q) : ev (cj f) q = conj (ev f q) := rfl

theorem direction_zeta : dirE (M.vz : M.Var 0) = (0, 1) := by simp [dirE, M.vz]
theorem dir_zb : dirE (M.vzb : M.Var 0) = (0, 1) := by simp [dirE, M.vzb]

theorem wirt_alt (F : E 0 → ℂ) (x) : wirt M.vz F x =
    (1 / 2 : ℂ) * (fderiv ℝ F x (0, 1) - Complex.I * fderiv ℝ F x (Complex.I • ((0, 1) : E 0))) := by
  rw [wirt, direction_zeta, if_pos (by simp [M.vz])]; ring
theorem wirt_zb (F : E 0 → ℂ) (x) : wirt M.vzb F x =
    (1 / 2 : ℂ) * (fderiv ℝ F x (0, 1) + Complex.I * fderiv ℝ F x (Complex.I • ((0, 1) : E 0))) := by
  rw [wirt, dir_zb, if_neg (by simp [M.vzb])]

theorem ev_th (f : S τ) (q) : ev (th f) q = q.1.2 * wirt M.vz (ext f.1) q.1 := by
  rw [← coordE_vz]; rfl
theorem ev_thb (f : S τ) (q) : ev (thb f) q = conj q.1.2 * wirt M.vzb (ext f.1) q.1 := by
  rw [← coordE_vzb]; rfl

theorem fd_conj (f : S τ) (q : Qp 0 τ) (e : E 0) :
    fderiv ℝ (ext (cj f).1) q.1 e = conj (fderiv ℝ (ext f.1) q.1 e) := by
  have : ext (cj f).1 = Complex.conjCLE ∘ ext f.1 := ext_conj f.1
  rw [this, ContinuousLinearEquiv.comp_fderiv]
  simp

theorem th_cj (f : S τ) : th (cj f) = cj (thb f) := S_ext fun q => by
  rw [ev_cj, ev_th, ev_thb, wirt_alt, wirt_zb, fd_conj, fd_conj]
  simp only [map_mul, map_add, Complex.conj_conj, Complex.conj_I, map_div₀, map_one, map_ofNat]
  ring
theorem thb_cj (f : S τ) : thb (cj f) = cj (th f) := S_ext fun q => by
  rw [ev_cj, ev_th, ev_thb, wirt_alt, wirt_zb, fd_conj, fd_conj]
  simp only [map_mul, map_sub, Complex.conj_conj, Complex.conj_I, map_div₀, map_one, map_ofNat]
  ring

def Bd (K : ℤ) (f : S τ) : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ q, ‖ev f q‖ ≤ C * ‖q.1.2‖ ^ K

theorem Bd.add {K} {f g : S τ} (hf : Bd K f) (hg : Bd K g) : Bd K (f + g) := by
  obtain ⟨C, hC, h⟩ := hf; obtain ⟨C', hC', h'⟩ := hg
  exact ⟨C + C', by positivity, fun q => by
    rw [ev_add, add_mul]; exact (norm_add_le _ _).trans (add_le_add (h q) (h' q))⟩
theorem Bd.smul {K} {f : S τ} (c : ℂ) (hf : Bd K f) : Bd K (c • f) := by
  obtain ⟨C, hC, h⟩ := hf
  exact ⟨‖c‖ * C, by positivity, fun q => by
    rw [ev_smul, norm_mul, mul_assoc]; exact mul_le_mul_of_nonneg_left (h q) (norm_nonneg _)⟩
theorem Bd.neg {K} {f : S τ} (hf : Bd K f) : Bd K (-f) := by
  have := hf.smul (-1); rwa [neg_one_smul] at this
theorem Bd.sub {K} {f g : S τ} (hf : Bd K f) (hg : Bd K g) : Bd K (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg
theorem Bd.mul (hτ : 1 ≤ τ) {K K'} {f g : S τ} (hf : Bd K f) (hg : Bd K' g) : Bd (K + K') (f * g) := by
  obtain ⟨C, hC, h⟩ := hf; obtain ⟨C', hC', h'⟩ := hg
  refine ⟨C * C', by positivity, fun q => ?_⟩
  have h0 : ‖q.1.2‖ ≠ 0 := by have := one_le hτ q; positivity
  rw [ev_mul, norm_mul, zpow_add₀ h0]
  calc _ ≤ (C * ‖q.1.2‖ ^ K) * (C' * ‖q.1.2‖ ^ K') := mul_le_mul (h q) (h' q) (norm_nonneg _) (by positivity)
    _ = _ := by ring
theorem Bd.mono (hτ : 1 ≤ τ) {K K'} {f : S τ} (hf : Bd K f) (hK : K ≤ K') : Bd K' f := by
  obtain ⟨C, hC, h⟩ := hf
  exact ⟨C, hC, fun q => (h q).trans (mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (one_le hτ q) hK) hC)⟩
theorem Bd.cj {K} {f : S τ} (hf : Bd K f) : Bd K (cj f) := by
  obtain ⟨C, hC, h⟩ := hf
  exact ⟨C, hC, fun q => by rw [ev_cj, Complex.norm_conj]; exact h q⟩
theorem bd_zero (K) : Bd K (0 : S τ) := ⟨0, le_rfl, fun q => by simp⟩
theorem bd_one : Bd 0 (1 : S τ) := ⟨1, zero_le_one, fun q => by simp⟩
theorem bounded_zeta : Bd 1 (z : S τ) := ⟨1, zero_le_one, fun q => by simp [eval_zeta]⟩
theorem bd_zb : Bd 1 (zb : S τ) := ⟨1, zero_le_one, fun q => by simp [ev_zb]⟩
theorem bd_zi (hτ : 1 ≤ τ) : Bd (-1) (zi : S τ) := ⟨1, zero_le_one, fun q => by simp [ev_zi hτ]⟩
theorem bd_zbi (hτ : 1 ≤ τ) : Bd (-1) (zbi : S τ) := ⟨1, zero_le_one, fun q => by simp [ev_zbi hτ]⟩

instance haarE : (volume : Measure (E 0)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure (volume : Measure (Fin 0 → ℂ)) (volume : Measure ℂ)

theorem ringSpec_normalisedCharacter_eq : mu0 0 τ = Measure.comap Subtype.val (volume : Measure (E 0)) := by
  have : (dens0 : E 0 → ENNReal) = 1 := by funext x; simp [dens0]
  rw [mu0, this, withDensity_one]

theorem ext_val (f : Qp 0 τ → ℂ) (q : Qp 0 τ) : ext f q.1 = f q := ext_of_mem f q.2

theorem int_ext (f : S τ) : ∫ q, ev f q ∂mu0 0 τ = ∫ x, ext f.1 x := by
  rw [ringSpec_normalisedCharacter_eq, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Qset 0 τ) (fun x hx => by simp [ext, hx]),
    ← integral_subtype_comap (Qset_open 0 τ).measurableSet]
  congr 1; funext q; exact (ext_val _ q).symm

theorem integrable_ext (hτ : 1 ≤ τ) {f : S τ} (hf : Bd (-3) f) : Integrable (ext f.1) := by
  obtain ⟨C, hC, h⟩ := hf
  have hm : AEStronglyMeasurable (ext f.1) (volume : Measure (E 0)) := by
    have : ext f.1 = (Qset 0 τ).indicator (ext f.1) := by
      funext x; by_cases hx : x ∈ Qset 0 τ <;> simp [ext, hx]
    rw [this, aestronglyMeasurable_indicator_iff (Qset_open 0 τ).measurableSet]
    exact (f.2 : ContDiffOn ℝ sm (ext f.1) _).continuousOn.aestronglyMeasurable (Qset_open 0 τ).measurableSet
  have hi : Integrable (fun x : E 0 => (1 + ‖x‖) ^ (-(3 : ℝ))) := integrable_one_add_norm (by
    simp [Module.finrank_prod, Module.finrank_pi_fintype]; norm_num)
  refine (hi.const_mul (8 * C)).mono' hm (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ Qset 0 τ
  · rw [ext_of_mem _ hx]
    refine (h ⟨x, hx⟩).trans ?_
    have h1 : 1 ≤ ‖x.2‖ := one_le hτ ⟨x, hx⟩
    have h2 : ‖x‖ = ‖x.2‖ := by
      rw [Prod.norm_def, Subsingleton.elim x.1 0, norm_zero, max_eq_right (norm_nonneg _)]
    rw [h2, show (-(3 : ℝ)) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    show C * ‖x.2‖ ^ (-3 : ℤ) ≤ 8 * C * (1 + ‖x.2‖) ^ (-3 : ℤ)
    have h3 : ‖x.2‖ ^ (-3 : ℤ) ≤ 8 * (1 + ‖x.2‖) ^ (-3 : ℤ) := by
      rw [zpow_neg, zpow_neg, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have : (1 + ‖x.2‖) ^ 3 ≤ (2 * ‖x.2‖) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
      norm_cast
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h3 hC]
  · simp only [ext, hx, dif_neg, not_false_eq_true, norm_zero]; positivity

theorem integrable_ev (hτ : 1 ≤ τ) {f : S τ} (hf : Bd (-3) f) : Integrable (ev f) (mu0 0 τ) := by
  have := (integrableOn_iff_comap_subtypeVal (Qset_open 0 τ).measurableSet).1
    ((integrable_ext hτ hf).integrableOn (s := Qset 0 τ))
  rw [ringSpec_normalisedCharacter_eq]
  refine this.congr (Filter.Eventually.of_forall fun q => ext_val _ q)

theorem ev_zero_near {h : S τ} {ε : ℝ} (hε : 0 < ε) (h0 : ∀ q : Qp 0 τ, Complex.normSq q.1.2 - τ ≤ ε → ev h q = 0)
    {x : E 0} (hx : x ∉ Qset 0 τ) : ext h.1 =ᶠ[nhds x] fun _ => 0 := by
  have hx' : Complex.normSq x.2 - τ < ε := by
    have : ¬ τ < Complex.normSq x.2 := fun h' => hx ⟨fun l => l.elim0, h'⟩
    linarith [not_lt.1 this]
  have ho : IsOpen {y : E 0 | Complex.normSq y.2 - τ < ε} :=
    isOpen_lt ((Complex.continuous_normSq.comp continuous_snd).sub continuous_const) continuous_const
  filter_upwards [ho.mem_nhds hx'] with y hy
  by_cases hy' : y ∈ Qset 0 τ
  · rw [ext_of_mem _ hy']; exact h0 ⟨y, hy'⟩ (le_of_lt hy)
  · simp [ext, hy']

theorem ibp (hτ : 1 ≤ τ) {h : S τ} {ε : ℝ} (hε : 0 < ε)
    (h0 : ∀ q : Qp 0 τ, Complex.normSq q.1.2 - τ ≤ ε → ev h q = 0)
    (b0 : Bd (-3) h) (b1 : Bd (-3) (th h)) (b2 : Bd (-3) (thb h)) :
    ∫ q, ev (zi * th h) q ∂mu0 0 τ = 0 ∧ ∫ q, ev (zbi * thb h) q ∂mu0 0 τ = 0 := by
  have hd : ∀ x, DifferentiableAt ℝ (ext h.1) x := fun x => by
    by_cases hx : x ∈ Qset 0 τ
    · exact ext_smooth_diff h.2 x hx
    · exact (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq (ev_zero_near hε h0 hx)
  have a1 : Bd (-3) (zi * th h) := (Bd.mul hτ (bd_zi hτ) b1).mono hτ (by norm_num)
  have a2 : Bd (-3) (zbi * thb h) := (Bd.mul hτ (bd_zbi hτ) b2).mono hτ (by norm_num)
  have e1 : ∀ q : Qp 0 τ, ev (zi * th h) q = wirt M.vz (ext h.1) q.1 := fun q => by
    rw [ev_mul, ev_zi hτ, ev_th, inv_mul_cancel_left₀ (z_ne hτ q)]
  have e2 : ∀ q : Qp 0 τ, ev (zbi * thb h) q = wirt M.vzb (ext h.1) q.1 := fun q => by
    rw [ev_mul, ev_zbi hτ, ev_thb, inv_mul_cancel_left₀ ((map_ne_zero _).2 (z_ne hτ q))]
  have key : ∀ (g : S τ) (e : E 0), Bd (-3) g → (∀ q : Qp 0 τ, ev g q = fderiv ℝ (ext h.1) q.1 e) →
      ∫ q, ev g q ∂mu0 0 τ = 0 := by
    intro g e hg hge
    have hfe : (fun x => fderiv ℝ (ext h.1) x e) = ext g.1 := by
      funext x
      by_cases hx : x ∈ Qset 0 τ
      · rw [ext_of_mem _ hx]; exact (hge ⟨x, hx⟩).symm
      · rw [(ev_zero_near hε h0 hx).fderiv_eq]; simp [ext, hx]
    have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (E 0)))
      (f := fun _ => (1 : ℂ)) (g := ext h.1) (v := e) (by simp)
      (by simp only [one_mul]; rw [hfe]; exact integrable_ext hτ hg)
      (by simp only [one_mul]; exact integrable_ext hτ b0) (fun x _ => differentiableAt_const _) (fun x _ => hd x)
    simp only [one_mul] at this
    rw [hfe] at this
    rw [int_ext, this]; simp
  have k1 := key (zi * th h + zbi * thb h) (0, 1) (a1.add a2) fun q => by
    rw [ev_add, e1, e2, wirt_alt, wirt_zb]; ring
  have k2 := key (Complex.I • (zi * th h - zbi * thb h)) (Complex.I • ((0, 1) : E 0)) ((a1.sub a2).smul _) fun q => by
    rw [ev_smul, ev_sub, e1, e2, wirt_alt, wirt_zb]
    linear_combination (-fderiv ℝ (ext h.1) q.1 (Complex.I • ((0, 1) : E 0))) * Complex.I_mul_I
  simp only [ev_add, ev_smul, ev_sub] at k1 k2
  rw [integral_add (integrable_ev hτ a1) (integrable_ev hτ a2)] at k1
  rw [integral_const_mul, integral_sub (integrable_ev hτ a1) (integrable_ev hτ a2)] at k2
  have k3 := (mul_eq_zero.1 k2).resolve_left Complex.I_ne_zero
  constructor
  · linear_combination (1 / 2 : ℂ) * k1 + (1 / 2 : ℂ) * k3
  · linear_combination (1 / 2 : ℂ) * k1 - (1 / 2 : ℂ) * k3

end

end Formalism.FourierDecayAlt.P.MAx2.R2

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx2.R2
open Formalism.FourierDecayAlt.MA

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.MAx1.An MeasureTheory
open scoped ComplexConjugate

noncomputable section

variable {τ : ℝ}

inductive Cl : ℤ → S τ → Prop
  | one : Cl 0 1
  | zero (K) : Cl K 0
  | mz {K f} : Cl K f → Cl (K + 1) (z * f)
  | mzb {K f} : Cl K f → Cl (K + 1) (zb * f)
  | mzi {K f} : Cl K f → Cl (K - 1) (zi * f)
  | mzbi {K f} : Cl K f → Cl (K - 1) (zbi * f)
  | up {K f} : Cl K f → Cl (K + 1) f
  | add {K f g} : Cl K f → Cl K g → Cl K (f + g)
  | smul {K f} (c : ℂ) : Cl K f → Cl K (c • f)

theorem Cl.cast {K K' : ℤ} {f : S τ} (h : Cl K f) (e : K = K') : Cl K' f := e ▸ h
theorem Cl.neg {K} {f : S τ} (h : Cl K f) : Cl K (-f) := by
  have := h.smul (-1); rwa [neg_one_smul] at this
theorem Cl.sub {K} {f g : S τ} (h : Cl K f) (h' : Cl K g) : Cl K (f - g) := by
  rw [sub_eq_add_neg]; exact h.add h'.neg
theorem Cl.sum {K} {ι : Type} (s : Finset ι) (f : ι → S τ) (h : ∀ i ∈ s, Cl K (f i)) : Cl K (∑ i ∈ s, f i) :=
  Finset.sum_induction f (Cl K) (fun _ _ => Cl.add) (Cl.zero K) h
theorem gg_eq : (gg : S τ) = z * zb - (τ : ℂ) • 1 := S_ext fun q => by
  rw [ev_sub, ev_mul, ev_smul, ev_one, ev_gg, eval_zeta, ev_zb, mul_one]
theorem Cl.mgg {K} {f : S τ} (h : Cl K f) : Cl (K + 2) (gg * f) := by
  rw [gg_eq, sub_mul, mul_assoc, smul_mul_assoc, one_mul]
  exact (h.mzb.mz.cast (by ring)).sub ((h.up.up.cast (by ring)).smul _)

theorem Cl.bd (hτ : 1 ≤ τ) {K} {f : S τ} (h : Cl K f) : Bd K f := by
  induction h with
  | one => exact bd_one
  | zero K => exact bd_zero K
  | mz _ ih => exact (bounded_zeta.mul hτ ih).mono hτ (by omega)
  | mzb _ ih => exact (bd_zb.mul hτ ih).mono hτ (by omega)
  | mzi _ ih => exact ((bd_zi hτ).mul hτ ih).mono hτ (by omega)
  | mzbi _ ih => exact ((bd_zbi hτ).mul hτ ih).mono hτ (by omega)
  | up _ ih => exact ih.mono hτ (by omega)
  | add _ _ ih ih' => exact ih.add ih'
  | smul c _ ih => exact ih.smul c

theorem Cl.th (hτ : 1 ≤ τ) {K} {f : S τ} (h : Cl K f) : Cl K (th f) := by
  induction h with
  | one => rw [th_one hτ]; exact Cl.zero _
  | zero K => rw [map_zero]; exact Cl.zero _
  | mz h ih => rw [th_mul, theta_zeta]; exact h.mz.add ih.mz
  | mzb h ih => rw [th_mul, th_zb, zero_mul, zero_add]; exact ih.mzb
  | mzi h ih => rw [th_mul, th_zi hτ, neg_mul]; exact h.mzi.neg.add ih.mzi
  | mzbi h ih => rw [th_mul, th_zbi hτ, zero_mul, zero_add]; exact ih.mzbi
  | up _ ih => exact ih.up
  | add _ _ ih ih' => rw [map_add]; exact ih.add ih'
  | smul c _ ih => rw [map_smul]; exact ih.smul c

theorem Cl.thb (hτ : 1 ≤ τ) {K} {f : S τ} (h : Cl K f) : Cl K (thb f) := by
  induction h with
  | one => rw [thb_one hτ]; exact Cl.zero _
  | zero K => rw [map_zero]; exact Cl.zero _
  | mz h ih => rw [thb_mul, theta_bar_zeta, zero_mul, zero_add]; exact ih.mz
  | mzb h ih => rw [thb_mul, thb_zb]; exact h.mzb.add ih.mzb
  | mzi h ih => rw [thb_mul, thb_zi hτ, zero_mul, zero_add]; exact ih.mzi
  | mzbi h ih => rw [thb_mul, thb_zbi hτ, neg_mul]; exact h.mzbi.neg.add ih.mzbi
  | up _ ih => exact ih.up
  | add _ _ ih ih' => rw [map_add]; exact ih.add ih'
  | smul c _ ih => rw [map_smul]; exact ih.smul c

theorem Cl.mono {K} {f : S τ} (h : Cl K f) (n : ℕ) : Cl (K + n) f := by
  induction n with
  | zero => simpa using h
  | succ n ih => exact ih.up.cast (by push_cast; ring)

def T1 (K : ℤ) (f : S τ) : Prop := Bd K f ∧ Bd K (th f) ∧ Bd K (thb f)

theorem Cl.t1 (hτ : 1 ≤ τ) {K} {f : S τ} (h : Cl K f) : T1 K f := ⟨h.bd hτ, (h.th hτ).bd hτ, (h.thb hτ).bd hτ⟩
theorem T1.mul (hτ : 1 ≤ τ) {K K'} {f g : S τ} (h : T1 K f) (h' : T1 K' g) : T1 (K + K') (f * g) :=
  ⟨h.1.mul hτ h'.1, by rw [th_mul]; exact (h.2.1.mul hτ h'.1).add (h.1.mul hτ h'.2.1),
    by rw [thb_mul]; exact (h.2.2.mul hτ h'.1).add (h.1.mul hτ h'.2.2)⟩
theorem T1.cj {K} {f : S τ} (h : T1 K f) : T1 K (cj f) :=
  ⟨h.1.cj, by rw [th_cj]; exact h.2.2.cj, by rw [thb_cj]; exact h.2.1.cj⟩
theorem first_order_gamma (hτ : 1 ≤ τ) : T1 2 (gg : S τ) := by
  have := (Cl.one (τ := τ)).mgg; rw [mul_one] at this; exact this.t1 hτ

def opR (c : ℂ) (f : S τ) : S τ := -(gg * (zi * th f)) - c • (zb * f)
def opRs (c : ℂ) (g : S τ) : S τ := zbi * thb (gg * g) - conj c • (z * g)
def opV (c : ℂ) (f : S τ) : S τ := gg * (zbi * thb f) - c • (z * f)
def opVs (c : ℂ) (g : S τ) : S τ := -(zi * th (gg * g)) - conj c • (zb * g)

theorem Cl.opR (hτ : 1 ≤ τ) {K} {f : S τ} (h : Cl K f) (c) : Cl (K + 1) (opR c f) :=
  (((h.th hτ).mzi.mgg.cast (by ring)).neg).sub (h.mzb.smul c)
theorem Cl.opV (hτ : 1 ≤ τ) {K} {f : S τ} (h : Cl K f) (c) : Cl (K + 1) (opV c f) :=
  (((h.thb hτ).mzbi.mgg.cast (by ring))).sub (h.mz.smul c)
theorem Cl.opRs (hτ : 1 ≤ τ) {K} {f : S τ} (h : Cl K f) (c) : Cl (K + 1) (opRs c f) :=
  (((h.mgg.thb hτ).mzbi.cast (by ring))).sub (h.mz.smul _)
theorem Cl.opVs (hτ : 1 ≤ τ) {K} {f : S τ} (h : Cl K f) (c) : Cl (K + 1) (opVs c f) :=
  (((h.mgg.th hτ).mzi.cast (by ring)).neg).sub (h.mzb.smul _)

theorem inner_eq_integral_alt (f g : S τ) : ip0 f g = ∫ q, ev (f * cj g) q ∂mu0 0 τ := rfl

theorem cj_mul (f g : S τ) : cj (f * g) = cj f * cj g := S_ext fun q => by simp
theorem cj_gg : cj (gg : S τ) = gg := S_ext fun q => by simp [ev_gg, mul_comm]

theorem adjR (hτ : 1 ≤ τ) {K K' : ℤ} {f g : S τ} {ε : ℝ} (hε : 0 < ε)
    (h0 : ∀ q : Qp 0 τ, Complex.normSq q.1.2 - τ ≤ ε → ev f q = 0) (hf : T1 K f) (hg : Cl K' g)
    (hK : K + K' + 2 ≤ -3) (c : ℂ) : ip0 (opR c f) g = ip0 f (opRs c g) ∧ ip0 (opV c f) g = ip0 f (opVs c g) := by
  have hh : T1 (K + (2 + K')) (f * cj (gg * g)) := by
    rw [cj_mul, cj_gg]; exact hf.mul hτ ((first_order_gamma hτ).mul hτ (hg.t1 hτ).cj)
  obtain ⟨i1, i2⟩ := ibp hτ hε (h := f * cj (gg * g)) (fun q hq => by rw [ev_mul, h0 q hq, zero_mul])
    (hh.1.mono hτ (by omega)) (hh.2.1.mono hτ (by omega)) (hh.2.2.mono hτ (by omega))
  have j1 := integrable_ev hτ ((((bd_zi hτ).mul hτ hh.2.1)).mono hτ (by omega))
  have j2 := integrable_ev hτ ((((bd_zbi hτ).mul hτ hh.2.2)).mono hτ (by omega))
  have r1 := integrable_ev hτ ((hf.1.mul hτ ((hg.opRs hτ c).bd hτ).cj).mono hτ (K' := -3) (by omega))
  have r2 := integrable_ev hτ ((hf.1.mul hτ ((hg.opVs hτ c).bd hτ).cj).mono hτ (K' := -3) (by omega))
  constructor
  · have e : ∀ q, ev (opR c f * cj g) q = ev (f * cj (opRs c g)) q - ev (zi * th (f * cj (gg * g))) q := fun q => by
      rw [th_mul, th_cj]
      simp [opR, opRs, ev_zi hτ, ev_zbi hτ, eval_zeta, ev_zb, ev_gg]
      ring
    rw [inner_eq_integral_alt, inner_eq_integral_alt]; simp only [e]
    rw [integral_sub r1 j1, i1, sub_zero]
  · have e : ∀ q, ev (opV c f * cj g) q = ev (f * cj (opVs c g)) q + ev (zbi * thb (f * cj (gg * g))) q := fun q => by
      rw [thb_mul, thb_cj]
      simp [opV, opVs, ev_zi hτ, ev_zbi hτ, eval_zeta, ev_zb, ev_gg]
      ring
    rw [inner_eq_integral_alt, inner_eq_integral_alt]; simp only [e]
    rw [integral_add r2 j2, i2, add_zero]

def Gf (τ : ℝ) (x : E 0) : ℝ := Complex.normSq x.2 - τ

theorem Gf_smooth : ContDiff ℝ sm (Gf τ) := by
  have : Gf τ = fun x : E 0 => x.2.re * x.2.re + x.2.im * x.2.im - τ := by
    funext x; simp [Gf, Complex.normSq_apply]
  rw [this]
  have h1 : ContDiff ℝ sm fun x : E 0 => x.2.re := Complex.reCLM.contDiff.comp contDiff_snd
  have h2 : ContDiff ℝ sm fun x : E 0 => x.2.im := Complex.imCLM.contDiff.comp contDiff_snd
  exact ((h1.mul h1).add (h2.mul h2)).sub contDiff_const

theorem Gf_pos (q : Qp 0 τ) : 0 < Gf τ q.1 := sub_pos.2 q.2.2

theorem phi_smooth {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) :
    (fun q : Qp 0 τ => ((φ (Gf τ q.1) : ℝ) : ℂ)) ∈ smSub 0 τ := by
  have h1 : ContDiffOn ℝ sm (fun x => Real.log (Gf τ x)) (Qset 0 τ) :=
    Gf_smooth.contDiffOn.log fun x hx => (Gf_pos ⟨x, hx⟩).ne'
  have h2 : ContDiffOn ℝ sm (fun x => ((φ (Real.exp (Real.log (Gf τ x))) : ℝ) : ℂ)) (Qset 0 τ) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (ContDiff.comp_contDiffOn (g := fun u => φ (Real.exp u)) hφ h1)
  exact h2.congr fun x hx => by rw [ext_of_mem _ hx, Real.exp_log (Gf_pos ⟨x, hx⟩)]

def phiS {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) : S τ := ⟨_, phi_smooth hφ⟩

theorem fd_phi {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : Qp 0 τ) (e : E 0) :
    fderiv ℝ (ext (phiS (τ := τ) hφ).1) q.1 e =
      ((LE.ld 1 φ (Gf τ q.1) / Gf τ q.1 : ℝ) : ℂ) * fderiv ℝ (ext (gg : S τ).1) q.1 e := by
  have hG : HasFDerivAt (Gf τ) (fderiv ℝ (Gf τ) q.1) q.1 := (Gf_smooth.differentiable (by simp [sm]) q.1).hasFDerivAt
  have hψ : HasDerivAt (fun u => φ (Real.exp u)) (LE.ld 1 φ (Gf τ q.1)) (Real.log (Gf τ q.1)) := by
    rw [LE.ld, iteratedDeriv_one]
    exact ((hφ.differentiable (by simp)) _).hasDerivAt
  have h1 := (hψ.comp _ (Real.hasDerivAt_log (Gf_pos q).ne')).comp_hasFDerivAt q.1 hG
  have h2 := Complex.ofRealCLM.hasFDerivAt.comp q.1 h1
  have h3 := Complex.ofRealCLM.hasFDerivAt.comp q.1 hG
  have e1 : ext (phiS (τ := τ) hφ).1 =ᶠ[nhds q.1]
      (Complex.ofRealCLM ∘ ((fun u => φ (Real.exp u)) ∘ Real.log) ∘ Gf τ) := by
    filter_upwards [(Qset_open 0 τ).mem_nhds q.2] with y hy
    rw [ext_of_mem _ hy]
    simp [phiS, Real.exp_log (Gf_pos ⟨y, hy⟩)]
  have e2 : ext (gg : S τ).1 =ᶠ[nhds q.1] (Complex.ofRealCLM ∘ Gf τ) := by
    filter_upwards [(Qset_open 0 τ).mem_nhds q.2] with y hy
    rw [ext_of_mem _ hy]
    have := ev_gg (τ := τ) ⟨y, hy⟩
    rw [Complex.mul_conj] at this
    show ev gg ⟨y, hy⟩ = _
    rw [this]; simp [Gf]
  rw [e1.fderiv_eq, e2.fderiv_eq, h2.fderiv, h3.fderiv]
  simp [div_eq_mul_inv]

theorem first_order_cutoff (hτ : 1 ≤ τ) {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) {ε : ℝ} (hε : 0 < ε) (h0 : ∀ x, x ≤ ε → φ x = 0)
    (hb : ∀ p, ∃ C, ∀ x, 0 < x → |LE.ld p φ x| ≤ C) : T1 0 (phiS (τ := τ) hφ) := by
  obtain ⟨C0, hC0⟩ := hb 0
  obtain ⟨C1, hC1⟩ := hb 1
  have n0 : 0 ≤ C0 := (abs_nonneg _).trans (hC0 1 one_pos)
  have n1 : 0 ≤ C1 := (abs_nonneg _).trans (hC1 1 one_pos)
  have key : ∀ q : Qp 0 τ, ‖((LE.ld 1 φ (Gf τ q.1) / Gf τ q.1 : ℝ) : ℂ) * (q.1.2 * conj q.1.2)‖ ≤
      C1 * (1 + τ / ε) * ‖q.1.2‖ ^ (0 : ℤ) := fun q => by
    have hp := Gf_pos q
    rw [zpow_zero, mul_one, Complex.mul_conj, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs]
    have hn : Complex.normSq q.1.2 = Gf τ q.1 + τ := by simp [Gf]
    by_cases hlt : Gf τ q.1 < ε
    · have : LE.ld 1 φ (Gf τ q.1) = 0 := by
        rw [LE.ld, iteratedDeriv_one]
        have : (fun u => φ (Real.exp u)) =ᶠ[nhds (Real.log (Gf τ q.1))] fun _ => 0 := by
          filter_upwards [Iio_mem_nhds (Real.log_lt_log hp hlt)] with u hu
          exact h0 _ (le_of_lt ((Real.lt_log_iff_exp_lt hε).1 hu))
        rw [this.deriv_eq]; simp
      rw [this]; simp; positivity
    · push Not at hlt
      rw [hn, abs_mul, abs_div, abs_of_pos hp, abs_of_pos (by linarith : 0 < Gf τ q.1 + τ)]
      have h1 : τ / Gf τ q.1 ≤ τ / ε := div_le_div_of_nonneg_left (by linarith) hε hlt
      calc |LE.ld 1 φ (Gf τ q.1)| / Gf τ q.1 * (Gf τ q.1 + τ) = |LE.ld 1 φ (Gf τ q.1)| * (1 + τ / Gf τ q.1) := by
            field_simp
        _ ≤ C1 * (1 + τ / ε) := mul_le_mul (hC1 _ hp) (by linarith) (by positivity) n1
  refine ⟨⟨C0, n0, fun q => ?_⟩, ⟨C1 * (1 + τ / ε), by positivity, fun q => ?_⟩,
    ⟨C1 * (1 + τ / ε), by positivity, fun q => ?_⟩⟩
  · have := hC0 _ (Gf_pos q)
    rw [LE.ld, iteratedDeriv_zero, Real.exp_log (Gf_pos q)] at this
    simpa [phiS, ev] using this
  · have e := congrArg (fun f => ev f q) (th_gg (τ := τ) hτ)
    simp only [ev_th, ev_mul, eval_zeta, ev_zb, wirt_alt] at e
    rw [ev_th, wirt_alt, fd_phi, fd_phi]
    convert key q using 2
    rw [← e]; ring
  · have e := congrArg (fun f => ev f q) (thb_gg (τ := τ) hτ)
    simp only [ev_thb, ev_mul, eval_zeta, ev_zb, wirt_zb] at e
    rw [ev_thb, wirt_zb, fd_phi, fd_phi]
    convert key q using 2
    rw [← e]; ring

end

end Formalism.FourierDecayAlt.P.MAx2.R2

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx2.R2
open Formalism.FourierDecayAlt.MA

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.MAx1.An MeasureTheory Finset
open scoped ComplexConjugate

noncomputable section

section Act
variable (P : M.Par)

def Phi : (DQ P).Pr →+* Module.End ℂ (SmQ P.r P.TT) :=
  RingHom.fst (Module.End ℂ (SmQ P.r P.TT)) (Module.End ℂ (SmQ P.r P.TT))ᵐᵒᵖ
theorem actA_eq (a : A P (DQ P)) (f π) : actA P a f π = ∑ π', Phi P (a π π') (f π') := rfl

theorem act_mul (a b : A P (DQ P)) (f) : actA P (a * b) f = actA P a (actA P b f) := by
  funext π
  simp only [actA_eq, Matrix.mul_apply, map_sum, map_mul, LinearMap.sum_apply, Module.End.mul_apply]
  rw [Finset.sum_comm]
theorem act_add (a b : A P (DQ P)) (f π) : actA P (a + b) f π = actA P a f π + actA P b f π := by
  simp only [actA_eq, Matrix.add_apply, map_add, LinearMap.add_apply, Finset.sum_add_distrib]
theorem act_sub (a b : A P (DQ P)) (f π) : actA P (a - b) f π = actA P a f π - actA P b f π := by
  simp only [actA_eq, Matrix.sub_apply, map_sub, LinearMap.sub_apply, Finset.sum_sub_distrib]
theorem act_neg (a : A P (DQ P)) (f π) : actA P (-a) f π = -actA P a f π := by
  simp only [actA_eq, Matrix.neg_apply, map_neg, LinearMap.neg_apply, Finset.sum_neg_distrib]
theorem act_diag (d : M.Ty P → (DQ P).Pr) (f π) : actA P (Matrix.diagonal d) f π = (d π).1 (f π) := by
  rw [actA_eq, Finset.sum_eq_single π (fun b _ hb => by rw [Matrix.diagonal_apply_ne _ hb.symm, map_zero]; rfl)
    (by simp), Matrix.diagonal_apply_eq]
  rfl
theorem act_one (f) : actA P 1 f = f := by
  funext π; rw [← Matrix.diagonal_one, act_diag]; rfl
theorem act_sc (w : (DQ P).Pr) (f π) : actA P (sc P (DQ P) w) f π = w.1 (f π) := act_diag P _ f π
theorem star_sc (w : (DQ P).Pr) : star (sc P (DQ P) w) = sc P (DQ P) (star w) := by
  simp only [sc, Matrix.scalar_apply, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]; rfl
theorem alg_fst (c : ℂ) (g : SmQ P.r P.TT) : (algebraMap ℂ (DQ P).Pr c).1 g = c • g := rfl
theorem act_alg (c : ℂ) (f π) : actA P (algebraMap ℂ (A P (DQ P)) c) f π = c • f π := by
  rw [Matrix.algebraMap_eq_diagonal, act_diag]; rfl
theorem act_kap (g : M.Ty P → ℂ) (f π) : actA P (kap P (DQ P) g) f π = g π • f π := act_diag P _ f π
end Act

section R0
variable {B : Type} [Ring B] [Algebra ℂ B] (L : LevelData B 0)
theorem Dr0 : L.Dr = 1 := by simp [LevelData.Dr]
theorem Drb0 : L.Drb = 1 := by simp [LevelData.Drb]
theorem Dri0 : L.Dri = 1 := by simp [LevelData.Dri]
theorem Drbi0 : L.Drbi = 1 := by simp [LevelData.Drbi]
theorem Ahat0 (y) : L.Ahat y = 1 := by simp [LevelData.Ahat, LevelData.Dr, LevelData.Ar, LevelData.Tprod]
theorem Ahatv0 (y) : L.Ahatv y = 1 := by simp [LevelData.Ahatv, LevelData.Drb, LevelData.Avr, LevelData.Tvprod]
theorem raising_eq_gamma_lowering (y) : L.R0 y = L.GG * L.l0 y := by
  simp [LevelData.R0, LevelData.Drb, LevelData.Ar, LevelData.Br, LevelData.Tprod]
theorem R0v0 (y) : L.R0v y = L.GG * L.m0 y := by
  simp [LevelData.R0v, LevelData.Dr, LevelData.Avr, LevelData.Bvr, LevelData.Tvprod]
end R0

abbrev Pb (b : ℕ) : M.Par := ⟨1, 0, 1, 1, fun _ => 0, fun _ => 2 * b⟩

variable (b : ℕ)

theorem hT : 1 ≤ (Pb b).TT := by simp [M.Par.TT]
theorem aC_eq (π) : M.aC (Pb b) π = b := by simp [M.aC]

theorem nab_act (f π) : actA (Pb b) (nabA (Pb b) (DQ (Pb b))) f π = zi * th (f π) + (b : ℂ) • (zb * (ggi * f π)) := by
  rw [nabA, act_diag, aC_eq]; rfl
theorem nabs_act (f π) : actA (Pb b) (nabsA (Pb b) (DQ (Pb b))) f π =
    -(zbi * thb (f π)) + (b : ℂ) • (z * (ggi * f π)) := by
  rw [nabsA, act_diag, aC_eq]; rfl
theorem z_act (f π) : actA (Pb b) (zA (Pb b) (DQ (Pb b))) f π = z * f π := act_sc _ _ _ _
theorem zb_act (f π) : actA (Pb b) (zbA (Pb b) (DQ (Pb b))) f π = zb * f π := act_sc _ _ _ _
theorem zi_act (f π) : actA (Pb b) (ziA (Pb b) (DQ (Pb b))) f π = zi * f π := act_sc _ _ _ _
theorem zbi_act (f π) : actA (Pb b) (zbiA (Pb b) (DQ (Pb b))) f π = zbi * f π := act_sc _ _ _ _
theorem gg_act (f π) : actA (Pb b) (ggA (Pb b) (DQ (Pb b))) f π = gg * f π := act_sc _ _ _ _
theorem ggi_act (f π) : actA (Pb b) (ggiA (Pb b) (DQ (Pb b))) f π = ggi * f π := act_sc _ _ _ _

variable {b}
variable {L : LevelData (A (Pb b) (DQ (Pb b))) 0} (hL : IsModelLevel (Pb b) (DQ (Pb b)) L)
include hL

theorem raising_action (y f π) : actA (Pb b) (L.R0 y) f π = opR (b + (y + 1 / 2)) (f π) := by
  obtain ⟨-, -, -, -, -, -, hz, hzi, hzb, hzbi, hg, hgi, hn, hns, -⟩ := hL
  rw [raising_eq_gamma_lowering, LevelData.l0, hg, hn, hzb, hgi]
  simp only [act_mul, act_sub, act_neg, act_alg, gg_act, nab_act, zb_act, ggi_act]
  refine S_ext fun q => ?_
  have := gg_ne' q
  simp only [opR, ev_mul, ev_sub, ev_add, ev_neg, ev_smul, ev_gg, ev_ggi (hT b)]
  field_simp
  ring

theorem raising_variant_action (y f π) : actA (Pb b) (L.R0v y) f π = opV (b + (y - 1 / 2)) (f π) := by
  obtain ⟨-, -, -, -, -, -, hz, hzi, hzb, hzbi, hg, hgi, hn, hns, -⟩ := hL
  rw [R0v0, LevelData.m0, hg, hns, hz, hgi]
  simp only [act_mul, act_sub, act_neg, act_alg, gg_act, nabs_act, z_act, ggi_act]
  refine S_ext fun q => ?_
  have := gg_ne' q
  simp only [opV, ev_mul, ev_sub, ev_add, ev_neg, ev_smul, ev_gg, ev_ggi (hT b)]
  field_simp
  ring

theorem raising_star_action (y f π) : actA (Pb b) (star (L.R0 y)) f π = opRs (b + (y + 1 / 2)) (f π) := by
  have : Fact ((DQ (Pb b)).Laws (Pb b).TT) := ⟨laws (hT b)⟩
  obtain ⟨-, s1, s2, s3, s4, s5⟩ := Formalism.FourierDecayAlt.P.MAx1.starGens (Pb b) (DQ (Pb b))
  obtain ⟨-, -, -, -, -, -, hz, hzi, hzb, hzbi, hg, hgi, hn, hns, -⟩ := hL
  have s6 : star (zbA (Pb b) (DQ (Pb b))) = zA (Pb b) (DQ (Pb b)) := by rw [← s1, star_star]
  rw [raising_eq_gamma_lowering, LevelData.l0, hg, hn, hzb, hgi]
  simp only [star_mul, star_sub, star_neg, s3, s4, s5, s6, ← algebraMap_star_comm]
  simp only [act_mul, act_sub, act_neg, act_alg, gg_act, nabs_act, z_act, ggi_act]
  refine S_ext fun q => ?_
  have := gg_ne' q
  simp only [opRs, ev_mul, ev_sub, ev_add, ev_neg, ev_smul, ev_gg, ev_ggi (hT b), map_add, Complex.conj_natCast,
    Complex.star_def]
  field_simp
  ring

theorem R0vs_act (y f π) : actA (Pb b) (star (L.R0v y)) f π = opVs (b + (y - 1 / 2)) (f π) := by
  have : Fact ((DQ (Pb b)).Laws (Pb b).TT) := ⟨laws (hT b)⟩
  obtain ⟨-, s1, s2, s3, s4, s5⟩ := Formalism.FourierDecayAlt.P.MAx1.starGens (Pb b) (DQ (Pb b))
  obtain ⟨-, -, -, -, -, -, hz, hzi, hzb, hzbi, hg, hgi, hn, hns, -⟩ := hL
  have s6 : star (nabsA (Pb b) (DQ (Pb b))) = nabA (Pb b) (DQ (Pb b)) := by rw [← s5, star_star]
  rw [R0v0, LevelData.m0, hg, hns, hz, hgi]
  simp only [star_mul, star_sub, star_neg, s1, s3, s4, s6, ← algebraMap_star_comm]
  simp only [act_mul, act_sub, act_neg, act_alg, gg_act, nab_act, zb_act, ggi_act]
  refine S_ext fun q => ?_
  have := gg_ne' q
  simp only [opVs, ev_mul, ev_sub, ev_add, ev_neg, ev_smul, ev_gg, ev_ggi (hT b), map_add, map_sub, Complex.conj_natCast,
    Complex.star_def]
  field_simp
  ring

theorem hat_cl {a} (ha : a ∈ hatSet (Pb b) L) {K} {f : M.Ty (Pb b) → S (Pb b).TT} (hf : ∀ π, Cl K (f π)) (π) :
    Cl (K + 1) (actA (Pb b) a f π) := by
  rcases ha with ((⟨y, rfl⟩ | ⟨y, rfl⟩) | ⟨y, rfl⟩) | ⟨y, rfl⟩
  · rw [Ahat0, act_one]; exact (hf π).up
  · rw [raising_action hL]; exact (hf π).opR (hT b) _
  · rw [Ahatv0, act_one]; exact (hf π).up
  · rw [raising_variant_action hL]; exact (hf π).opV (hT b) _

theorem word_cl {K} {f : M.Ty (Pb b) → S (Pb b).TT} (hf : ∀ π, Cl K (f π)) (w : List (A (Pb b) (DQ (Pb b))))
    (hw : ∀ a ∈ w, a ∈ hatSet (Pb b) L) : ∀ π, Cl (K + w.length) (actA (Pb b) w.prod f π) := by
  induction w with
  | nil => intro π; rw [List.prod_nil, act_one]; simpa using hf π
  | cons a w ih =>
    intro π
    rw [List.prod_cons, act_mul]
    exact (hat_cl hL (hw a (List.mem_cons_self ..)) (ih fun x hx => hw x (List.mem_cons_of_mem _ hx)) π).cast
      (by simp; ring)

omit hL in
theorem const_cl (a : A (Pb b) (DQ (Pb b))) (ha : ∀ π π', ∃ c : ℂ, a π π' = algebraMap ℂ _ c) {K}
    {f : M.Ty (Pb b) → S (Pb b).TT} (hf : ∀ π, Cl K (f π)) (π) : Cl K (actA (Pb b) a f π) := by
  refine Cl.sum _ _ fun π' _ => ?_
  obtain ⟨c, hc⟩ := ha π π'
  rw [hc, alg_fst]; exact (hf π').smul c

omit hL in
theorem SS_const (i π π') : ∃ c : ℂ, SS (Pb b) (DQ (Pb b)) i π π' = algebraMap ℂ _ c := by
  simp only [SS, Matrix.of_apply]
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨0, (map_zero _).symm⟩

theorem bdd_cl {a} (ha : a ∈ Submonoid.closure (bddSet (Pb b) L)) :
    ∀ {K} {f : M.Ty (Pb b) → S (Pb b).TT} (hf : ∀ π, Cl K (f π)) (π), Cl K (actA (Pb b) a f π) := by
  obtain ⟨-, -, -, -, -, -, hz, hzi, hzb, hzbi, hg, hgi, hn, hns, -⟩ := hL
  induction ha using Submonoid.closure_induction with
  | one => intro K f hf π; rw [act_one]; exact hf π
  | mul x y _ _ ihx ihy => intro K f hf π; rw [act_mul]; exact ihx (ihy hf) π
  | mem x hx =>
    intro K f hf π
    rcases hx with (((rfl | rfl | rfl | rfl) | ⟨g, rfl⟩) | ⟨i, -, rfl⟩) | ⟨i, -, rfl⟩
    · rw [hzi, zi_act]; exact (hf π).mzi.up.cast (by ring)
    · rw [hzbi, zbi_act]; exact (hf π).mzbi.up.cast (by ring)
    · rw [LevelData.D, LevelData.Dbi, Dr0, Drbi0, one_mul, mul_one, hz, hzbi, act_mul, z_act, zbi_act]
      exact (hf π).mzbi.mz.cast (by ring)
    · rw [LevelData.Db, LevelData.Di, Drb0, Dri0, one_mul, mul_one, hzb, hzi, act_mul, zb_act, zi_act]
      exact (hf π).mzi.mzb.cast (by ring)
    · rw [act_kap]; exact (hf π).smul _
    · simp only []
      rw [Drb0, Dri0, one_mul, one_mul]; exact const_cl _ (SS_const i) hf π
    · simp only []
      rw [Drb0, Dri0, one_mul, one_mul]
      refine const_cl _ (fun π π' => ?_) hf π
      obtain ⟨c, hc⟩ := SS_const (b := b) i π' π
      exact ⟨star c, by rw [Matrix.star_apply, hc, algebraMap_star_comm]⟩

theorem jdecay {K : ℤ} {j : M.Ty (Pb b) → S (Pb b).TT} (hj : ∀ π, Cl K (j π)) (m : ℕ) (hK : K + m ≤ -2) :
    JDecay (Pb b) L j m := by
  intro w hw ha π
  have h1 := (word_cl hL hj w ha π).bd (hT b)
  have h2 := (integrable_ev (hT b) ((h1.mul (hT b) h1.cj).mono (hT b) (K' := -3) (by omega))).norm
  refine h2.congr (Filter.Eventually.of_forall fun q => ?_)
  simp only [ev_mul, ev_cj, norm_mul, Complex.norm_conj, sq]; rfl

theorem jadj {K : ℤ} {j : M.Ty (Pb b) → S (Pb b).TT} (hj : ∀ π, Cl K (j π)) (m : ℕ) (hK : 2 * K + m ≤ -4) :
    JAdj (Pb b) L j m := by
  intro φ ε hε hφ h0 hb β hβ X hX v w hl ha
  have hG : ∀ q, Gq (Pb b) q = Gf (Pb b).TT q.1 := fun q => by simp [Gq, Gf]
  have hφS : toSm (Pb b) (fun q => (φ (Gq (Pb b) q) : ℂ)) = phiS hφ := by
    simp only [hG]
    exact dif_pos (phi_smooth hφ)
  rw [hφS]
  have hv := bdd_cl hL hβ (word_cl hL hj v fun a h => ha a (List.mem_append_left _ h))
  have hw := word_cl hL hj w fun a h => ha a (List.mem_append_right _ h)
  rw [← act_mul] at hv
  have hf : ∀ π, T1 (0 + (K + v.length)) (phiS hφ * actA (Pb b) (β * v.prod) j π) := fun π =>
    (first_order_cutoff (hT b) hφ hε h0 hb).mul (hT b) ((hv π).t1 (hT b))
  have hz : ∀ π (q : Qp 0 (Pb b).TT), Complex.normSq q.1.2 - (Pb b).TT ≤ ε →
      ev (phiS hφ * actA (Pb b) (β * v.prod) j π) q = 0 := fun π q hq => by
    rw [ev_mul]
    have : ev (phiS hφ) q = 0 := by
      show ((φ (Gf _ q.1) : ℝ) : ℂ) = 0
      rw [h0 (Gf _ q.1) hq]; simp
    rw [this, zero_mul]
  rw [act_mul _ (star X)]
  rcases hX with ((⟨y, rfl⟩ | ⟨y, rfl⟩) | ⟨y, rfl⟩) | ⟨y, rfl⟩
  · rw [Ahat0, star_one, act_one, act_one]
  · refine Finset.sum_congr rfl fun π _ => ?_
    rw [raising_action hL, raising_star_action hL]
    exact (adjR (hT b) hε (hz π) (hf π) (hw π) (by omega) _).1
  · rw [Ahatv0, star_one, act_one, act_one]
  · refine Finset.sum_congr rfl fun π _ => ?_
    rw [raising_variant_action hL, R0vs_act hL]
    exact (adjR (hT b) hε (hz π) (hf π) (hw π) (by omega) _).2

end

end Formalism.FourierDecayAlt.P.MAx2.R2

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx2.R2
open Formalism.FourierDecayAlt.MA

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.MAx1.An MeasureTheory Finset
open scoped ComplexConjugate

noncomputable section

variable {τ : ℝ}

def jf (b n : ℕ) : S τ := gg ^ b * zi ^ n

theorem gg_ggi (hτ : 1 ≤ τ) : (gg : S τ) * ggi = 1 := Ring.mul_inverse_cancel _ (laws hτ).unit_gg

theorem th_ggpow (hτ : 1 ≤ τ) (b : ℕ) : th ((gg : S τ) ^ b) = (b : ℂ) • (z * zb * ggi * gg ^ b) ∧
    thb ((gg : S τ) ^ b) = (b : ℂ) • (z * zb * ggi * gg ^ b) := by
  have h := gg_ggi hτ
  induction b with
  | zero => simp [th_one hτ, thb_one hτ]
  | succ b ih =>
    rw [pow_succ, th_mul, thb_mul, ih.1, ih.2, th_gg hτ, thb_gg hτ]
    have : (b : ℂ) • (z * zb * ggi * gg ^ b) * gg + gg ^ b * (z * zb) =
        ((b + 1 : ℕ) : ℂ) • (z * zb * ggi * (gg ^ b * (gg : S τ))) := by
      push_cast
      rw [add_smul, one_smul, smul_mul_assoc]
      congr 1
      · congr 1; ring
      · linear_combination (-(z * zb * gg ^ b)) * h
    exact ⟨this, this⟩

theorem th_zipow (hτ : 1 ≤ τ) (n : ℕ) : th ((zi : S τ) ^ n) = -((n : ℂ) • zi ^ n) ∧ thb ((zi : S τ) ^ n) = 0 := by
  induction n with
  | zero => simp [th_one hτ, thb_one hτ]
  | succ n ih =>
    rw [pow_succ, th_mul, thb_mul, ih.1, ih.2, th_zi hτ, thb_zi hτ]
    refine ⟨?_, by simp⟩
    push_cast
    rw [add_smul, one_smul, neg_mul, smul_mul_assoc]; ring

theorem th_jf (hτ : 1 ≤ τ) (b n : ℕ) :
    th (jf b n : S τ) = (b : ℂ) • (z * zb * ggi * jf b n) - (n : ℂ) • jf b n := by
  rw [jf, th_mul, (th_ggpow hτ b).1, (th_zipow hτ n).1]
  simp only [Algebra.smul_def]; ring
theorem thb_jf (hτ : 1 ≤ τ) (b n : ℕ) : thb (jf b n : S τ) = (b : ℂ) • (z * zb * ggi * jf b n) := by
  rw [jf, thb_mul, (th_ggpow hτ b).2, (th_zipow hτ n).2]
  simp only [Algebra.smul_def]; ring

theorem cl_jf (b n : ℕ) : Cl (2 * b - n) (jf b n : S τ) := by
  have h1 : ∀ n : ℕ, Cl (-n) ((zi : S τ) ^ n) := fun n => by
    induction n with
    | zero => simpa using Cl.one
    | succ n ih => rw [pow_succ']; exact ih.mzi.cast (by push_cast; ring)
  induction b with
  | zero => simpa [jf] using h1 n
  | succ b ih => rw [jf, pow_succ', mul_assoc]; exact ih.mgg.cast (by push_cast; ring)

def lamb (b d : ℕ) : Fin ((Pb b).k + 2 * (Pb b).r + 1) → ℝ := fun i => if (i : ℕ) = 0 then -1 / 2 else -1 / 2 - d

theorem cmValueConst_eq (b : ℕ) (Y : ℂ) : C0 (QQr (Pb b) (DQ (Pb b))) (sites (Pb b) (DQ (Pb b))) Y = t11 (Pb b) (DQ (Pb b)) Y := by
  simp [C0, v0, sites, QQr, Fin.sum_univ_two, Matrix.one_apply]

theorem wC_eq (b : ℕ) (π) (Y : ℂ) : M.wC (Pb b) π Y = -((Y + 1 / 2) * (Y + (1 / 2 + 2 * b))) := by
  simp [M.wC, M.wNum, M.coordinatePolynomial, M.qP]

theorem jeigen (b d : ℕ) : JEigen (Pb b) (fun _ => jf b (d + 1 + 2 * b)) (lamb b d) := by
  intro Y
  funext π
  have hτ := hT b
  have hx : ∀ Y π, M.xC (Pb b) π Y = 1 := fun Y π => by simp [M.xC]
  have h21 : weightedSumBis (Pb b) (DQ (Pb b)) Y = 0 := by simp [weightedSumBis]
  have h12 : S12 (Pb b) (DQ (Pb b)) Y = 0 := by simp [S12]
  have h4 : S4 (Pb b) (DQ (Pb b)) Y = 0 := by simp [S4]
  have hp : (∏ s, ((Y : ℂ) + lamb b d s)) = (Y - 1 / 2) * (Y - 1 / 2 - d) := by
    rw [show (∏ s, ((Y : ℂ) + lamb b d s)) = ∏ s : Fin 2, ((Y : ℂ) + lamb b d s) from rfl, Fin.prod_univ_two]
    simp [lamb]; ring
  rw [cmValueConst_eq, t11, h21, h12, h4, mul_zero, mul_zero, zero_mul, add_zero, add_zero, add_zero, hp]
  simp only [xA, l0A, m0A, act_mul, act_add, act_sub, act_neg, act_alg, act_kap, gg_act, ggi_act, nab_act, nabs_act,
    z_act, zb_act, hx, wC_eq, one_smul]
  simp only [map_sub, map_neg, map_add, map_smul, thb_mul, th_jf hτ, thb_jf hτ, theta_bar_zeta, thb_zb, thb_zi hτ, thb_ggi hτ]
  refine S_ext fun q => ?_
  have h1 := gg_ne' q
  have h2 := z_ne hτ q
  have h3 : conj q.1.2 ≠ 0 := (map_ne_zero _).2 h2
  have h4 : (((Pb b).TT : ℝ) : ℂ) = 1 := by simp [M.Par.TT]
  simp only [ev_mul, ev_sub, ev_add, ev_neg, ev_smul, ev_zero, ev_gg, ev_ggi hτ, eval_zeta, ev_zb, ev_zi hτ, ev_zbi hτ, h4] at *
  generalize ev (jf b (d + 1 + 2 * b)) q = J
  generalize conj q.1.2 = w at *
  generalize q.1.2 = x at *
  push_cast
  field_simp
  ring

theorem Pb_OK (b : ℕ) : (Pb b).OK where
  k_pos := le_rfl
  T_pos := one_pos
  T'_pos := one_pos
  int_u := fun i _ => ⟨0, by simp⟩
  int_u' := fun i _ => ⟨2 * b, by simp⟩
  gap := fun i hi => by simp at hi

theorem lam_anti (b d : ℕ) (hd : 0 < d) : StrictAnti (lamb b d) := by
  intro x y hxy
  have hy : (y : ℕ) < 2 := y.2
  have : (x : ℕ) < y := hxy
  have hx0 : (x : ℕ) = 0 := by omega
  have hy1 : (y : ℕ) ≠ 0 := by omega
  have : (0 : ℝ) < d := by exact_mod_cast hd
  simp only [lamb, hx0, hy1, if_true, if_false]; linarith

theorem hypsNonvacuous : HypsNonvacuous := by
  intro Ntot Lb B hN hNL hL2
  obtain ⟨b, hb⟩ := exists_nat_ge (|B| + 6 * Ntot * Lb + 2 * Lb + 5)
  have : Fact ((DQ (Pb b)).Laws (Pb b).TT) := ⟨laws (hT b)⟩
  obtain ⟨L, hL⟩ := Formalism.FourierDecayAlt.P.MAx1.levelExists (Pb b) (DQ (Pb b))
  have hB := le_abs_self B
  have hB0 := abs_nonneg B
  have hN0 : (0 : ℝ) ≤ 6 * Ntot * Lb := by positivity
  have hcl : ∀ π : M.Ty (Pb b), Cl (-((2 * Ntot + 3 : ℕ) : ℤ) - 1)
      ((fun _ => jf b (2 * Ntot + 3 + 1 + 2 * b) : M.Ty (Pb b) → S (Pb b).TT) π) := fun π =>
    (cl_jf b _).cast (by push_cast; ring)
  refine ⟨Pb b, 1, L, fun _ => jf b (2 * Ntot + 3 + 1 + 2 * b), lamb b (2 * Ntot + 3), -(2 * b) + 2, -2,
    ⟨⟨Pb_OK b, le_rfl, le_rfl, hL, ⟨lam_anti _ _ (by omega), fun i => ⟨fun h => ?_, fun h => ?_⟩⟩,
      ⟨lam_anti _ _ (by omega), fun i => ⟨fun h => ?_, fun h => ?_⟩⟩, by linarith, fun Y hY => ?_⟩,
      jdecay hL hcl _ (by push_cast; omega), jadj hL hcl _ (by push_cast; omega), jeigen _ _, hN, hNL, hL2, ?_,
      by linarith⟩, ?_, by linarith⟩
  · have : (i : ℕ) = 0 := by simp at h; omega
    simp [lamb, this]; norm_num
  · simp at h
  · have : (i : ℕ) = 0 := by simp at h; omega
    simp only [lamb, this, if_true]; linarith
  · simp at h
  · left; constructor <;> simp only [] <;> linarith [hY.1, hY.2]
  · show ((2 : ℕ) : ℝ) * Lb ≤ _
    push_cast; linarith
  · intro h
    have h1 : (jf b (2 * Ntot + 3 + 1 + 2 * b) : S (Pb b).TT) = 0 := congrFun h fun _ => 0
    have h2 : IsUnit (jf b (2 * Ntot + 3 + 1 + 2 * b) : S (Pb b).TT) :=
      ((show IsUnit (gg : S (Pb b).TT) from (laws (hT b)).unit_gg).pow _).mul
        ((Ring.isUnit_iff_inverse_mul_cancel _ |>.1 ((laws (hT b)).unit_alt_bis M.vz) |> fun h =>
          (IsUnit.of_mul_eq_one (z : S (Pb b).TT) h : IsUnit (zi : S (Pb b).TT))).pow _)
    have := Formalism.FourierDecayAlt.P.analytic_nontrivial 0 (Pb b).TT
    exact not_isUnit_zero (h1 ▸ h2)

end

end Formalism.FourierDecayAlt.P.MAx2.R2

namespace Formalism.FourierDecayAlt.P.MAx2.R2
open Formalism.FourierDecayAlt.MA

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Matrix

section G
variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

noncomputable def low : (ℂ → M2 A) → List (Site A) → ℂ → M2 A
  | QQ, [] => QQ
  | QQ, σ :: s => low (fun Y => (Ts σ (star Y))ᴴ * QQ Y * Ts σ Y) s

theorem comm_mul (x : A) (M N : M2 A) (hM : ∀ i j, Commute (M i j) x) (hN : ∀ i j, Commute (N i j) x) (i j) :
    Commute ((M * N) i j) x := by
  rw [Matrix.mul_apply]
  exact Commute.sum_left _ _ _ fun k _ => (hM i k).mul_left (hN k j)

theorem step_ok (σ : Site A) (s : List (Site A)) (QQ : ℂ → M2 A) (h : SitesOK QQ (σ :: s)) :
    SitesOK (fun Y => (Ts σ (star Y))ᴴ * QQ Y * Ts σ Y) s := by
  obtain ⟨h1, h2⟩ := h
  rw [List.pairwise_cons] at h2
  refine ⟨fun τ hτ => ⟨(h1 τ (List.mem_cons_of_mem _ hτ)).1, ?_⟩, h2.2⟩
  intro Y i j x hx
  have hc := h2.1 τ hτ
  have hT : ∀ y ∈ ops τ, ∀ (Z : ℂ) a b, Commute (Ts σ Z a b) y := fun y hy Z a b =>
    (Formalism.FourierDecayAlt.P.MAx1.WeylSymmetry.Ts_comm σ y (hc _ (Or.inl (by simp [hol])) y hy).symm
      (hc _ (Or.inl (by simp [hol])) y hy).symm (hc _ (Or.inl (by simp [hol])) y hy).symm Z a b).symm
  have hsx : star x ∈ ops τ := by
    rcases hx with hx | hx
    · right; rwa [star_star]
    · left; exact hx
  refine comm_mul x _ _ (comm_mul x _ _ (fun a b => ?_) fun a b => (h1 τ (List.mem_cons_of_mem _ hτ)).2 Y a b x hx)
    (hT x hx Y) i j
  rw [Matrix.conjTranspose_apply]
  have := (hT _ hsx (star Y) b a).star_star
  rwa [star_star] at this

theorem low_real (s : List (Site A)) : ∀ (QQ : ℂ → M2 A) (Y : ℂ), star Y = Y →
    low QQ s Y = ((s.map fun σ => Ts σ Y).prod)ᴴ * QQ Y * (s.map fun σ => Ts σ Y).prod := by
  induction s with
  | nil => intro QQ Y _; simp [low]
  | cons σ s ih =>
    intro QQ Y hY
    rw [low, ih _ Y hY]
    simp only [hY, List.map_cons, List.prod_cons, Matrix.conjTranspose_mul, mul_assoc]

theorem form_low {S : Type} [Fintype S] [DecidableEq S] (w : List (Letter ℂ S)) (hw : Good w) (s : List (Site A)) :
    ∀ QQ : ℂ → M2 A, SitesOK QQ s →
      star (s.map fun σ => bT σ w).prod * RRw QQ w * (s.map fun σ => bT σ w).prod = RRw (low QQ s) w := by
  induction s with
  | nil => intro QQ _; simp [low]
  | cons σ s ih =>
    intro QQ h
    have h0 := h.1 σ (List.mem_cons_self ..)
    have := Formalism.FourierDecayAlt.P.site_exchange_relation ℂ A S σ QQ (fun Y => (Ts σ (star Y))ᴴ * QQ Y * Ts σ Y) w h0.1 h0.2
      (fun Y hY => by simp only [hY]) hw
    rw [low, ← ih _ (step_ok σ s QQ h), ← this]
    simp only [List.map_cons, List.prod_cons, star_mul, mul_assoc]

theorem first_clause {S : Type} [Fintype S] [DecidableEq S] (w : List (Letter ℂ S)) (hw : Good w) (s : List (Site A))
    (QQ : ℂ → M2 A) (h : SitesOK QQ s) :
    ∑ e, ∑ e', star (uw s w e) * RRw QQ w e e' * uw s w e' = (w.reverse.map fun a => C0 QQ s a.pt).prod := by
  have h1 := congrFun (congrFun (form_low w hw s QQ h) e1) e1
  rw [Formalism.FourierDecayAlt.P.word_matrix_entry_one ℂ A S _ w hw] at h1
  have h2 : (w.reverse.map fun l => low QQ s l.pt 0 0) = w.reverse.map fun a => C0 QQ s a.pt := by
    refine List.map_congr_left fun l hl => ?_
    rw [low_real s QQ l.pt (hw.2.1 l (List.mem_reverse.1 hl))]
    simp only [C0, v0, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [← h2, ← h1]
  simp only [uw, Matrix.mul_apply, Matrix.star_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
end G

theorem modelWordsD : Formalism.FourierDecayAlt.MA.ModelWordsD := by
  intro P _ D hL l S _ _ w hw
  have : Fact (D.Laws P.TT) := ⟨hL⟩
  have hs : SitesOK (K := ℂ) (startM P D l).QQ (sites P D) := by
    rw [Formalism.FourierDecayAlt.P.MAx1.sites_eq]; exact Formalism.FourierDecayAlt.P.MAx1.sitesOKM P D l
  exact ⟨first_clause w hw _ _ hs, fun Y h1 h2 z => Formalism.FourierDecayAlt.P.conjugate_word_eigen ℂ _ S _ _ w Y hs hw h1 h2 z⟩

end Formalism.FourierDecayAlt.P.MAx2.R2

namespace Formalism.FourierDecayAlt.P.MAx2

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA

theorem between_of_onCut {u u' : ℕ → ℝ} {l : ℕ} {Y : ℝ} (h : I.OnCut u u' l Y) : C7.Between u u' l Y := by
  unfold I.OnCut at h
  unfold C7.Between
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨min_lt_iff.2 (Or.inl (by linarith)), lt_max_iff.2 (Or.inr (by linarith))⟩
  · exact ⟨min_lt_iff.2 (Or.inr (by linarith)), lt_max_iff.2 (Or.inl (by linarith))⟩

end Formalism.FourierDecayAlt.P.MAx2

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA

theorem roots_outside_of_parts_alt : Formalism.FourierDecayAlt.MA.RootsOutQOfParts := by
  intro hJ P l L j lam α β Lb c Ntot hH
  obtain ⟨⟨_, hl1, hlk, _, hu, hu', _, hcut⟩, _⟩ := hH
  exact hJ (sysQ P l L j lam α β Lb c Ntot) P.u P.u' l hl1 hlk hu hu'
    (fun Y hY => MAx2.between_of_onCut (hcut Y hY))

theorem induction_imports_of_parts : Formalism.FourierDecayAlt.MA.StepImportsQOfParts := by
  intro hM hW hPR hI3 hAB hJ hI4 hI4' hI5 hR hWR hPRat
  obtain ⟨CR, hCR, hR⟩ := hR
  obtain ⟨Cd, hCd, hWR⟩ := hWR
  refine ⟨CR, Cd, Real.exp 3, hCR, hCd, (Real.exp_pos 3).le, fun P l L j lam α β Lb c Ntot hH w hw hl => ?_⟩
  exact ⟨hM P l L j lam α β Lb c Ntot hH w hw hl, hW P l L j lam α β Lb c Ntot hH w hw hl,
    hPR P l L j lam α β Lb c Ntot hH w hw hl, hI3 P l L j lam α β Lb c Ntot hH w hw hl,
    hAB P l L j lam α β Lb c Ntot hH w hw hl, hJ P l L j lam α β Lb c Ntot hH w hw hl,
    hI4 P l L j lam α β Lb c Ntot hH w hw hl, hI4' P l L j lam α β Lb c Ntot hH w hw hl,
    hI5 P l L j lam α β Lb c Ntot hH w hw hl, hR P l L j lam α β Lb c Ntot hH w hw hl,
    hWR P l L j lam α β Lb c Ntot hH w hw hl, hPRat P l L j lam α β Lb c Ntot hH w hw hl⟩

theorem third_identity_of_parts : Formalism.FourierDecayAlt.MA.EnergyAbsoluteIdentityFromComponents := by
  intro hS hPS hTy hBF P l L j lam α β Lb c Ntot hH w hw hl Y hY ω i
  have hH' := hH
  obtain ⟨⟨hOK, hl1, hlk, _, hu, hu', hαβ, hcut⟩, _, _, _, _, _, hL2, _, h6⟩ := hH'
  have hbox := (hBF (sysQ P l L j lam α β Lb c Ntot) hL2 h6).1 w.length hl
  have hYb : Y ∈ (sysQ P l L j lam α β Lb c Ntot).box w.length := hY
  have hmid : Y ∈ Set.Icc (α + (β - α) / 3) (β - (β - α) / 3) := hbox hYb
  have hYI : Y ∈ Set.Icc α β := ⟨by have := hmid.1; linarith, by have := hmid.2; linarith⟩
  have hπ := hTy P hOK (ixOf P w.length i).2
  have hsign := (hPS P.k P.r P.u P.u' (M.rho P (ixOf P w.length i).2) lam l Y hl1 hlk hu hu' hπ
    (MAx2.between_of_onCut (hcut Y hYI))).2.2
  have h := hS P l L j lam α β Lb c Ntot hH w hw hl Y hY ω i
  show _ = ((|∏ s, (Y + lam s)| * _ : ℝ) : ℂ) * _
  rw [hsign]
  exact h

theorem factor_chosen : Formalism.FourierDecayAlt.MA.FactorChosen := by
  intro hex P l L j lam α β Lb c Ntot hH N hN
  obtain ⟨mB, hmB⟩ := hex P l L j lam α β Lb Ntot hH N hN
  exact Classical.epsilon_spec ⟨mB, hmB⟩

theorem family_imports_of_parts : Formalism.FourierDecayAlt.MA.FamImportsQOfParts := by
  intro hex hch hrest P l L j lam α β Lb c Ntot hH N hN
  obtain ⟨h0, h1, h2, h3⟩ := hch hex P l L j lam α β Lb c Ntot hH N hN
  obtain ⟨m2, m3⟩ := hrest P l L j lam α β Lb c Ntot hH N hN
  exact ⟨h0, m2, h1, h2, h3, m3⟩

theorem theorem_P_of_parts : Formalism.FourierDecayAlt.MA.ThmPQOfParts := by
  intro hF hA hG P l L j lam α β Lb c Ntot hH N Y hN hB ε hε
  show cutoffEnergyForm P l j c ε (LE.plus (List.ofFn Y)) = _
  rw [hF P l L j lam α β Lb c Ntot hH N Y hN hB ε hε, hA P l L j lam α β Lb c Ntot hH N Y hN hB ε hε,
    hG P l L j lam α β Lb c Ntot hH N Y hN hB ε hε]
  rfl

theorem jacobi_norm : Formalism.FourierDecayAlt.MA.JnNorm := by
  intro P l L j lam α β Lb c Ntot
  simp only [LE.Sys.jn, LE.Sys.dens, LE.sq]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  refine Finset.sum_congr rfl fun a _ => ?_
  show (Wq P ω ^ 0 * ((1 : ℂ)).re) * ‖(j a : Qp P.r P.TT → ℂ) ω‖ ^ 2 = _
  simp

theorem lemma_model_of_parts : Formalism.FourierDecayAlt.MA.LemmaEModelOfParts := by
  intro hLE hC hSI hFI hRO hI1 hJL hTP hJn
  obtain ⟨CR, Cd, CP, hCR, hCd, hCP, hS⟩ := hSI
  have h7 : 0 ≤ 2 * Real.exp 1 * √(LE.C7 CR Cd CP) := by positivity
  refine ⟨64 * (1 + 2 * Real.exp 1 * √(LE.C7 CR Cd CP)), 6 * (64 * (1 + 2 * Real.exp 1 * √(LE.C7 CR Cd CP))),
    by positivity, by positivity, ?_⟩
  intro P l L j lam α β c Ntot hSet hD hA hE hN hI w hAdm hw
  set C₂ := 64 * (1 + 2 * Real.exp 1 * √(LE.C7 CR Cd CP)) with hC₂
  have hC2 : 64 ≤ C₂ := by rw [hC₂]; nlinarith
  have hN1 : (1 : ℝ) ≤ Ntot := by exact_mod_cast (by omega : 1 ≤ Ntot)
  have hr : (1 : ℝ) ≤ ((P.r : ℝ) + 1) ^ 2 := by
    have : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
    nlinarith
  obtain ⟨_, h2, h3⟩ := hC P.k P.r Ntot C₂ (6 * C₂) (β - α) hN (by linarith) le_rfl hI
  have hLb1 : (Ntot : ℝ) ≤ C₂ * Ntot * ((P.r : ℝ) + 1) ^ 2 := by
    have : (Ntot : ℝ) * 1 ≤ Ntot * (C₂ * ((P.r : ℝ) + 1) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith
    nlinarith
  have hLb2 : 2 < C₂ * Ntot * ((P.r : ℝ) + 1) ^ 2 := by
    have : (64 : ℝ) * 1 * 1 ≤ C₂ * Ntot * ((P.r : ℝ) + 1) ^ 2 := by
      apply mul_le_mul (mul_le_mul hC2 hN1 (by norm_num) (by linarith)) hr (by norm_num) (by positivity)
    linarith
  have hH : Hyps P l L j lam α β (C₂ * Ntot * ((P.r : ℝ) + 1) ^ 2) Ntot :=
    ⟨hSet, hD, hA, hE, hN, hLb1, hLb2, h2, h3⟩
  have key := hLE CR Cd CP hCR hCd hCP C₂ le_rfl (6 * C₂) le_rfl
    (sysQ P l L j lam α β (C₂ * Ntot * ((P.r : ℝ) + 1) ^ 2) c Ntot) hN rfl hI
    (hRO P l L j lam α β _ c Ntot hH) (hI1 P l L j lam α β _ c Ntot hH) (hJL P l L j lam α β _ c Ntot hH)
    (hTP P l L j lam α β _ c Ntot hH) (fun w hw hl => hS P l L j lam α β _ c Ntot hH w hw hl)
    (hFI P l L j lam α β _ c Ntot hH)
  have := key w hAdm hw
  rw [hJn P l L j lam α β _ c Ntot] at this
  exact this

theorem hypotheses_nonvacuous : Formalism.FourierDecayAlt.MA.HypsNonvacuous := MAx2.R2.hypsNonvacuous

theorem model_words : Formalism.FourierDecayAlt.MA.ModelWordsD := MAx2.R2.modelWordsD

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.MAx2

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.Wd

theorem wordS_pts : ∀ v : List (Bool × ℝ), (wordS v).map (fun lt => lt.pt) = v.map (fun x => ((x.2 : ℝ) : ℂ))
  | [] => rfl
  | x :: v => by
    simp only [wordS, List.map_cons, List.map_map]
    congr 1
    rw [← wordS_pts v]
    rfl

theorem plusWord_points (w : List ℝ) : (wordP w).map (fun lt => lt.pt) = w.map (fun Y => ((Y : ℝ) : ℂ)) := by
  unfold wordP
  rw [List.map_map]
  have := wordS_pts (LE.plus w)
  simp only [LE.plus, List.map_map] at this
  exact this

theorem mem_wordP {w : List ℝ} {a} (h : a ∈ wordP w) : ∃ Y ∈ w, a.pt = ((Y : ℝ) : ℂ) := by
  have : a.pt ∈ (wordP w).map (fun lt => lt.pt) := List.mem_map_of_mem h
  rw [plusWord_points, List.mem_map] at this
  obtain ⟨Y, hY, e⟩ := this
  exact ⟨Y, hY, e.symm⟩

theorem pairwise_wordP {w : List ℝ} (h : w.Pairwise fun Y Y' => 2 < |Y - Y'|) :
    (wordP w).Pairwise fun a a' => 2 < |a.pt.re - a'.pt.re| := by
  have h2 : ((wordP w).map (fun lt => lt.pt)).Pairwise fun z z' : ℂ => 2 < |z.re - z'.re| := by
    rw [plusWord_points, List.pairwise_map]
    refine h.imp fun {a b} hab => ?_
    simpa using hab
  rwa [List.pairwise_map] at h2

theorem famPos (P : M.Par) (l : ℕ) (L : R.LevelData (A P (DQ P)) P.r) (j : M.Ty P → SmQ P.r P.TT)
    (lam : Fin (P.k + 2 * P.r + 1) → ℝ) (α β Lb : ℝ) (c : LE.Cut) (Ntot : ℕ)
    (hH : Hyps P l L j lam α β Lb Ntot) (N : ℕ) (hN : N ≤ Ntot) :
    ((sysQ P l L j lam α β Lb c Ntot).fam N).Pos := by
  obtain ⟨⟨hOK, hl1, hlk, _, hu, hu', hαβ, hcut⟩, _, _, _, _, _, hL2, _, h6⟩ := hH
  have hBF := Formalism.FourierDecayAlt.P.boxes_fit (sysQ P l L j lam α β Lb c Ntot) hL2 h6
  have hTT : 0 < P.TT := mul_pos hOK.T_pos hOK.T'_pos
  refine ⟨fun ω => ?_, fun Y hY i => ?_⟩
  · show 0 < Complex.normSq ω.1.2 / (Complex.normSq ω.1.2 - P.TT)
    have h := ω.2.2
    exact div_pos (by linarith) (by linarith)
  · have hYbox : ∀ a : Fin N, Y a ∈ (sysQ P l L j lam α β Lb c Ntot).box (N - 1 - (a : ℕ)) := fun a => hY a
    have hYI : ∀ a : Fin N, Y a ∈ Set.Icc α β := fun a => by
      have hm : Y a ∈ Set.Icc (α + (β - α) / 3) (β - (β - α) / 3) :=
        hBF.1 (N - 1 - (a : ℕ)) (by show N - 1 - (a : ℕ) < Ntot; omega) (hYbox a)
      exact ⟨by have := hm.1; linarith, by have := hm.2; linarith⟩
    have hpw : (List.ofFn Y).Pairwise fun Y Y' => 2 < |Y - Y'| := by
      rw [List.pairwise_ofFn]
      intro a b hab
      have hab' : (a : ℕ) < b := hab
      have := hBF.2.1 (N - 1 - (b : ℕ)) (N - 1 - (a : ℕ)) (by omega) (Y b) (hYbox b) (Y a) (hYbox a)
      change Lb ≤ Y a - Y b at this
      rw [abs_of_pos (by linarith)]
      linarith
    have hcutw : ∀ a ∈ wordP (List.ofFn Y), a.pt.im = 0 ∧ I.OnCut P.u P.u' l a.pt.re := by
      intro a ha
      obtain ⟨Y', hY', e⟩ := mem_wordP ha
      rw [List.mem_ofFn] at hY'
      obtain ⟨b, rfl⟩ := hY'
      rw [e]
      exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; exact hcut _ (hYI b)⟩
    set ix := ixOf P (List.ofFn Y).length (cast (iota_len P N Y) i)
    have hπ := Formalism.FourierDecayAlt.P.types_interlace P hOK ix.2
    have hpos := Formalism.FourierDecayAlt.P.c_pos_truncated Formalism.FourierDecayAlt.P.interlacing_sign Formalism.FourierDecayAlt.P.q_positive_interlacing
      Formalism.FourierDecayAlt.P.q_positive_shift Formalism.FourierDecayAlt.P.cPos_true (Fin (List.ofFn Y).length) P.k P.u P.u'
      (M.rho P ix.2) l P.T P.T' (wordP (List.ofFn Y)) hl1 hlk hπ hOK.T_pos hOK.T'_pos hcutw
      (pairwise_wordP hpw) ix.1
    exact hpos.1

end Formalism.FourierDecayAlt.P.MAx2

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx2.Jet

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.P.MAx1.An
open scoped ComplexConjugate

noncomputable section

variable (P : M.Par)

def Gr (x : E P.r) : ℝ := (∏ l, Complex.normSq (x.1 l)) * (Complex.normSq x.2 - P.TT)

theorem normSq_smooth {f : E P.r → ℂ} (hf : ContDiff ℝ sm f) : ContDiff ℝ sm (fun x => Complex.normSq (f x)) := by
  have : (fun x => Complex.normSq (f x)) = fun x => (f x).re * (f x).re + (f x).im * (f x).im := by
    funext x; simp [Complex.normSq_apply]
  rw [this]
  have h1 : ContDiff ℝ sm fun x => (f x).re := Complex.reCLM.contDiff.comp hf
  have h2 : ContDiff ℝ sm fun x => (f x).im := Complex.imCLM.contDiff.comp hf
  exact (h1.mul h1).add (h2.mul h2)

theorem Gr_smooth : ContDiff ℝ sm (Gr P) := by
  unfold Gr
  refine ContDiff.mul ?_ ((normSq_smooth P contDiff_snd).sub contDiff_const)
  exact contDiff_prod fun l _ => normSq_smooth P ((contDiff_apply ℝ ℂ l).comp contDiff_fst)

theorem psi_smooth {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (n : ℕ) :
    ContDiff ℝ sm (iteratedDeriv n (fun u => φ (Real.exp u))) := by
  rw [iteratedDeriv_eq_iterate]; exact ContDiff.iterate_deriv n hφ

def Phi (φ : ℝ → ℝ) (n : ℕ) : SmQ P.r P.TT := toSm P (fun x => ((LE.ld n φ (Gq P x) : ℝ) : ℂ))

theorem phi_mem {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (n : ℕ) :
    (fun x : Qp P.r P.TT => ((LE.ld n φ (Gq P x) : ℝ) : ℂ)) ∈ smSub P.r P.TT := by
  have h1 : ContDiffOn ℝ sm (fun x => Real.log (Gr P x)) (Qset P.r P.TT) :=
    (Gr_smooth P).contDiffOn.log fun x hx => (Gq_pos P ⟨x, hx⟩).ne'
  have h2 : ContDiffOn ℝ sm
      (fun x => ((iteratedDeriv n (fun u => φ (Real.exp u)) (Real.log (Gr P x)) : ℝ) : ℂ)) (Qset P.r P.TT) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn ((psi_smooth hφ n).comp_contDiffOn h1)
  exact h2.congr fun x hx => by rw [ext_of_mem _ hx]; rfl

theorem ev_Phi {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (n : ℕ) (x : Qp P.r P.TT) :
    evQ P (Phi P φ n) x = ((LE.ld n φ (Gq P x) : ℝ) : ℂ) := by
  unfold Phi toSm; rw [dif_pos (phi_mem P hφ n)]; rfl

theorem G_mem : (fun x : Qp P.r P.TT => ((Gq P x : ℝ) : ℂ)) ∈ smSub P.r P.TT := by
  have h2 : ContDiffOn ℝ sm (fun x => ((Gr P x : ℝ) : ℂ)) (Qset P.r P.TT) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (Gr_smooth P).contDiffOn
  exact h2.congr fun x hx => by rw [ext_of_mem _ hx]; rfl

def GQ : SmQ P.r P.TT := ⟨_, G_mem P⟩

theorem GQ_unit : IsUnit (GQ P) := isUnit_of_ne _ fun q => by
  show ((Gq P q : ℝ) : ℂ) ≠ 0
  exact_mod_cast (Gq_pos P q).ne'

theorem ev_inverse (f : SmQ P.r P.TT) (hf : IsUnit f) (q : Qp P.r P.TT) :
    ((Ring.inverse f : SmQ P.r P.TT) : Qp P.r P.TT → ℂ) q = ((f : Qp P.r P.TT → ℂ) q)⁻¹ := by
  have h : ((f * Ring.inverse f : SmQ P.r P.TT) : Qp P.r P.TT → ℂ) q = 1 := by
    rw [Ring.mul_inverse_cancel f hf]; rfl
  exact eq_inv_of_mul_eq_one_right h

def kapG (v : M.Var P.r) : SmQ P.r P.TT := eulerQ v (GQ P) * Ring.inverse (GQ P)

theorem euler_Phi {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (n : ℕ) (v : M.Var P.r) :
    eulerQ v (Phi P φ n) = Phi P φ (n + 1) * kapG P v := by
  apply Subtype.ext; funext x
  have hG : HasFDerivAt (Gr P) (fderiv ℝ (Gr P) x.1) x.1 :=
    ((Gr_smooth P).differentiable (by simp [sm]) x.1).hasFDerivAt
  have hψ : HasDerivAt (iteratedDeriv n (fun u => φ (Real.exp u)))
      (iteratedDeriv (n + 1) (fun u => φ (Real.exp u)) (Real.log (Gr P x.1))) (Real.log (Gr P x.1)) := by
    rw [iteratedDeriv_succ]
    exact (((psi_smooth hφ n).differentiable (by simp [sm])) _).hasDerivAt
  have h1 := (hψ.comp _ (Real.hasDerivAt_log (Gq_pos P x).ne')).comp_hasFDerivAt x.1 hG
  have h2 := Complex.ofRealCLM.hasFDerivAt.comp x.1 h1
  have h3 := Complex.ofRealCLM.hasFDerivAt.comp x.1 hG
  have e1 : ext (Phi P φ n : Qp P.r P.TT → ℂ) =ᶠ[nhds x.1]
      (Complex.ofRealCLM ∘ ((iteratedDeriv n (fun u => φ (Real.exp u))) ∘ Real.log) ∘ Gr P) := by
    filter_upwards [(Qset_open _ _).mem_nhds x.2] with y hy
    rw [ext_of_mem _ hy]
    exact ev_Phi P hφ n ⟨y, hy⟩
  have e2 : ext (GQ P : Qp P.r P.TT → ℂ) =ᶠ[nhds x.1] (Complex.ofRealCLM ∘ Gr P) := by
    filter_upwards [(Qset_open _ _).mem_nhds x.2] with y hy
    rw [ext_of_mem _ hy]; rfl
  have hk : ((kapG P v : SmQ P.r P.TT) : Qp P.r P.TT → ℂ) x =
      coordE v x.1 * wirt v (ext (GQ P : Qp P.r P.TT → ℂ)) x.1 * ((Gr P x.1 : ℝ) : ℂ)⁻¹ := by
    show ((eulerQ v (GQ P) : SmQ P.r P.TT) : Qp P.r P.TT → ℂ) x *
      ((Ring.inverse (GQ P) : SmQ P.r P.TT) : Qp P.r P.TT → ℂ) x = _
    rw [ev_inverse P _ (GQ_unit P), eulerQ_apply]; rfl
  show ((eulerQ v (Phi P φ n) : SmQ P.r P.TT) : Qp P.r P.TT → ℂ) x =
    (Phi P φ (n + 1) : Qp P.r P.TT → ℂ) x * ((kapG P v : SmQ P.r P.TT) : Qp P.r P.TT → ℂ) x
  rw [hk, eulerQ_apply, wirt_congr v e1, wirt_congr v e2, wirt_eq, wirt_eq]
  simp only []
  rw [h2.fderiv, h3.fderiv]
  have e3 := ev_Phi P hφ (n + 1) x
  simp only [evQ] at e3
  rw [e3]
  simp only [WL_apply, ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.smul_apply,
    Complex.ofRealCLM_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_inv]
  have hGx : ((Gr P x.1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Gq_pos P x).ne'
  have hGG : Gq P x = Gr P x.1 := rfl
  unfold LE.ld
  rw [hGG]
  field_simp

def IsJ (F : (ℝ → ℝ) → SmQ P.r P.TT) : Prop :=
  ∃ (n : ℕ) (qs : Fin n → ℕ) (c : Fin n → SmQ P.r P.TT), ∀ φ, LE.SmoothLog φ → F φ = ∑ t, Phi P φ (qs t) * c t

theorem isJ_zero : IsJ P (fun _ => 0) := ⟨0, Fin.elim0, Fin.elim0, fun φ _ => by simp⟩

theorem isJ_add {F G : (ℝ → ℝ) → SmQ P.r P.TT} (hF : IsJ P F) (hG : IsJ P G) : IsJ P (fun φ => F φ + G φ) := by
  obtain ⟨n, qs, c, h⟩ := hF
  obtain ⟨m, qs', c', h'⟩ := hG
  refine ⟨n + m, Fin.append qs qs', Fin.append c c', fun φ hφ => ?_⟩
  beta_reduce
  rw [h φ hφ, h' φ hφ, Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

theorem isJ_smul (z : ℂ) {F : (ℝ → ℝ) → SmQ P.r P.TT} (hF : IsJ P F) : IsJ P (fun φ => z • F φ) := by
  obtain ⟨n, qs, c, h⟩ := hF
  refine ⟨n, qs, fun t => z • c t, fun φ hφ => ?_⟩
  beta_reduce
  rw [h φ hφ, Finset.smul_sum]
  simp [mul_smul_comm]

theorem isJ_mul (g : SmQ P.r P.TT) {F : (ℝ → ℝ) → SmQ P.r P.TT} (hF : IsJ P F) : IsJ P (fun φ => g * F φ) := by
  obtain ⟨n, qs, c, h⟩ := hF
  refine ⟨n, qs, fun t => g * c t, fun φ hφ => ?_⟩
  beta_reduce
  rw [h φ hφ, Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => by ring

theorem isJ_sum {ι : Type} (s : Finset ι) (F : ι → (ℝ → ℝ) → SmQ P.r P.TT) (h : ∀ i ∈ s, IsJ P (F i)) :
    IsJ P (fun φ => ∑ i ∈ s, F i φ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isJ_zero P
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact isJ_add P (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem isJ_euler (v : M.Var P.r) {F : (ℝ → ℝ) → SmQ P.r P.TT} (hF : IsJ P F) :
    IsJ P (fun φ => eulerQ v (F φ)) := by
  obtain ⟨n, qs, c, h⟩ := hF
  refine ⟨n + n, Fin.append (fun t => qs t + 1) qs, Fin.append (fun t => kapG P v * c t) (fun t => eulerQ v (c t)),
    fun φ hφ => ?_⟩
  beta_reduce
  rw [h φ hφ, map_sum, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Formalism.FourierDecayAlt.P.analytic_leibniz, euler_Phi P hφ]
  ring

def okSub : Subalgebra ℂ (Module.End ℂ (SmQ P.r P.TT)) where
  carrier := {T | ∀ F, IsJ P F → IsJ P (fun φ => T (F φ))}
  mul_mem' {a b} ha hb F hF := ha _ (hb F hF)
  add_mem' {a b} ha hb F hF := isJ_add P (ha F hF) (hb F hF)
  algebraMap_mem' z F hF := by
    show IsJ P (fun φ => (algebraMap ℂ (Module.End ℂ (SmQ P.r P.TT)) z) (F φ))
    simp only [Module.algebraMap_end_apply]
    exact isJ_smul P z hF

theorem mulOp_mem (g : SmQ P.r P.TT) : (DQ P).mulOp g ∈ okSub P := fun F hF => isJ_mul P g hF

theorem euler_mem (v : M.Var P.r) : (DQ P).ev v ∈ okSub P := fun F hF => isJ_euler P v hF

def prSub : Subalgebra ℂ (DQ P).Pr where
  carrier := {a | a.1 ∈ okSub P}
  mul_mem' {a b} ha hb := by show a.1 * b.1 ∈ okSub P; exact mul_mem ha hb
  add_mem' {a b} ha hb := by show a.1 + b.1 ∈ okSub P; exact add_mem ha hb
  algebraMap_mem' z := Subalgebra.algebraMap_mem (okSub P) z

theorem mem_prSub (a : (DQ P).Pr) : a ∈ prSub P ↔ a.1 ∈ okSub P := Iff.rfl

theorem gens_sub : (DQ P).gens P.TT ⊆ prSub P := by
  intro a ha
  simp only [DAlg.gens, Set.mem_union, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with ((((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | h)
  · exact mulOp_mem P _
  · exact mulOp_mem P _
  · exact mulOp_mem P _
  · exact mulOp_mem P _
  · exact euler_mem P _
  · exact euler_mem P _
  · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact mulOp_mem P _
    · exact mulOp_mem P _
    · exact mulOp_mem P _
    · exact mulOp_mem P _
    · exact mulOp_mem P _
    · exact mulOp_mem P _
    · exact mul_mem (mulOp_mem P _) (euler_mem P _)
    · exact mul_mem (mulOp_mem P _) (euler_mem P _)

end

end Formalism.FourierDecayAlt.P.MAx2.Jet

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx2.Jet

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr

noncomputable section

def matSub {R : Type} [Ring R] [Algebra ℂ R] (S : Subalgebra ℂ R) (n : Type) [Fintype n] [DecidableEq n] :
    Subalgebra ℂ (Matrix n n R) where
  carrier := {M | ∀ i j, M i j ∈ S}
  mul_mem' {a b} ha hb i j := by
    rw [Matrix.mul_apply]; exact Subalgebra.sum_mem _ fun k _ => mul_mem (ha i k) (hb k j)
  add_mem' {a b} ha hb i j := add_mem (ha i j) (hb i j)
  algebraMap_mem' z i j := by
    rw [Matrix.algebraMap_matrix_apply]
    split_ifs
    · exact S.algebraMap_mem z
    · exact S.zero_mem

section Gen
variable {R : Type} [Ring R] [Algebra ℂ R] (S : Subalgebra ℂ R) {n : Type} [Fintype n] [DecidableEq n]

theorem mem_matSub {M : Matrix n n R} : M ∈ matSub S n ↔ ∀ i j, M i j ∈ S := Iff.rfl

theorem diag_mem (d : n → R) (h : ∀ i, d i ∈ S) : Matrix.diagonal d ∈ matSub S n := fun i j => by
  rw [Matrix.diagonal_apply]; split_ifs
  · exact h i
  · exact S.zero_mem

theorem scalar_mem (x : R) (h : x ∈ S) : Matrix.scalar n x ∈ matSub S n := by
  rw [Matrix.scalar_apply]; exact diag_mem S _ fun _ => h

theorem matrix_two_mem_sub (a b c d : R) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S) :
    !![a, b; c, d] ∈ matSub S (Fin 2) := by
  intro i j; fin_cases i <;> fin_cases j <;> simpa

end Gen

variable (P : M.Par)

abbrev TS : Subalgebra ℂ (A P (DQ P)) := matSub (prSub P) (M.Ty P)

theorem gen_mem {a : (DQ P).Pr} (h : a ∈ (DQ P).gens P.TT) : a ∈ prSub P := gens_sub P h

theorem sc_mem {w : (DQ P).Pr} (h : w ∈ prSub P) : sc P (DQ P) w ∈ TS P := scalar_mem _ _ h

theorem kap_mem (f : M.Ty P → ℂ) : kap P (DQ P) f ∈ TS P :=
  diag_mem _ _ fun _ => Subalgebra.algebraMap_mem _ _

theorem SS_mem (i : ℕ) : SS P (DQ P) i ∈ TS P := fun π π' => by
  simp only [SS, Matrix.of_apply]
  split_ifs
  · exact Subalgebra.algebraMap_mem _ _
  · exact Subalgebra.zero_mem _

section Lev
variable {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L)
include hL

theorem lev_mem : (∀ l, L.p l ∈ TS P) ∧ (∀ l, L.pb l ∈ TS P) ∧ (∀ l, L.c l ∈ TS P) ∧ (∀ l, L.ci l ∈ TS P) ∧
    (∀ l, L.cb l ∈ TS P) ∧ (∀ l, L.cbi l ∈ TS P) ∧ L.ζ ∈ TS P ∧ L.ζi ∈ TS P ∧ L.ζb ∈ TS P ∧ L.ζbi ∈ TS P ∧
    L.GG ∈ TS P ∧ L.GGi ∈ TS P ∧ L.nab ∈ TS P ∧ L.nabs ∈ TS P := by
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hg, hgi, hn, hns, -⟩ := hL
  have gm : ∀ a ∈ (DQ P).gens P.TT, sc P (DQ P) a ∈ TS P := fun a ha => sc_mem P (gen_mem P ha)
  refine ⟨fun l => ?_, fun l => ?_, fun l => ?_, fun l => ?_, fun l => ?_, fun l => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hp]; exact gm _ (by simp [DAlg.gens])
  · rw [hpb]; exact gm _ (by simp [DAlg.gens])
  · rw [hc]; exact gm _ (by simp [DAlg.gens])
  · rw [hci]; exact gm _ (by simp [DAlg.gens])
  · rw [hcb]; exact gm _ (by simp [DAlg.gens])
  · rw [hcbi]; exact gm _ (by simp [DAlg.gens])
  · rw [hz]; exact gm _ (by simp [DAlg.gens])
  · rw [hzi]; exact gm _ (by simp [DAlg.gens])
  · rw [hzb]; exact gm _ (by simp [DAlg.gens])
  · rw [hzbi]; exact gm _ (by simp [DAlg.gens])
  · rw [hg]; exact gm _ (by simp [DAlg.gens])
  · rw [hgi]; exact gm _ (by simp [DAlg.gens])
  · rw [hn]
    refine diag_mem _ _ fun π => add_mem (gen_mem P (by simp [DAlg.gens])) (Subalgebra.smul_mem _
      (mul_mem (gen_mem P (by simp [DAlg.gens])) (gen_mem P (by simp [DAlg.gens]))) _)
  · rw [hns]
    refine diag_mem _ _ fun π => add_mem (neg_mem (gen_mem P (by simp [DAlg.gens]))) (Subalgebra.smul_mem _
      (mul_mem (gen_mem P (by simp [DAlg.gens])) (gen_mem P (by simp [DAlg.gens]))) _)

theorem Dr_mem : L.Dr ∈ TS P ∧ L.Drb ∈ TS P ∧ L.Dri ∈ TS P ∧ L.Drbi ∈ TS P := by
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, -⟩ := lev_mem P hL
  refine ⟨Subalgebra.list_prod_mem _ fun x hx => ?_, Subalgebra.list_prod_mem _ fun x hx => ?_,
    Subalgebra.list_prod_mem _ fun x hx => ?_, Subalgebra.list_prod_mem _ fun x hx => ?_⟩ <;>
  · obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx
    first | exact hc l | exact hcb l | exact hci l | exact hcbi l

theorem Tprod_mem (Y : ℂ) : L.Tprod Y ∈ matSub (TS P) (Fin 2) ∧ L.Tvprod Y ∈ matSub (TS P) (Fin 2) := by
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, -⟩ := lev_mem P hL
  refine ⟨Subalgebra.list_prod_mem _ fun x hx => ?_, Subalgebra.list_prod_mem _ fun x hx => ?_⟩
  · obtain ⟨l, rfl⟩ := List.mem_ofFn.1 (List.mem_reverse.1 hx)
    exact matrix_two_mem_sub _ _ _ _ _ (add_mem (Subalgebra.algebraMap_mem _ _) (hp l)) (neg_mem (hc l)) (hci l)
      (Subalgebra.zero_mem _)
  · obtain ⟨l, rfl⟩ := List.mem_ofFn.1 (List.mem_reverse.1 hx)
    exact matrix_two_mem_sub _ _ _ _ _ (sub_mem (Subalgebra.algebraMap_mem _ _) (hpb l)) (neg_mem (hcb l)) (hcbi l)
      (Subalgebra.zero_mem _)

theorem hat_mem (Y : ℂ) : L.Di * L.Ahat Y ∈ TS P ∧ L.Dbi * L.R0 Y ∈ TS P := by
  obtain ⟨-, -, -, -, -, -, hz, hzi, hzb, hzbi, hg, hgi, hn, hns⟩ := lev_mem P hL
  obtain ⟨d1, d2, d3, d4⟩ := Dr_mem P hL
  have hT := (Tprod_mem P hL Y).1
  have hA : L.Ar Y ∈ TS P := hT 0 0
  have hB : L.Br Y ∈ TS P := hT 1 0
  refine ⟨mul_mem (mul_mem hzi d3) (mul_mem d1 hA), mul_mem (mul_mem hzbi d4) (mul_mem (mul_mem d2 hg) (add_mem
    (mul_mem (sub_mem (neg_mem hn) (mul_mem (Subalgebra.algebraMap_mem _ _) (mul_mem hzb hgi))) hA) hB))⟩

end Lev

section SlopeTestRemainingChoices
variable {S : Type} [Fintype S] [DecidableEq S]

abbrev US (S : Type) [Fintype S] [DecidableEq S] : Subalgebra ℂ (SlopeTestRemainingChoices S (A P (DQ P))) := matSub (TS P) (Ix S)

theorem io_mem {x : A P (DQ P)} (h : x ∈ TS P) : (io x : SlopeTestRemainingChoices S (A P (DQ P))) ∈ US P S := scalar_mem _ _ h

theorem eU_mem (a : S) (i j : Fin 2) : (eU a i j : SlopeTestRemainingChoices S (A P (DQ P))) ∈ US P S := fun x y => by
  simp only [eU, Matrix.of_apply]
  split_ifs
  · exact Subalgebra.one_mem _
  · exact Subalgebra.zero_mem _

theorem ins_mem (a : S) (M : Matrix (Fin 2) (Fin 2) (SlopeTestRemainingChoices S (A P (DQ P)))) (h : ∀ i j, M i j ∈ US P S) :
    ins a M ∈ US P S :=
  Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ => mul_mem (eU_mem P a i j) (h i j)

theorem insert_matrix_mem (a : S) (x y z w : SlopeTestRemainingChoices S (A P (DQ P))) (hx : x ∈ US P S) (hy : y ∈ US P S) (hz : z ∈ US P S)
    (hw : w ∈ US P S) : ins a !![x, y; z, w] ∈ US P S :=
  ins_mem P a _ (matrix_two_mem_sub (US P S) x y z w hx hy hz hw)

theorem frame_mem (l : ℕ) {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L) :
    ∀ w : List (Letter ℂ S), (∀ Y, (ofWord L (startM P (DQ P) l) w).ee Y ∈ US P S) ∧
      (∀ Y, (ofWord L (startM P (DQ P) l) w).x Y ∈ US P S) ∧ (∀ Y, (ofWord L (startM P (DQ P) l) w).xi Y ∈ US P S)
  | [] => by
    obtain ⟨-, -, -, -, -, -, hz, hzi, hzb, hzbi, hg, hgi, hn, hns⟩ := lev_mem P hL
    refine ⟨fun Y => io_mem P ?_, fun Y => io_mem P (kap_mem P _), fun Y => io_mem P (kap_mem P _)⟩
    show eeA P (DQ P) Y ∈ TS P
    refine mul_mem (mul_mem (sc_mem P (gen_mem P (by simp [DAlg.gens]))) (sc_mem P (gen_mem P (by simp [DAlg.gens]))))
      (Subalgebra.sum_mem _ fun j _ => mul_mem (kap_mem P _) (SS_mem P j))
  | lt :: w => by
    obtain ⟨he, hx, hxi⟩ := frame_mem l hL w
    obtain ⟨-, -, -, -, -, -, hz, hzi, hzb, hzbi, hg, hgi, hn, hns⟩ := lev_mem P hL
    have htz : (tz L : SlopeTestRemainingChoices S (A P (DQ P))) ∈ US P S := io_mem P (Subalgebra.smul_mem _ hzbi _)
    have hDD : ∀ Y Ya, (ofWord L (startM P (DQ P) l) w).DD Y Ya ∈ US P S := fun Y Ya =>
      Subalgebra.smul_mem _ (sub_mem (he Y) (he Ya)) _
    have h1 : (1 : SlopeTestRemainingChoices S (A P (DQ P))) ∈ US P S := Subalgebra.one_mem _
    have h0 : (0 : SlopeTestRemainingChoices S (A P (DQ P))) ∈ US P S := Subalgebra.zero_mem _
    simp only [ofWord]
    split_ifs
    · refine ⟨fun Y => ?_, fun Y => ?_, fun Y => ?_⟩
      · exact insert_matrix_mem P _ _ _ _ _ (add_mem (sub_mem (he Y) (hDD Y _)) htz) (neg_mem (Subalgebra.smul_mem _ h1 _)) h0
          (mul_mem (mul_mem (hxi _) (he Y)) (hx _))
      · exact mul_mem (hx Y) (insert_matrix_mem P _ _ _ _ _ (Subalgebra.smul_mem _ h1 _) h0 h0 h1)
      · exact mul_mem (hxi Y) (insert_matrix_mem P _ _ _ _ _ (Subalgebra.smul_mem _ h1 _) h0 h0 h1)
    · refine ⟨fun Y => ?_, fun Y => ?_, fun Y => ?_⟩
      · exact insert_matrix_mem P _ _ _ _ _ (he Y) h0 (neg_mem (Subalgebra.smul_mem _ (mul_mem (hxi _) (hxi _)) _))
          (add_mem (sub_mem (mul_mem (mul_mem (hxi _) (he Y)) (hx _)) (hDD Y _)) htz)
      · exact mul_mem (hx Y) (insert_matrix_mem P _ _ _ _ _ (Subalgebra.smul_mem _ h1 _) h0 h0 h1)
      · exact mul_mem (hxi Y) (insert_matrix_mem P _ _ _ _ _ (Subalgebra.smul_mem _ h1 _) h0 h0 h1)

end SlopeTestRemainingChoices

theorem g_mem (l : ℕ) {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L) (w : List ℝ) (Y : ℝ) :
    g1 P L w Y ∈ US P (Fin w.length) ∧ g2 P l L w Y ∈ US P (Fin w.length) := by
  obtain ⟨h1, h2⟩ := hat_mem P hL (Y : ℂ)
  refine ⟨io_mem P h1, add_mem (io_mem P h2) (mul_mem ((frame_mem P l hL (wordP w)).1 _) (io_mem P h1))⟩

end

end Formalism.FourierDecayAlt.P.MAx2.Jet

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx2.Jet

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr

noncomputable section

variable (P : M.Par)

def JF (N : ℕ) (X : (ℝ → ℝ) → Qp P.r P.TT → Iota P N → ℂ) : Prop :=
  ∀ i, ∃ F : (ℝ → ℝ) → SmQ P.r P.TT, IsJ P F ∧ ∀ φ, LE.SmoothLog φ → ∀ x, X φ x i = evQ P (F φ) x

theorem toSm_ev (f : SmQ P.r P.TT) : toSm P (evQ P f) = f := by
  unfold toSm; rw [dif_pos (show evQ P f ∈ smSub P.r P.TT from f.2)]; rfl

theorem evQ_sum {ι : Type} (s : Finset ι) (f : ι → SmQ P.r P.TT) (x : Qp P.r P.TT) :
    evQ P (∑ i ∈ s, f i) x = ∑ i ∈ s, evQ P (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl

theorem evQ_mul (f g : SmQ P.r P.TT) (x : Qp P.r P.TT) : evQ P (f * g) x = evQ P f x * evQ P g x := rfl

theorem apply_matrix_jet_family {N : ℕ} (b : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) (hb : b ∈ US P (Fin N))
    {X : (ℝ → ℝ) → Qp P.r P.TT → Iota P N → ℂ} (hX : JF P N X) :
    JF P N (fun φ => wordModuleApply P b (X φ)) := by
  intro i
  choose F hF hXF using hX
  refine ⟨fun φ => ∑ e', ∑ π', ((b (ixOf P N i).1 e') (ixOf P N i).2 π').1 (F (iotaOf P N e' π') φ), ?_, ?_⟩
  · exact isJ_sum P _ _ fun e' _ => isJ_sum P _ _ fun π' _ => (hb _ _ _ _) _ (hF _)
  · intro φ hφ x
    have e : ∀ e' π', toSm P (fun q' => X φ q' (iotaOf P N e' π')) = F (iotaOf P N e' π') φ := fun e' π' => by
      have : (fun q' => X φ q' (iotaOf P N e' π')) = evQ P (F (iotaOf P N e' π') φ) := funext (hXF _ φ hφ)
      rw [this, toSm_ev]
    simp only [wordModuleApply, e]
    rw [evQ_sum]
    exact Finset.sum_congr rfl fun e' _ => (evQ_sum P _ _ x).symm

theorem gL_JF (l : ℕ) {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L) (w : List ℝ) (Y : ℝ)
    {X : (ℝ → ℝ) → Qp P.r P.TT → Iota P w.length → ℂ} (hX : JF P w.length X) :
    JF P (w.length + 1) (fun φ => gL P l L w Y (X φ)) := by
  rintro ⟨b, i⟩
  cases b
  · obtain ⟨F, hF, h⟩ := apply_matrix_jet_family P _ (g_mem P l hL w Y).1 hX i
    exact ⟨F, hF, fun φ hφ x => h φ hφ x⟩
  · obtain ⟨F, hF, h⟩ := apply_matrix_jet_family P _ (g_mem P l hL w Y).2 hX i
    exact ⟨F, hF, fun φ hφ x => h φ hφ x⟩

theorem Xw_JF (l : ℕ) {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L)
    {u : (ℝ → ℝ) → Qp P.r P.TT → M.Ty P → ℂ} (hu : JF P 0 u) :
    ∀ w : List ℝ, JF P w.length (fun φ => Xw P l L (u φ) w)
  | [] => hu
  | Y :: w => gL_JF P l hL w Y (Xw_JF l hL hu w)

theorem base_JF (j : M.Ty P → SmQ P.r P.TT) : JF P 0 (fun φ => LE.mulF (baseQ P) φ (ju P j)) := by
  intro π
  refine ⟨fun φ => Phi P φ 0 * j π, ⟨1, fun _ => 0, fun _ => j π, fun φ hφ => by simp⟩, fun φ hφ x => ?_⟩
  rw [evQ_mul, ev_Phi P hφ]
  simp only [LE.mulF, ju, LE.ld, iteratedDeriv_zero, Real.exp_log (Gq_pos P x)]
  rfl

theorem famJet (l : ℕ) (L : LevelData (A P (DQ P)) P.r) (hL : IsModelLevel P (DQ P) L) (j : M.Ty P → SmQ P.r P.TT)
    (lam : Fin (P.k + 2 * P.r + 1) → ℝ) (α β Lb : ℝ) (c : LE.Cut) (Ntot N : ℕ) :
    ((sysQ P l L j lam α β Lb c Ntot).fam N).Jet := by
  intro Y _
  have hX := Xw_JF P l hL (base_JF P j) (List.ofFn Y)
  have hJ : ∀ a : Iota P N, ∃ (n : ℕ) (qs : Fin n → ℕ) (cc : Fin n → SmQ P.r P.TT), ∀ φ, LE.SmoothLog φ →
      ∀ x, Xw P l L (LE.mulF (baseQ P) φ (ju P j)) (List.ofFn Y) x (cast (iota_len P N Y) a) =
        ∑ t, ((LE.ld (qs t) φ (Gq P x) : ℝ) : ℂ) * evQ P (cc t) x := by
    intro a
    obtain ⟨F, ⟨n, qs, cc, hF⟩, h⟩ := hX (cast (iota_len P N Y) a)
    refine ⟨n, qs, cc, fun φ hφ x => ?_⟩
    refine (h φ hφ x).trans ?_
    rw [hF φ hφ, evQ_sum]
    exact Finset.sum_congr rfl fun t _ => by rw [evQ_mul, ev_Phi P hφ]
  choose n qs cc hcc using hJ
  refine ⟨Finset.univ.sup fun a => Finset.univ.sup (qs a),
    fun q ω a => ∑ t ∈ Finset.univ.filter (fun t => qs a t = q), evQ P (cc a t) ω, fun φ hφ ω a => ?_⟩
  show Xw P l L (LE.mulF (baseQ P) φ (ju P j)) (List.ofFn Y) ω (cast (iota_len P N Y) a) = _
  rw [hcc a φ hφ ω]
  have hmaps : ∀ t ∈ (Finset.univ : Finset (Fin (n a))),
      qs a t ∈ Finset.range ((Finset.univ.sup fun a => Finset.univ.sup (qs a)) + 1) := fun t _ =>
    Finset.mem_range.2 (Nat.lt_succ_of_le ((Finset.le_sup (f := qs a) (Finset.mem_univ t)).trans
      (Finset.le_sup (f := fun a => Finset.univ.sup (qs a)) (Finset.mem_univ a))))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [(Finset.mem_filter.1 ht).2]
  rfl

end

end Formalism.FourierDecayAlt.P.MAx2.Jet

namespace Formalism.FourierDecayAlt.P

theorem family_restriction : Formalism.FourierDecayAlt.MA.FamRestQ := by
  intro P l L j lam α β Lb c Ntot hH N hN
  exact ⟨MAx2.famPos P l L j lam α β Lb c Ntot hH N hN,
    MAx2.Jet.famJet P l L hH.1.2.2.2.1 j lam α β Lb c Ntot N⟩

end Formalism.FourierDecayAlt.P

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx2.J0

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.P.MAx1.An MeasureTheory
open scoped ComplexConjugate

noncomputable section

variable {τ : ℝ}

abbrev S (τ : ℝ) := SmQ 0 τ
def z : S τ := coordQ M.vz
def zb : S τ := coordQ M.vzb
def zi : S τ := Ring.inverse z
def zbi : S τ := Ring.inverse zb
def gg : S τ := (anQ 0 τ).gg τ
def ggi : S τ := Ring.inverse gg
def th : Module.End ℂ (S τ) := eulerQ M.vz
def thb : Module.End ℂ (S τ) := eulerQ M.vzb

def ev (f : S τ) (q : Qp 0 τ) : ℂ := f.1 q

@[simp] theorem ev_mul (f g : S τ) (q) : ev (f * g) q = ev f q * ev g q := rfl
@[simp] theorem ev_add (f g : S τ) (q) : ev (f + g) q = ev f q + ev g q := rfl
@[simp] theorem ev_sub (f g : S τ) (q) : ev (f - g) q = ev f q - ev g q := rfl
@[simp] theorem ev_neg (f : S τ) (q) : ev (-f) q = -ev f q := rfl
@[simp] theorem ev_smul (c : ℂ) (f : S τ) (q) : ev (c • f) q = c * ev f q := rfl
@[simp] theorem ev_one (q) : ev (1 : S τ) q = 1 := rfl
@[simp] theorem ev_zero (q) : ev (0 : S τ) q = 0 := rfl
@[simp] theorem ev_sum {ι : Type} (s : Finset ι) (f : ι → S τ) (q) : ev (∑ i ∈ s, f i) q = ∑ i ∈ s, ev (f i) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, ev_add, ih, Finset.sum_insert ha]
theorem S_ext {f g : S τ} (h : ∀ q, ev f q = ev g q) : f = g := Subtype.ext (funext h)

theorem eval_zeta (q) : ev (z : S τ) q = q.1.2 := coordE_vz q.1
theorem ev_zb (q) : ev (zb : S τ) q = conj q.1.2 := coordE_vzb q.1
theorem ev_gg (q) : ev (gg : S τ) q = q.1.2 * conj q.1.2 - τ := by
  have := gg_apply (r := 0) (TT := τ) q
  rw [coordE_vz, coordE_vzb] at this
  exact this

theorem laws (hτ : 0 ≤ τ) : (anQ 0 τ).Laws τ := Formalism.FourierDecayAlt.P.analytic_laws 0 τ hτ

theorem z_ne (hτ : 0 ≤ τ) (q : Qp 0 τ) : q.1.2 ≠ 0 := by
  intro h
  have h2 : τ < Complex.normSq q.1.2 := q.2.2
  rw [h, Complex.normSq_zero] at h2
  linarith

theorem ev_inv (f : S τ) (hf : IsUnit f) (q) : ev (Ring.inverse f) q = (ev f q)⁻¹ := by
  have h : ev (f * Ring.inverse f) q = 1 := by rw [Ring.mul_inverse_cancel f hf]; rfl
  rw [ev_mul] at h
  exact (eq_inv_of_mul_eq_one_right h)

theorem ev_zi (hτ : 0 ≤ τ) (q) : ev (zi : S τ) q = (q.1.2)⁻¹ := by
  rw [zi, ev_inv z ((laws hτ).unit_alt_bis M.vz), eval_zeta]
theorem ev_zbi (hτ : 0 ≤ τ) (q) : ev (zbi : S τ) q = (conj q.1.2)⁻¹ := by
  rw [zbi, ev_inv zb ((laws hτ).unit_alt_bis M.vzb), ev_zb]
theorem ev_ggi (hτ : 0 ≤ τ) (q) : ev (ggi : S τ) q = (q.1.2 * conj q.1.2 - τ)⁻¹ := by
  rw [ggi, ev_inv gg (laws hτ).unit_gg, ev_gg]
theorem gg_ne' (q : Qp 0 τ) : q.1.2 * conj q.1.2 - τ ≠ 0 := by
  rw [← ev_gg]; exact gg_ne (r := 0) (TT := τ) q

def GR (q : Qp 0 τ) : ℝ := Complex.normSq q.1.2 - τ

theorem GR_pos (q : Qp 0 τ) : 0 < GR q := sub_pos.2 q.2.2

theorem ev_gg_re (q : Qp 0 τ) : ev (gg : S τ) q = ((GR q : ℝ) : ℂ) := by
  rw [ev_gg, Complex.mul_conj, GR]; push_cast; ring

theorem GR_le (hτ : 0 ≤ τ) (q : Qp 0 τ) : GR q ≤ ‖q.1.2‖ ^ 2 := by
  rw [GR, Complex.normSq_eq_norm_sq]; linarith

theorem th_mul (f g : S τ) : th (f * g) = th f * g + f * th g := Formalism.FourierDecayAlt.P.analytic_leibniz 0 τ _ f g
theorem thb_mul (f g : S τ) : thb (f * g) = thb f * g + f * thb g := Formalism.FourierDecayAlt.P.analytic_leibniz 0 τ _ f g
theorem theta_zeta : th (z : S τ) = z := by
  have := Formalism.FourierDecayAlt.P.analytic_coordinates 0 τ M.vz M.vz; rwa [if_pos rfl] at this
theorem th_zb : th (zb : S τ) = 0 := by
  have := Formalism.FourierDecayAlt.P.analytic_coordinates 0 τ M.vz M.vzb; rwa [if_neg Formalism.FourierDecayAlt.P.MAx1.vz_ne] at this
theorem theta_bar_zeta : thb (z : S τ) = 0 := by
  have := Formalism.FourierDecayAlt.P.analytic_coordinates 0 τ M.vzb M.vz; rwa [if_neg Formalism.FourierDecayAlt.P.MAx1.vz_ne.symm] at this
theorem thb_zb : thb (zb : S τ) = zb := by
  have := Formalism.FourierDecayAlt.P.analytic_coordinates 0 τ M.vzb M.vzb; rwa [if_pos rfl] at this
theorem th_zi (hτ : 0 ≤ τ) : th (zi : S τ) = -zi := by
  have := Formalism.FourierDecayAlt.P.MAx1.eci (laws hτ) M.vz M.vz; rwa [if_pos rfl] at this
theorem th_zbi (hτ : 0 ≤ τ) : th (zbi : S τ) = 0 := by
  have := Formalism.FourierDecayAlt.P.MAx1.eci (laws hτ) M.vz M.vzb; rwa [if_neg Formalism.FourierDecayAlt.P.MAx1.vz_ne] at this
theorem thb_zi (hτ : 0 ≤ τ) : thb (zi : S τ) = 0 := by
  have := Formalism.FourierDecayAlt.P.MAx1.eci (laws hτ) M.vzb M.vz; rwa [if_neg Formalism.FourierDecayAlt.P.MAx1.vz_ne.symm] at this
theorem thb_zbi (hτ : 0 ≤ τ) : thb (zbi : S τ) = -zbi := by
  have := Formalism.FourierDecayAlt.P.MAx1.eci (laws hτ) M.vzb M.vzb; rwa [if_pos rfl] at this
theorem th_gg (hτ : 0 ≤ τ) : th (gg : S τ) = z * zb := Formalism.FourierDecayAlt.P.MAx1.euler_GG_z (laws hτ)
theorem thb_gg (hτ : 0 ≤ τ) : thb (gg : S τ) = z * zb := Formalism.FourierDecayAlt.P.MAx1.euler_gg_zb (laws hτ)
theorem th_one (hτ : 0 ≤ τ) : th (1 : S τ) = 0 := Formalism.FourierDecayAlt.P.MAx1.ev_one (laws hτ) M.vz
theorem thb_one (hτ : 0 ≤ τ) : thb (1 : S τ) = 0 := Formalism.FourierDecayAlt.P.MAx1.ev_one (laws hτ) M.vzb
theorem th_const (hτ : 0 ≤ τ) (c : ℂ) : th (c • (1 : S τ)) = 0 := by rw [map_smul, th_one hτ, smul_zero]
theorem thb_const (hτ : 0 ≤ τ) (c : ℂ) : thb (c • (1 : S τ)) = 0 := by rw [map_smul, thb_one hτ, smul_zero]

theorem ext_conj (f : Qp 0 τ → ℂ) : ext (fun q => conj (f q)) = fun x => Complex.conjCLE (ext f x) := by
  funext x; by_cases hx : x ∈ Qset 0 τ <;> simp [ext, hx]

def cj (f : S τ) : S τ := ⟨fun q => conj (f.1 q), by
  show ContDiffOn ℝ sm (ext fun q => conj (f.1 q)) (Qset 0 τ)
  rw [ext_conj]
  exact Complex.conjCLE.contDiff.comp_contDiffOn f.2⟩

@[simp] theorem ev_cj (f : S τ) (q) : ev (cj f) q = conj (ev f q) := rfl

theorem direction_zeta : dirE (M.vz : M.Var 0) = (0, 1) := by simp [dirE, M.vz]
theorem dir_zb : dirE (M.vzb : M.Var 0) = (0, 1) := by simp [dirE, M.vzb]

theorem wirt_alt (F : E 0 → ℂ) (x) : wirt M.vz F x =
    (1 / 2 : ℂ) * (fderiv ℝ F x (0, 1) - Complex.I * fderiv ℝ F x (Complex.I • ((0, 1) : E 0))) := by
  rw [wirt, direction_zeta, if_pos (by simp [M.vz])]; ring
theorem wirt_zb (F : E 0 → ℂ) (x) : wirt M.vzb F x =
    (1 / 2 : ℂ) * (fderiv ℝ F x (0, 1) + Complex.I * fderiv ℝ F x (Complex.I • ((0, 1) : E 0))) := by
  rw [wirt, dir_zb, if_neg (by simp [M.vzb])]

theorem ev_th (f : S τ) (q) : ev (th f) q = q.1.2 * wirt M.vz (ext f.1) q.1 := by
  rw [← coordE_vz]; rfl
theorem ev_thb (f : S τ) (q) : ev (thb f) q = conj q.1.2 * wirt M.vzb (ext f.1) q.1 := by
  rw [← coordE_vzb]; rfl

theorem fd_conj (f : S τ) (q : Qp 0 τ) (e : E 0) :
    fderiv ℝ (ext (cj f).1) q.1 e = conj (fderiv ℝ (ext f.1) q.1 e) := by
  have : ext (cj f).1 = Complex.conjCLE ∘ ext f.1 := ext_conj f.1
  rw [this, ContinuousLinearEquiv.comp_fderiv]
  simp

theorem th_cj (f : S τ) : th (cj f) = cj (thb f) := S_ext fun q => by
  rw [ev_cj, ev_th, ev_thb, wirt_alt, wirt_zb, fd_conj, fd_conj]
  simp only [map_mul, map_add, Complex.conj_conj, Complex.conj_I, map_div₀, map_one, map_ofNat]
  ring
theorem thb_cj (f : S τ) : thb (cj f) = cj (th f) := S_ext fun q => by
  rw [ev_cj, ev_th, ev_thb, wirt_alt, wirt_zb, fd_conj, fd_conj]
  simp only [map_mul, map_sub, Complex.conj_conj, Complex.conj_I, map_div₀, map_one, map_ofNat]
  ring

theorem cj_mul (f g : S τ) : cj (f * g) = cj f * cj g := S_ext fun q => by simp
theorem cj_add (f g : S τ) : cj (f + g) = cj f + cj g := S_ext fun q => by simp
theorem cj_gg : cj (gg : S τ) = gg := S_ext fun q => by simp [ev_gg, mul_comm]

instance haarE : (volume : Measure (E 0)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure (volume : Measure (Fin 0 → ℂ)) (volume : Measure ℂ)

theorem ringSpec_normalisedCharacter_eq : mu0 0 τ = Measure.comap Subtype.val (volume : Measure (E 0)) := by
  have : (dens0 : E 0 → ENNReal) = 1 := by funext x; simp [dens0]
  rw [mu0, this, withDensity_one]

theorem ext_val (f : Qp 0 τ → ℂ) (q : Qp 0 τ) : ext f q.1 = f q := ext_of_mem f q.2

theorem int_ext (f : S τ) : ∫ q, ev f q ∂mu0 0 τ = ∫ x, ext f.1 x := by
  rw [ringSpec_normalisedCharacter_eq, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Qset 0 τ) (fun x hx => by simp [ext, hx]),
    ← integral_subtype_comap (Qset_open 0 τ).measurableSet]
  congr 1; funext q; exact (ext_val _ q).symm

theorem integrable_ext_of {f : S τ} (hf : Integrable (ev f) (mu0 0 τ)) : Integrable (ext f.1) := by
  rw [ringSpec_normalisedCharacter_eq] at hf
  have h1 : IntegrableOn (ext f.1) (Qset 0 τ) := by
    rw [integrableOn_iff_comap_subtypeVal (Qset_open 0 τ).measurableSet]
    exact hf.congr (Filter.Eventually.of_forall fun q => (ext_val _ q).symm)
  exact (integrableOn_iff_integrable_of_support_subset (fun x hx => by
    by_contra h; exact hx (by simp [ext, h]))).1 h1

theorem ev_zero_near {h : S τ} {ε : ℝ} (hε : 0 < ε) (h0 : ∀ q : Qp 0 τ, Complex.normSq q.1.2 - τ ≤ ε → ev h q = 0)
    {x : E 0} (hx : x ∉ Qset 0 τ) : ext h.1 =ᶠ[nhds x] fun _ => 0 := by
  have hx' : Complex.normSq x.2 - τ < ε := by
    have : ¬ τ < Complex.normSq x.2 := fun h' => hx ⟨fun l => l.elim0, h'⟩
    linarith [not_lt.1 this]
  have ho : IsOpen {y : E 0 | Complex.normSq y.2 - τ < ε} :=
    isOpen_lt ((Complex.continuous_normSq.comp continuous_snd).sub continuous_const) continuous_const
  filter_upwards [ho.mem_nhds hx'] with y hy
  by_cases hy' : y ∈ Qset 0 τ
  · rw [ext_of_mem _ hy']; exact h0 ⟨y, hy'⟩ (le_of_lt hy)
  · simp [ext, hy']

theorem ibp (hτ : 0 ≤ τ) {h : S τ} {ε : ℝ} (hε : 0 < ε)
    (h0 : ∀ q : Qp 0 τ, Complex.normSq q.1.2 - τ ≤ ε → ev h q = 0)
    (b0 : Integrable (ev h) (mu0 0 τ)) (a1 : Integrable (ev (zi * th h)) (mu0 0 τ))
    (a2 : Integrable (ev (zbi * thb h)) (mu0 0 τ)) :
    ∫ q, ev (zi * th h) q ∂mu0 0 τ = 0 ∧ ∫ q, ev (zbi * thb h) q ∂mu0 0 τ = 0 := by
  have hd : ∀ x, DifferentiableAt ℝ (ext h.1) x := fun x => by
    by_cases hx : x ∈ Qset 0 τ
    · exact ext_smooth_diff h.2 x hx
    · exact (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq (ev_zero_near hε h0 hx)
  have e1 : ∀ q : Qp 0 τ, ev (zi * th h) q = wirt M.vz (ext h.1) q.1 := fun q => by
    rw [ev_mul, ev_zi hτ, ev_th, inv_mul_cancel_left₀ (z_ne hτ q)]
  have e2 : ∀ q : Qp 0 τ, ev (zbi * thb h) q = wirt M.vzb (ext h.1) q.1 := fun q => by
    rw [ev_mul, ev_zbi hτ, ev_thb, inv_mul_cancel_left₀ ((map_ne_zero _).2 (z_ne hτ q))]
  have key : ∀ (g : S τ) (e : E 0), Integrable (ev g) (mu0 0 τ) →
      (∀ q : Qp 0 τ, ev g q = fderiv ℝ (ext h.1) q.1 e) → ∫ q, ev g q ∂mu0 0 τ = 0 := by
    intro g e hg hge
    have hfe : (fun x => fderiv ℝ (ext h.1) x e) = ext g.1 := by
      funext x
      by_cases hx : x ∈ Qset 0 τ
      · rw [ext_of_mem _ hx]; exact (hge ⟨x, hx⟩).symm
      · rw [(ev_zero_near hε h0 hx).fderiv_eq]; simp [ext, hx]
    have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (E 0)))
      (f := fun _ => (1 : ℂ)) (g := ext h.1) (v := e) (by simp)
      (by simp only [one_mul]; rw [hfe]; exact integrable_ext_of hg)
      (by simp only [one_mul]; exact integrable_ext_of b0) (fun x _ => differentiableAt_const _) (fun x _ => hd x)
    simp only [one_mul] at this
    rw [hfe] at this
    rw [int_ext, this]; simp
  have k1 := key (zi * th h + zbi * thb h) (0, 1) ((a1.add a2).congr (Filter.Eventually.of_forall fun q => rfl)) fun q => by
    rw [ev_add, e1, e2, wirt_alt, wirt_zb]; ring
  have k2 := key (Complex.I • (zi * th h - zbi * thb h)) (Complex.I • ((0, 1) : E 0))
    (((a1.sub a2).const_mul Complex.I).congr (Filter.Eventually.of_forall fun q => rfl)) fun q => by
    rw [ev_smul, ev_sub, e1, e2, wirt_alt, wirt_zb]
    linear_combination (-fderiv ℝ (ext h.1) q.1 (Complex.I • ((0, 1) : E 0))) * Complex.I_mul_I
  simp only [ev_add, ev_smul, ev_sub] at k1 k2
  rw [integral_add a1 a2] at k1
  rw [integral_const_mul, integral_sub a1 a2] at k2
  have k3 := (mul_eq_zero.1 k2).resolve_left Complex.I_ne_zero
  constructor
  · linear_combination (1 / 2 : ℂ) * k1 + (1 / 2 : ℂ) * k3
  · linear_combination (1 / 2 : ℂ) * k1 - (1 / 2 : ℂ) * k3

theorem ev_cont (f : S τ) : Continuous (ev f) := by
  have h1 := (continuousOn_iff_continuous_domRestrict.1
    ((f.2 : ContDiffOn ℝ sm (ext f.1) (Qset 0 τ)).continuousOn))
  exact h1.congr fun q => ext_val _ q

theorem ev_aesm (f : S τ) : AEStronglyMeasurable (ev f) (mu0 0 τ) := (ev_cont f).aestronglyMeasurable

def L2 (f : S τ) : Prop := MemLp (ev f) 2 (mu0 0 τ)

theorem L2.add {f g : S τ} (hf : L2 f) (hg : L2 g) : L2 (f + g) := MemLp.add hf hg
theorem L2.sub {f g : S τ} (hf : L2 f) (hg : L2 g) : L2 (f - g) := MemLp.sub hf hg
theorem L2.neg {f : S τ} (hf : L2 f) : L2 (-f) := MemLp.neg hf
theorem L2.smul {f : S τ} (c : ℂ) (hf : L2 f) : L2 (c • f) := MemLp.const_mul hf c
theorem L2.zero : L2 (0 : S τ) := by
  show MemLp (fun _ => (0 : ℂ)) 2 (mu0 0 τ); exact MemLp.zero
theorem L2.sum {ι : Type} (s : Finset ι) (f : ι → S τ) (h : ∀ i ∈ s, L2 (f i)) : L2 (∑ i ∈ s, f i) :=
  Finset.sum_induction f L2 (fun _ _ => L2.add) L2.zero h

theorem L2.of_le {f : S τ} {g : Qp 0 τ → ℝ} (hg : MemLp g 2 (mu0 0 τ)) (h : ∀ q, ‖ev f q‖ ≤ g q) : L2 f :=
  hg.of_le (ev_aesm f) (Filter.Eventually.of_forall fun q => (h q).trans (le_abs_self _))

theorem L2.of_le' {f g : S τ} (hg : L2 g) (C : ℝ) (h : ∀ q, ‖ev f q‖ ≤ C * ‖ev g q‖) : L2 f :=
  L2.of_le (g := fun q => C * ‖ev g q‖) ((MemLp.norm hg).const_mul C) h

theorem L2.conjf {f : S τ} (hf : L2 f) : L2 (cj f) :=
  L2.of_le' hf 1 fun q => by simp

theorem L2.integrable_mul {f g : S τ} (hf : L2 f) (hg : L2 g) : Integrable (ev (f * g)) (mu0 0 τ) :=
  MemLp.integrable_mul (p := 2) (q := 2) hf hg

theorem L2.integrable_mul_cj {f g : S τ} (hf : L2 f) (hg : L2 g) : Integrable (ev (f * cj g)) (mu0 0 τ) :=
  L2.integrable_mul hf (L2.conjf hg)

end

end Formalism.FourierDecayAlt.P.MAx2.J0

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx2.J0

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.MAx1.An MeasureTheory Finset
open scoped ComplexConjugate

noncomputable section

section Act
variable (P : M.Par)

def Phi : (DQ P).Pr →+* Module.End ℂ (SmQ P.r P.TT) :=
  RingHom.fst (Module.End ℂ (SmQ P.r P.TT)) (Module.End ℂ (SmQ P.r P.TT))ᵐᵒᵖ
theorem actA_eq (a : A P (DQ P)) (f π) : actA P a f π = ∑ π', Phi P (a π π') (f π') := rfl

theorem act_mul (a b : A P (DQ P)) (f) : actA P (a * b) f = actA P a (actA P b f) := by
  funext π
  simp only [actA_eq, Matrix.mul_apply, map_sum, map_mul, LinearMap.sum_apply, Module.End.mul_apply]
  rw [Finset.sum_comm]
theorem act_diag (d : M.Ty P → (DQ P).Pr) (f π) : actA P (Matrix.diagonal d) f π = (d π).1 (f π) := by
  rw [actA_eq, Finset.sum_eq_single π (fun b _ hb => by rw [Matrix.diagonal_apply_ne _ hb.symm, map_zero]; rfl)
    (by simp), Matrix.diagonal_apply_eq]
  rfl
theorem act_one (f) : actA P 1 f = f := by
  funext π; rw [← Matrix.diagonal_one, act_diag]; rfl
theorem act_sub (a b : A P (DQ P)) (f π) : actA P (a - b) f π = actA P a f π - actA P b f π := by
  simp only [actA_eq, Matrix.sub_apply, map_sub, LinearMap.sub_apply, Finset.sum_sub_distrib]
theorem act_neg (a : A P (DQ P)) (f π) : actA P (-a) f π = -actA P a f π := by
  simp only [actA_eq, Matrix.neg_apply, map_neg, LinearMap.neg_apply, Finset.sum_neg_distrib]
theorem act_sc (w : (DQ P).Pr) (f π) : actA P (sc P (DQ P) w) f π = w.1 (f π) := act_diag P _ f π
theorem alg_fst (c : ℂ) (g : SmQ P.r P.TT) : (algebraMap ℂ (DQ P).Pr c).1 g = c • g := rfl
theorem act_alg (c : ℂ) (f π) : actA P (algebraMap ℂ (A P (DQ P)) c) f π = c • f π := by
  rw [Matrix.algebraMap_eq_diagonal, act_diag]; rfl
end Act

section R0
variable {B : Type} [Ring B] [Algebra ℂ B] (L : LevelData B 0)
theorem Dr0 : L.Dr = 1 := by simp [LevelData.Dr]
theorem Drb0 : L.Drb = 1 := by simp [LevelData.Drb]
theorem Dri0 : L.Dri = 1 := by simp [LevelData.Dri]
theorem Drbi0 : L.Drbi = 1 := by simp [LevelData.Drbi]
theorem Ahat0 (y) : L.Ahat y = 1 := by simp [LevelData.Ahat, LevelData.Dr, LevelData.Ar, LevelData.Tprod]
theorem Ahatv0 (y) : L.Ahatv y = 1 := by simp [LevelData.Ahatv, LevelData.Drb, LevelData.Avr, LevelData.Tvprod]
theorem raising_eq_gamma_lowering (y) : L.R0 y = L.GG * L.l0 y := by
  simp [LevelData.R0, LevelData.Drb, LevelData.Ar, LevelData.Br, LevelData.Tprod]
theorem R0v0 (y) : L.R0v y = L.GG * L.m0 y := by
  simp [LevelData.R0v, LevelData.Dr, LevelData.Avr, LevelData.Bvr, LevelData.Tvprod]
end R0

variable {τ : ℝ}

def opR (c : ℂ) (f : S τ) : S τ := -(gg * (zi * th f)) - c • (zb * f)
def opRs (c : ℂ) (g : S τ) : S τ := zbi * thb (gg * g) - conj c • (z * g)
def opV (c : ℂ) (f : S τ) : S τ := gg * (zbi * thb f) - c • (z * f)
def opVs (c : ℂ) (g : S τ) : S τ := -(zi * th (gg * g)) - conj c • (zb * g)

abbrev Pz (k : ℕ) (T T' : ℝ) (uu uu' : ℕ → ℝ) : M.Par := ⟨k, 0, T, T', uu, uu'⟩

variable {k : ℕ} {T T' : ℝ} {uu uu' : ℕ → ℝ}

local notation "PP" => Pz k T T' uu uu'

theorem nab_act (f π) : actA PP (nabA PP (DQ PP)) f π = zi * th (f π) + (M.aC PP π : ℂ) • (zb * (ggi * f π)) := by
  rw [nabA, act_diag]; rfl
theorem nabs_act (f π) : actA PP (nabsA PP (DQ PP)) f π =
    -(zbi * thb (f π)) + (M.aC PP π : ℂ) • (z * (ggi * f π)) := by
  rw [nabsA, act_diag]; rfl
theorem z_act (f π) : actA PP (zA PP (DQ PP)) f π = z * f π := act_sc _ _ _ _
theorem zb_act (f π) : actA PP (zbA PP (DQ PP)) f π = zb * f π := act_sc _ _ _ _
theorem gg_act (f π) : actA PP (ggA PP (DQ PP)) f π = gg * f π := act_sc _ _ _ _
theorem ggi_act (f π) : actA PP (ggiA PP (DQ PP)) f π = ggi * f π := act_sc _ _ _ _

theorem raising_action {L : LevelData (A PP (DQ PP)) 0} (hL : IsModelLevel PP (DQ PP) L) (hτ : 0 ≤ (PP).TT) (y f π) : actA PP (L.R0 y) f π = opR ((M.aC PP π : ℂ) + (y + 1 / 2)) (f π) := by
  obtain ⟨-, -, -, -, -, -, hz, hzi, hzb, hzbi, hg, hgi, hn, hns, -⟩ := hL
  rw [raising_eq_gamma_lowering, LevelData.l0, hg, hn, hzb, hgi]
  simp only [act_mul, act_sub, act_neg, act_alg, gg_act, nab_act, zb_act, ggi_act]
  refine S_ext fun q => ?_
  have := gg_ne' q
  simp only [opR, ev_mul, ev_sub, ev_add, ev_neg, ev_smul, ev_gg, ev_ggi hτ]
  field_simp
  ring

theorem raising_variant_action {L : LevelData (A PP (DQ PP)) 0} (hL : IsModelLevel PP (DQ PP) L) (hτ : 0 ≤ (PP).TT) (y f π) : actA PP (L.R0v y) f π = opV ((M.aC PP π : ℂ) + (y - 1 / 2)) (f π) := by
  obtain ⟨-, -, -, -, -, -, hz, hzi, hzb, hzbi, hg, hgi, hn, hns, -⟩ := hL
  rw [R0v0, LevelData.m0, hg, hns, hz, hgi]
  simp only [act_mul, act_sub, act_neg, act_alg, gg_act, nabs_act, z_act, ggi_act]
  refine S_ext fun q => ?_
  have := gg_ne' q
  simp only [opV, ev_mul, ev_sub, ev_add, ev_neg, ev_smul, ev_gg, ev_ggi hτ]
  field_simp
  ring

theorem raising_star_action {L : LevelData (A PP (DQ PP)) 0} (hL : IsModelLevel PP (DQ PP) L) (hτ : 0 ≤ (PP).TT) (y f π) : actA PP (star (L.R0 y)) f π = opRs ((M.aC PP π : ℂ) + (y + 1 / 2)) (f π) := by
  have : Fact ((DQ PP).Laws (PP).TT) := ⟨laws hτ⟩
  obtain ⟨-, s1, s2, s3, s4, s5⟩ := Formalism.FourierDecayAlt.P.MAx1.starGens PP (DQ PP)
  obtain ⟨-, -, -, -, -, -, hz, hzi, hzb, hzbi, hg, hgi, hn, hns, -⟩ := hL
  have s6 : star (zbA PP (DQ PP)) = zA PP (DQ PP) := by rw [← s1, star_star]
  rw [raising_eq_gamma_lowering, LevelData.l0, hg, hn, hzb, hgi]
  simp only [star_mul, star_sub, star_neg, s3, s4, s5, s6, ← algebraMap_star_comm]
  simp only [act_mul, act_sub, act_neg, act_alg, gg_act, nabs_act, z_act, ggi_act]
  refine S_ext fun q => ?_
  have := gg_ne' q
  simp only [opRs, ev_mul, ev_sub, ev_add, ev_neg, ev_smul, ev_gg, ev_ggi hτ, map_add, Complex.conj_ofReal,
    Complex.star_def]
  field_simp
  ring

theorem R0vs_act {L : LevelData (A PP (DQ PP)) 0} (hL : IsModelLevel PP (DQ PP) L) (hτ : 0 ≤ (PP).TT) (y f π) : actA PP (star (L.R0v y)) f π = opVs ((M.aC PP π : ℂ) + (y - 1 / 2)) (f π) := by
  have : Fact ((DQ PP).Laws (PP).TT) := ⟨laws hτ⟩
  obtain ⟨-, s1, s2, s3, s4, s5⟩ := Formalism.FourierDecayAlt.P.MAx1.starGens PP (DQ PP)
  obtain ⟨-, -, -, -, -, -, hz, hzi, hzb, hzbi, hg, hgi, hn, hns, -⟩ := hL
  have s6 : star (nabsA PP (DQ PP)) = nabA PP (DQ PP) := by rw [← s5, star_star]
  rw [R0v0, LevelData.m0, hg, hns, hz, hgi]
  simp only [star_mul, star_sub, star_neg, s1, s3, s4, s6, ← algebraMap_star_comm]
  simp only [act_mul, act_sub, act_neg, act_alg, gg_act, nab_act, zb_act, ggi_act]
  refine S_ext fun q => ?_
  have := gg_ne' q
  simp only [opVs, ev_mul, ev_sub, ev_add, ev_neg, ev_smul, ev_gg, ev_ggi hτ, map_add, map_sub, Complex.conj_ofReal,
    Complex.star_def]
  field_simp
  ring

end

end Formalism.FourierDecayAlt.P.MAx2.J0

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx2.J0

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.MAx1.An MeasureTheory Finset
open scoped ComplexConjugate

noncomputable section

variable {τ : ℝ}

theorem ideleNorm_embedding_neg_one_real (q : Qp 0 τ) : ‖ev (z : S τ) q‖ = ‖q.1.2‖ := by rw [eval_zeta]
theorem norm_zb (q : Qp 0 τ) : ‖ev (zb : S τ) q‖ = ‖q.1.2‖ := by rw [ev_zb, Complex.norm_conj]
theorem norm_gg (q : Qp 0 τ) : ‖ev (gg : S τ) q‖ = GR q := by
  rw [ev_gg_re, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (GR_pos q)]

theorem L2.square_integrable_zetabar_of_zeta {f : S τ} (h : L2 (z * f)) : L2 (zb * f) :=
  L2.of_le' h 1 fun q => by rw [ev_mul, ev_mul, norm_mul, norm_mul, ideleNorm_embedding_neg_one_real, norm_zb, one_mul]
theorem L2.z_of_zb {f : S τ} (h : L2 (zb * f)) : L2 (z * f) :=
  L2.of_le' h 1 fun q => by rw [ev_mul, ev_mul, norm_mul, norm_mul, ideleNorm_embedding_neg_one_real, norm_zb, one_mul]

theorem gg_div_le (hτ : 0 ≤ τ) (q : Qp 0 τ) : GR q * ‖q.1.2‖⁻¹ ≤ ‖q.1.2‖ := by
  have hz : 0 < ‖q.1.2‖ := norm_pos_iff.2 (z_ne hτ q)
  rw [mul_inv_le_iff₀ hz]
  have := GR_le hτ q
  nlinarith

theorem L2.square_integrable_gamma_zeta_inv (hτ : 0 ≤ τ) {f : S τ} (h : L2 (z * f)) : L2 (gg * (zi * f)) :=
  L2.of_le' h 1 fun q => by
    rw [ev_mul, ev_mul, ev_mul, norm_mul, norm_mul, norm_mul, ideleNorm_embedding_neg_one_real, norm_gg, ev_zi hτ, norm_inv, one_mul,
      ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (gg_div_le hτ q) (norm_nonneg _)

theorem L2.square_integrable_gamma_zetabar_inv (hτ : 0 ≤ τ) {f : S τ} (h : L2 (z * f)) : L2 (gg * (zbi * f)) :=
  L2.of_le' h 1 fun q => by
    rw [ev_mul, ev_mul, ev_mul, norm_mul, norm_mul, norm_mul, ideleNorm_embedding_neg_one_real, norm_gg, ev_zbi hτ, norm_inv,
      Complex.norm_conj, one_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (gg_div_le hτ q) (norm_nonneg _)

def Bdd (δ : ℝ) (β : S τ) : Prop := ∃ C, 0 ≤ C ∧ ∀ q, δ < GR q → ‖ev β q‖ ≤ C
def Good (δ : ℝ) (β : S τ) : Prop := Bdd δ β ∧ Bdd δ (th β) ∧ Bdd δ (thb β)
def Van (δ : ℝ) (ψ : S τ) : Prop := ∃ C, ∀ q, (GR q ≤ δ → ev ψ q = 0) ∧ ‖ev ψ q‖ ≤ C

theorem Bdd.add {δ} {a b : S τ} (ha : Bdd δ a) (hb : Bdd δ b) : Bdd δ (a + b) := by
  obtain ⟨C, hC, h⟩ := ha; obtain ⟨C', hC', h'⟩ := hb
  exact ⟨C + C', by positivity, fun q hq => by rw [ev_add]; exact (norm_add_le _ _).trans (add_le_add (h q hq) (h' q hq))⟩
theorem Bdd.mul {δ} {a b : S τ} (ha : Bdd δ a) (hb : Bdd δ b) : Bdd δ (a * b) := by
  obtain ⟨C, hC, h⟩ := ha; obtain ⟨C', hC', h'⟩ := hb
  exact ⟨C * C', by positivity, fun q hq => by
    rw [ev_mul, norm_mul]; exact mul_le_mul (h q hq) (h' q hq) (norm_nonneg _) hC⟩
theorem Bdd.neg {δ} {a : S τ} (ha : Bdd δ a) : Bdd δ (-a) := by
  obtain ⟨C, hC, h⟩ := ha; exact ⟨C, hC, fun q hq => by rw [ev_neg, norm_neg]; exact h q hq⟩
theorem bdd_zero (δ) : Bdd δ (0 : S τ) := ⟨0, le_rfl, fun q _ => by simp⟩
theorem bdd_const (δ) (c : ℂ) : Bdd δ (c • (1 : S τ)) := ⟨‖c‖, norm_nonneg _, fun q _ => by simp⟩

theorem Good.add (hτ : 0 ≤ τ) {δ} {a b : S τ} (ha : Good δ a) (hb : Good δ b) : Good δ (a + b) :=
  ⟨ha.1.add hb.1, by rw [map_add]; exact ha.2.1.add hb.2.1, by rw [map_add]; exact ha.2.2.add hb.2.2⟩
theorem Good.mul (hτ : 0 ≤ τ) {δ} {a b : S τ} (ha : Good δ a) (hb : Good δ b) : Good δ (a * b) :=
  ⟨ha.1.mul hb.1, by rw [th_mul]; exact (ha.2.1.mul hb.1).add (ha.1.mul hb.2.1),
    by rw [thb_mul]; exact (ha.2.2.mul hb.1).add (ha.1.mul hb.2.2)⟩
theorem good_const (hτ : 0 ≤ τ) (δ) (c : ℂ) : Good δ (c • (1 : S τ)) :=
  ⟨bdd_const δ c, by rw [th_const hτ]; exact bdd_zero δ, by rw [thb_const hτ]; exact bdd_zero δ⟩
theorem good_zero (hτ : 0 ≤ τ) (δ) : Good δ (0 : S τ) := by
  have := good_const hτ δ 0; rwa [zero_smul] at this
theorem Good.sum (hτ : 0 ≤ τ) {δ} {ι : Type} (s : Finset ι) (f : ι → S τ) (h : ∀ i ∈ s, Good δ (f i)) :
    Good δ (∑ i ∈ s, f i) :=
  Finset.sum_induction f (Good δ) (fun _ _ => Good.add hτ) (good_zero hτ δ) h

theorem inv_norm_le (hτ : 0 ≤ τ) {δ : ℝ} (hδ : 0 < δ) (q : Qp 0 τ) (hq : δ < GR q) : ‖q.1.2‖⁻¹ ≤ 1 + δ⁻¹ := by
  have hz : 0 < ‖q.1.2‖ := norm_pos_iff.2 (z_ne hτ q)
  have h1 : δ < ‖q.1.2‖ ^ 2 := by
    have := GR_le hτ q
    have : GR q ≤ ‖q.1.2‖ ^ 2 := this
    linarith
  have h2 : (‖q.1.2‖ ^ 2)⁻¹ < δ⁻¹ := inv_strictAnti₀ hδ h1
  have h3 : ‖q.1.2‖⁻¹ ≤ 1 + (‖q.1.2‖ ^ 2)⁻¹ := by
    rw [inv_le_iff_one_le_mul₀ hz]
    have : ‖q.1.2‖ * (1 + (‖q.1.2‖ ^ 2)⁻¹) = ‖q.1.2‖ + ‖q.1.2‖⁻¹ := by field_simp
    rw [mul_comm, this]
    by_cases h : 1 ≤ ‖q.1.2‖
    · linarith [inv_nonneg.2 hz.le]
    · push Not at h
      have : 1 < ‖q.1.2‖⁻¹ := (one_lt_inv₀ hz).2 h
      linarith
  linarith

theorem good_zi (hτ : 0 ≤ τ) {δ : ℝ} (hδ : 0 < δ) : Good δ (zi : S τ) := by
  have b : Bdd δ (zi : S τ) := ⟨1 + δ⁻¹, by positivity, fun q hq => by
    rw [ev_zi hτ, norm_inv]; exact inv_norm_le hτ hδ q hq⟩
  exact ⟨b, by rw [th_zi hτ]; exact b.neg, by rw [thb_zi hτ]; exact bdd_zero δ⟩
theorem good_zbi (hτ : 0 ≤ τ) {δ : ℝ} (hδ : 0 < δ) : Good δ (zbi : S τ) := by
  have b : Bdd δ (zbi : S τ) := ⟨1 + δ⁻¹, by positivity, fun q hq => by
    rw [ev_zbi hτ, norm_inv, Complex.norm_conj]; exact inv_norm_le hτ hδ q hq⟩
  exact ⟨b, by rw [th_zbi hτ]; exact bdd_zero δ, by rw [thb_zbi hτ]; exact b.neg⟩
theorem bdd_phase (hτ : 0 ≤ τ) (δ : ℝ) : Bdd δ ((z : S τ) * zbi) ∧ Bdd δ ((zb : S τ) * zi) := by
  constructor
  · refine ⟨1, zero_le_one, fun q _ => ?_⟩
    rw [ev_mul, eval_zeta, ev_zbi hτ, norm_mul, norm_inv, Complex.norm_conj, mul_inv_cancel₀ (norm_ne_zero_iff.2 (z_ne hτ q))]
  · refine ⟨1, zero_le_one, fun q _ => ?_⟩
    rw [ev_mul, ev_zb, ev_zi hτ, norm_mul, norm_inv, Complex.norm_conj, mul_inv_cancel₀ (norm_ne_zero_iff.2 (z_ne hτ q))]
theorem good_zzbi (hτ : 0 ≤ τ) (δ : ℝ) : Good δ ((z : S τ) * zbi) := by
  have b := (bdd_phase hτ δ).1
  refine ⟨b, ?_, ?_⟩
  · rw [th_mul, theta_zeta, th_zbi hτ, mul_zero, add_zero]; exact b
  · rw [thb_mul, theta_bar_zeta, thb_zbi hτ, zero_mul, zero_add, mul_neg]; exact b.neg
theorem good_zbzi (hτ : 0 ≤ τ) (δ : ℝ) : Good δ ((zb : S τ) * zi) := by
  have b := (bdd_phase hτ δ).2
  refine ⟨b, ?_, ?_⟩
  · rw [th_mul, th_zb, th_zi hτ, zero_mul, zero_add, mul_neg]; exact b.neg
  · rw [thb_mul, thb_zb, thb_zi hτ, mul_zero, add_zero]; exact b

theorem Van.mul_bdd {δ} {ψ β : S τ} (hψ : Van δ ψ) (hβ : Bdd δ β) : Van δ (ψ * β) := by
  obtain ⟨C, h⟩ := hψ; obtain ⟨C', hC', h'⟩ := hβ
  refine ⟨C * C', fun q => ⟨fun hq => by rw [ev_mul, (h q).1 hq, zero_mul], ?_⟩⟩
  by_cases hq : GR q ≤ δ
  · rw [ev_mul, (h q).1 hq, zero_mul, norm_zero]
    exact mul_nonneg ((norm_nonneg _).trans (h q).2) hC'
  · push Not at hq
    rw [ev_mul, norm_mul]
    exact mul_le_mul (h q).2 (h' q hq) (norm_nonneg _) ((norm_nonneg _).trans (h q).2)

theorem Van.l2 {δ} {ψ g : S τ} (hψ : Van δ ψ) (hg : L2 g) : L2 (ψ * g) := by
  obtain ⟨C, h⟩ := hψ
  exact L2.of_le' hg C fun q => by rw [ev_mul, norm_mul]; exact mul_le_mul_of_nonneg_right (h q).2 (norm_nonneg _)

def Gf (τ : ℝ) (x : E 0) : ℝ := Complex.normSq x.2 - τ

theorem Gf_smooth : ContDiff ℝ sm (Gf τ) := by
  have : Gf τ = fun x : E 0 => x.2.re * x.2.re + x.2.im * x.2.im - τ := by
    funext x; simp [Gf, Complex.normSq_apply]
  rw [this]
  have h1 : ContDiff ℝ sm fun x : E 0 => x.2.re := Complex.reCLM.contDiff.comp contDiff_snd
  have h2 : ContDiff ℝ sm fun x : E 0 => x.2.im := Complex.imCLM.contDiff.comp contDiff_snd
  exact ((h1.mul h1).add (h2.mul h2)).sub contDiff_const

theorem Gf_pos (q : Qp 0 τ) : 0 < Gf τ q.1 := sub_pos.2 q.2.2
theorem Gf_eq (q : Qp 0 τ) : Gf τ q.1 = GR q := rfl

theorem phi_smooth {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) :
    (fun q : Qp 0 τ => ((φ (Gf τ q.1) : ℝ) : ℂ)) ∈ smSub 0 τ := by
  have h1 : ContDiffOn ℝ sm (fun x => Real.log (Gf τ x)) (Qset 0 τ) :=
    Gf_smooth.contDiffOn.log fun x hx => (Gf_pos ⟨x, hx⟩).ne'
  have h2 : ContDiffOn ℝ sm (fun x => ((φ (Real.exp (Real.log (Gf τ x))) : ℝ) : ℂ)) (Qset 0 τ) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (ContDiff.comp_contDiffOn (g := fun u => φ (Real.exp u)) hφ h1)
  exact h2.congr fun x hx => by rw [ext_of_mem _ hx, Real.exp_log (Gf_pos ⟨x, hx⟩)]

def phiS {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) : S τ := ⟨_, phi_smooth hφ⟩

theorem ev_phiS {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : Qp 0 τ) : ev (phiS (τ := τ) hφ) q = ((φ (GR q) : ℝ) : ℂ) := rfl

theorem fd_phi {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : Qp 0 τ) (e : E 0) :
    fderiv ℝ (ext (phiS (τ := τ) hφ).1) q.1 e =
      ((LE.ld 1 φ (Gf τ q.1) / Gf τ q.1 : ℝ) : ℂ) * fderiv ℝ (ext (gg : S τ).1) q.1 e := by
  have hG : HasFDerivAt (Gf τ) (fderiv ℝ (Gf τ) q.1) q.1 := (Gf_smooth.differentiable (by simp [sm]) q.1).hasFDerivAt
  have hψ : HasDerivAt (fun u => φ (Real.exp u)) (LE.ld 1 φ (Gf τ q.1)) (Real.log (Gf τ q.1)) := by
    rw [LE.ld, iteratedDeriv_one]
    exact ((hφ.differentiable (by simp)) _).hasDerivAt
  have h1 := (hψ.comp _ (Real.hasDerivAt_log (Gf_pos q).ne')).comp_hasFDerivAt q.1 hG
  have h2 := Complex.ofRealCLM.hasFDerivAt.comp q.1 h1
  have h3 := Complex.ofRealCLM.hasFDerivAt.comp q.1 hG
  have e1 : ext (phiS (τ := τ) hφ).1 =ᶠ[nhds q.1]
      (Complex.ofRealCLM ∘ ((fun u => φ (Real.exp u)) ∘ Real.log) ∘ Gf τ) := by
    filter_upwards [(Qset_open 0 τ).mem_nhds q.2] with y hy
    rw [ext_of_mem _ hy]
    simp [phiS, Real.exp_log (Gf_pos ⟨y, hy⟩)]
  have e2 : ext (gg : S τ).1 =ᶠ[nhds q.1] (Complex.ofRealCLM ∘ Gf τ) := by
    filter_upwards [(Qset_open 0 τ).mem_nhds q.2] with y hy
    rw [ext_of_mem _ hy]
    have := ev_gg (τ := τ) ⟨y, hy⟩
    rw [Complex.mul_conj] at this
    show ev gg ⟨y, hy⟩ = _
    rw [this]; simp [Gf]
  rw [e1.fderiv_eq, e2.fderiv_eq, h2.fderiv, h3.fderiv]
  simp [div_eq_mul_inv]

theorem ev_th_phi (hτ : 0 ≤ τ) {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : Qp 0 τ) :
    ev (th (phiS (τ := τ) hφ)) q = ((LE.ld 1 φ (Gf τ q.1) / Gf τ q.1 : ℝ) : ℂ) * (q.1.2 * conj q.1.2) := by
  have e := congrArg (fun f => ev f q) (th_gg (τ := τ) hτ)
  simp only [ev_th, ev_mul, eval_zeta, ev_zb, wirt_alt] at e
  rw [ev_th, wirt_alt, fd_phi, fd_phi, ← e]; ring

theorem ev_thb_phi (hτ : 0 ≤ τ) {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : Qp 0 τ) :
    ev (thb (phiS (τ := τ) hφ)) q = ((LE.ld 1 φ (Gf τ q.1) / Gf τ q.1 : ℝ) : ℂ) * (q.1.2 * conj q.1.2) := by
  have e := congrArg (fun f => ev f q) (thb_gg (τ := τ) hτ)
  simp only [ev_thb, ev_mul, eval_zeta, ev_zb, wirt_zb] at e
  rw [ev_thb, wirt_zb, fd_phi, fd_phi, ← e]; ring

theorem log_derivative_vanish_near_zero {φ : ℝ → ℝ} {ε x : ℝ} (hε : 0 < ε) (h0 : ∀ x, x ≤ ε → φ x = 0) (hx : 0 < x) (hlt : x < ε) :
    LE.ld 1 φ x = 0 := by
  rw [LE.ld, iteratedDeriv_one]
  have : (fun u => φ (Real.exp u)) =ᶠ[nhds (Real.log x)] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds (Real.log_lt_log hx hlt)] with u hu
    exact h0 _ (le_of_lt ((Real.lt_log_iff_exp_lt hε).1 hu))
  rw [this.deriv_eq]; simp

theorem van_phi (hτ : 0 ≤ τ) {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) {ε : ℝ} (hε : 0 < ε) (h0 : ∀ x, x ≤ ε → φ x = 0)
    (hb : ∀ p, ∃ C, ∀ x, 0 < x → |LE.ld p φ x| ≤ C) :
    Van (ε / 2) (phiS (τ := τ) hφ) ∧ Van (ε / 2) (th (phiS (τ := τ) hφ)) ∧ Van (ε / 2) (thb (phiS (τ := τ) hφ)) := by
  obtain ⟨C0, hC0⟩ := hb 0
  obtain ⟨C1, hC1⟩ := hb 1
  have n1 : 0 ≤ C1 := (abs_nonneg _).trans (hC1 1 one_pos)
  have key : ∀ q : Qp 0 τ, (GR q ≤ ε / 2 → ((LE.ld 1 φ (Gf τ q.1) / Gf τ q.1 : ℝ) : ℂ) * (q.1.2 * conj q.1.2) = 0) ∧
      ‖((LE.ld 1 φ (Gf τ q.1) / Gf τ q.1 : ℝ) : ℂ) * (q.1.2 * conj q.1.2)‖ ≤ C1 * (1 + τ / ε) := fun q => by
    have hp := Gf_pos q
    have hn : Complex.normSq q.1.2 = Gf τ q.1 + τ := by simp [Gf]
    refine ⟨fun hq => ?_, ?_⟩
    · rw [log_derivative_vanish_near_zero hε h0 hp (by rw [Gf_eq]; linarith)]; simp
    rw [Complex.mul_conj, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs]
    by_cases hlt : Gf τ q.1 < ε
    · rw [log_derivative_vanish_near_zero hε h0 hp hlt]; simp; positivity
    · push Not at hlt
      rw [hn, abs_mul, abs_div, abs_of_pos hp, abs_of_pos (by linarith : 0 < Gf τ q.1 + τ)]
      have h1 : τ / Gf τ q.1 ≤ τ / ε := div_le_div_of_nonneg_left (by linarith) hε hlt
      calc |LE.ld 1 φ (Gf τ q.1)| / Gf τ q.1 * (Gf τ q.1 + τ) = |LE.ld 1 φ (Gf τ q.1)| * (1 + τ / Gf τ q.1) := by
            field_simp
        _ ≤ C1 * (1 + τ / ε) := mul_le_mul (hC1 _ hp) (by linarith) (by positivity) n1
  refine ⟨⟨C0, fun q => ⟨fun hq => ?_, ?_⟩⟩, ⟨C1 * (1 + τ / ε), fun q => ?_⟩, ⟨C1 * (1 + τ / ε), fun q => ?_⟩⟩
  · rw [ev_phiS, h0 _ (by linarith)]; simp
  · have := hC0 _ (GR_pos q)
    rw [LE.ld, iteratedDeriv_zero, Real.exp_log (GR_pos q)] at this
    rw [ev_phiS, Complex.norm_real, Real.norm_eq_abs]; exact this
  · rw [ev_th_phi hτ]; exact key q
  · rw [ev_thb_phi hτ]; exact key q

end

end Formalism.FourierDecayAlt.P.MAx2.J0

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx2.J0

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.MAx1.An MeasureTheory Finset
open scoped ComplexConjugate

noncomputable section

variable {τ : ℝ}

theorem inner_eq_integral_alt (f g : S τ) : ip0 f g = ∫ q, ev (f * cj g) q ∂mu0 0 τ := rfl

theorem int_add {a b : S τ} (ha : Integrable (ev a) (mu0 0 τ)) (hb : Integrable (ev b) (mu0 0 τ)) :
    Integrable (ev (a + b)) (mu0 0 τ) :=
  (ha.add hb).congr (Filter.Eventually.of_forall fun q => rfl)

theorem adjR (hτ : 0 ≤ τ) {f g : S τ} {δ : ℝ} (hδ : 0 < δ)
    (h0 : ∀ q : Qp 0 τ, GR q ≤ δ → ev f q = 0)
    (f0 : L2 f) (f1 : L2 (z * f)) (f2 : L2 (gg * (zi * th f))) (f3 : L2 (gg * (zbi * thb f)))
    (g0 : L2 g) (g1 : L2 (z * g)) (g2 : L2 (gg * (zi * th g))) (g3 : L2 (gg * (zbi * thb g))) (c : ℂ) :
    ip0 (opR c f) g = ip0 f (opRs c g) ∧ ip0 (opV c f) g = ip0 f (opVs c g) := by
  have g1' : L2 (zb * g) := L2.square_integrable_zetabar_of_zeta g1
  have hz0 : ∀ q : Qp 0 τ, Complex.normSq q.1.2 - τ ≤ δ → ev (f * cj (gg * g)) q = 0 := fun q hq => by
    rw [ev_mul, h0 q hq, zero_mul]
  have b0 : Integrable (ev (f * cj (gg * g))) (mu0 0 τ) := by
    refine (L2.integrable_mul_cj f1 g1).norm.mono' (ev_aesm _) (Filter.Eventually.of_forall fun q => ?_)
    have e1 : ‖ev (f * cj (gg * g)) q‖ = GR q * (‖ev f q‖ * ‖ev g q‖) := by
      simp only [ev_mul, ev_cj, norm_mul, Complex.norm_conj, norm_gg]; ring
    have e2 : ‖ev ((z * f) * cj (z * g)) q‖ = ‖q.1.2‖ ^ 2 * (‖ev f q‖ * ‖ev g q‖) := by
      simp only [ev_mul, ev_cj, norm_mul, Complex.norm_conj, ideleNorm_embedding_neg_one_real]; ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right (GR_le hτ q) (by positivity)
  have i1 : zi * th (f * cj (gg * g)) = (gg * (zi * th f)) * cj g + f * cj (z * g + gg * (zbi * thb g)) := by
    rw [th_mul, th_cj, thb_mul, thb_gg hτ]
    refine S_ext fun q => ?_
    have := z_ne hτ q
    have h2 : conj q.1.2 ≠ 0 := (map_ne_zero _).2 this
    simp only [ev_mul, ev_add, ev_cj, ev_zi hτ, ev_zbi hτ, eval_zeta, ev_zb, ev_gg, map_mul, map_add, map_sub,
      Complex.conj_conj, Complex.conj_ofReal, map_inv₀]
    field_simp
    try ring
  have i2 : zbi * thb (f * cj (gg * g)) = (gg * (zbi * thb f)) * cj g + f * cj (zb * g + gg * (zi * th g)) := by
    rw [thb_mul, thb_cj, th_mul, th_gg hτ]
    refine S_ext fun q => ?_
    have := z_ne hτ q
    have h2 : conj q.1.2 ≠ 0 := (map_ne_zero _).2 this
    simp only [ev_mul, ev_add, ev_cj, ev_zi hτ, ev_zbi hτ, eval_zeta, ev_zb, ev_gg, map_mul, map_add, map_sub,
      Complex.conj_conj, Complex.conj_ofReal, map_inv₀]
    field_simp
    try ring
  have a1 : Integrable (ev (zi * th (f * cj (gg * g)))) (mu0 0 τ) := by
    rw [i1]; exact int_add (L2.integrable_mul_cj f2 g0) (L2.integrable_mul_cj f0 (g1.add g3))
  have a2 : Integrable (ev (zbi * thb (f * cj (gg * g)))) (mu0 0 τ) := by
    rw [i2]; exact int_add (L2.integrable_mul_cj f3 g0) (L2.integrable_mul_cj f0 (g1'.add g2))
  obtain ⟨j1, j2⟩ := ibp hτ hδ hz0 b0 a1 a2
  have hs : ∀ c : ℂ, opRs c g = (z * g + gg * (zbi * thb g)) - conj c • (z * g) := fun c => by
    unfold opRs
    rw [thb_mul, thb_gg hτ]
    refine S_ext fun q => ?_
    have := z_ne hτ q
    have h2 : conj q.1.2 ≠ 0 := (map_ne_zero _).2 this
    simp only [ev_mul, ev_add, ev_sub, ev_smul, ev_zbi hτ, eval_zeta, ev_zb]
    field_simp
  have hvs : ∀ c : ℂ, opVs c g = -(zb * g + gg * (zi * th g)) - conj c • (zb * g) := fun c => by
    unfold opVs
    rw [th_mul, th_gg hτ]
    refine S_ext fun q => ?_
    have := z_ne hτ q
    simp only [ev_mul, ev_add, ev_sub, ev_neg, ev_smul, ev_zi hτ, eval_zeta, ev_zb]
    field_simp
  constructor
  · have e : ∀ q, ev (opR c f * cj g) q = ev (f * cj (opRs c g)) q - ev (zi * th (f * cj (gg * g))) q := fun q => by
      rw [i1, hs]
      have := z_ne hτ q
      have h2 : conj q.1.2 ≠ 0 := (map_ne_zero _).2 this
      simp only [opR, ev_mul, ev_add, ev_sub, ev_neg, ev_smul, ev_cj, ev_zi hτ, ev_zbi hτ, eval_zeta, ev_zb, ev_gg, map_mul,
        map_add, map_sub, map_neg, Complex.conj_conj, Complex.conj_ofReal, map_inv₀]
      field_simp
      try ring
    have r1 : Integrable (ev (f * cj (opRs c g))) (mu0 0 τ) := by
      rw [hs]; exact L2.integrable_mul_cj f0 ((g1.add g3).sub (g1.smul _))
    rw [inner_eq_integral_alt, inner_eq_integral_alt]
    simp only [e]
    rw [integral_sub r1 a1, j1, sub_zero]
  · have e : ∀ q, ev (opV c f * cj g) q = ev (f * cj (opVs c g)) q + ev (zbi * thb (f * cj (gg * g))) q := fun q => by
      rw [i2, hvs]
      have := z_ne hτ q
      have h2 : conj q.1.2 ≠ 0 := (map_ne_zero _).2 this
      simp only [opV, ev_mul, ev_add, ev_sub, ev_neg, ev_smul, ev_cj, ev_zi hτ, ev_zbi hτ, eval_zeta, ev_zb, ev_gg, map_mul,
        map_add, map_sub, map_neg, Complex.conj_conj, Complex.conj_ofReal, map_inv₀]
      field_simp
      try ring
    have r2 : Integrable (ev (f * cj (opVs c g))) (mu0 0 τ) := by
      rw [hvs]; exact L2.integrable_mul_cj f0 ((g1'.add g2).neg.sub (g1'.smul _))
    rw [inner_eq_integral_alt, inner_eq_integral_alt]
    simp only [e]
    rw [integral_add r2 a2, j2, add_zero]

variable {k : ℕ} {T T' : ℝ} {uu uu' : ℕ → ℝ}

local notation "PP" => Pz k T T' uu uu'

theorem square_integrable_words {L : LevelData (A PP (DQ PP)) 0} (hL : IsModelLevel PP (DQ PP) L) (hτ : 0 ≤ (PP).TT)
    {j : M.Ty PP → SmQ (PP).r (PP).TT} {m : ℕ} (hD : JDecay PP L j m) (w : List (A PP (DQ PP)))
    (hw : ∀ a ∈ w, a ∈ hatSet PP L) (hl : w.length + 1 ≤ m) (π : M.Ty PP) :
    L2 (actA PP w.prod j π) ∧ L2 (z * actA PP w.prod j π) ∧ L2 (gg * (zi * th (actA PP w.prod j π))) ∧
      L2 (gg * (zbi * thb (actA PP w.prod j π))) := by
  have hJ : ∀ w' : List (A PP (DQ PP)), w'.length ≤ m → (∀ a ∈ w', a ∈ hatSet PP L) → ∀ π,
      L2 (actA PP w'.prod j π) :=
    fun w' h1 h2 π => (memLp_two_iff_integrable_sq_norm (ev_aesm _)).2 (hD w' h1 h2 π)
  have hR : ∀ c : ℂ, L2 (opR c (actA PP w.prod j π)) := fun c => by
    have := hJ (L.R0 (c - M.aC PP π - 1 / 2) :: w) (by simp; omega)
      (fun a ha => by
        rcases List.mem_cons.1 ha with rfl | ha
        · exact Or.inl (Or.inl (Or.inr ⟨_, rfl⟩))
        · exact hw a ha) π
    rw [List.prod_cons, act_mul, raising_action hL hτ] at this
    rwa [show (M.aC PP π : ℂ) + (c - M.aC PP π - 1 / 2 + 1 / 2) = c by ring] at this
  have hV : ∀ c : ℂ, L2 (opV c (actA PP w.prod j π)) := fun c => by
    have := hJ (L.R0v (c - M.aC PP π + 1 / 2) :: w) (by simp; omega)
      (fun a ha => by
        rcases List.mem_cons.1 ha with rfl | ha
        · exact Or.inr ⟨_, rfl⟩
        · exact hw a ha) π
    rw [List.prod_cons, act_mul, raising_variant_action hL hτ] at this
    rwa [show (M.aC PP π : ℂ) + (c - M.aC PP π + 1 / 2 - 1 / 2) = c by ring] at this
  have e1 : gg * (zi * th (actA PP w.prod j π)) = -(opR 0 (actA PP w.prod j π)) := by
    simp only [opR, zero_smul, sub_zero, neg_neg]
  have e3 : gg * (zbi * thb (actA PP w.prod j π)) = opV 0 (actA PP w.prod j π) := by
    simp only [opV, zero_smul, sub_zero]
  have e4 : z * actA PP w.prod j π = opV 0 (actA PP w.prod j π) - opV 1 (actA PP w.prod j π) := by
    simp only [opV, zero_smul, one_smul, sub_zero]; abel
  refine ⟨hJ w (by omega) hw π, ?_, ?_, ?_⟩
  · rw [e4]; exact (hV 0).sub (hV 1)
  · rw [e1]; exact (hR 0).neg
  · rw [e3]; exact hV 0

def MulMat (δ : ℝ) (a : A PP (DQ PP)) : Prop :=
  ∀ π π', ∃ β : S (PP).TT, Good δ β ∧ ∀ g, Phi PP (a π π') g = β * g

theorem entry_alg (hτ : 0 ≤ (PP).TT) (δ : ℝ) (c : ℂ) :
    ∃ β : S (PP).TT, Good δ β ∧ ∀ g, Phi PP (algebraMap ℂ (DQ PP).Pr c) g = β * g :=
  ⟨c • 1, good_const hτ δ c, fun g => by
    show c • g = c • (1 : S (PP).TT) * g
    rw [smul_mul_assoc, one_mul]⟩

theorem entry_zero (hτ : 0 ≤ (PP).TT) (δ : ℝ) :
    ∃ β : S (PP).TT, Good δ β ∧ ∀ g, Phi PP (0 : (DQ PP).Pr) g = β * g :=
  ⟨0, good_zero hτ δ, fun g => by rw [map_zero, zero_mul]; rfl⟩

theorem mulmat_diag (hτ : 0 ≤ (PP).TT) (δ : ℝ) (d : M.Ty PP → (DQ PP).Pr)
    (hd : ∀ π, ∃ β : S (PP).TT, Good δ β ∧ ∀ g, Phi PP (d π) g = β * g) : MulMat δ (Matrix.diagonal d) := by
  intro π π'
  by_cases h : π = π'
  · subst h; rw [Matrix.diagonal_apply_eq]; exact hd π
  · rw [Matrix.diagonal_apply_ne _ h]; exact entry_zero hτ δ

theorem mulmat_mul (hτ : 0 ≤ (PP).TT) {δ : ℝ} {a b : A PP (DQ PP)} (ha : MulMat δ a) (hb : MulMat δ b) :
    MulMat δ (a * b) := by
  intro π π''
  choose βa hga hpa using ha
  choose βb hgb hpb using hb
  refine ⟨∑ π', βa π π' * βb π' π'', Good.sum hτ _ _ fun π' _ => (hga π π').mul hτ (hgb π' π''), fun g => ?_⟩
  rw [Matrix.mul_apply, map_sum, LinearMap.sum_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun π' _ => ?_
  rw [map_mul, Module.End.mul_apply, hpb, hpa, mul_assoc]

theorem mulmat_closure {L : LevelData (A PP (DQ PP)) 0} (hL : IsModelLevel PP (DQ PP) L) (hτ : 0 ≤ (PP).TT)
    {δ : ℝ} (hδ : 0 < δ) {b : A PP (DQ PP)} (hb : b ∈ Submonoid.closure (bddSet PP L)) : MulMat δ b := by
  obtain ⟨-, -, -, -, -, -, hz, hzi, hzb, hzbi, hg, hgi, hn, hns, -⟩ := hL
  induction hb using Submonoid.closure_induction with
  | one =>
    rw [← Matrix.diagonal_one]
    exact mulmat_diag hτ δ _ fun π => ⟨1, by simpa using good_const hτ δ 1, fun g => by rw [one_mul]; rfl⟩
  | mul x y _ _ ihx ihy => exact mulmat_mul hτ ihx ihy
  | mem x hx =>
    rcases hx with (((rfl | rfl | rfl | rfl) | ⟨g, rfl⟩) | ⟨i, -, rfl⟩) | ⟨i, -, rfl⟩
    · rw [hzi]
      show MulMat δ (Matrix.scalar _ (DQ PP).ziP)
      rw [Matrix.scalar_apply]
      exact mulmat_diag hτ δ _ fun _ => ⟨zi, good_zi hτ hδ, fun g => rfl⟩
    · rw [hzbi]
      show MulMat δ (Matrix.scalar _ (DQ PP).zbiP)
      rw [Matrix.scalar_apply]
      exact mulmat_diag hτ δ _ fun _ => ⟨zbi, good_zbi hτ hδ, fun g => rfl⟩
    · rw [LevelData.D, LevelData.Dbi, Dr0, Drbi0, one_mul, mul_one, hz, hzbi]
      show MulMat δ (Matrix.scalar _ (DQ PP).zP * Matrix.scalar _ (DQ PP).zbiP)
      rw [← map_mul, Matrix.scalar_apply]
      exact mulmat_diag hτ δ _ fun _ => ⟨z * zbi, good_zzbi hτ δ, fun g => by
        show (z : S (PP).TT) * (zbi * g) = z * zbi * g
        rw [mul_assoc]⟩
    · rw [LevelData.Db, LevelData.Di, Drb0, Dri0, one_mul, mul_one, hzb, hzi]
      show MulMat δ (Matrix.scalar _ (DQ PP).zbP * Matrix.scalar _ (DQ PP).ziP)
      rw [← map_mul, Matrix.scalar_apply]
      exact mulmat_diag hτ δ _ fun _ => ⟨zb * zi, good_zbzi hτ δ, fun g => by
        show (zb : S (PP).TT) * (zi * g) = zb * zi * g
        rw [mul_assoc]⟩
    · show MulMat δ (Matrix.diagonal fun π => algebraMap ℂ (DQ PP).Pr (g π))
      exact mulmat_diag hτ δ _ fun π => entry_alg hτ δ (g π)
    · dsimp only
      rw [Drb0, Dri0, one_mul, one_mul]
      intro π π'
      simp only [SS, Matrix.of_apply]
      split_ifs
      · exact entry_alg hτ δ _
      · exact entry_zero hτ δ
    · dsimp only
      rw [Drb0, Dri0, one_mul, one_mul]
      intro π π'
      rw [Matrix.star_apply]
      simp only [SS, Matrix.of_apply]
      split_ifs
      · rw [← algebraMap_star_comm]; exact entry_alg hτ δ _
      · rw [star_zero]; exact entry_zero hτ δ

theorem F_facts (hτ : 0 ≤ (PP).TT) {δ : ℝ} {ψ : S (PP).TT}
    (hψ : Van δ ψ) (hψ1 : Van δ (th ψ)) (hψ2 : Van δ (thb ψ))
    {b : A PP (DQ PP)} (hb : MulMat δ b) {U : M.Ty PP → S (PP).TT}
    (hU : ∀ π, L2 (U π) ∧ L2 (z * U π) ∧ L2 (gg * (zi * th (U π))) ∧ L2 (gg * (zbi * thb (U π)))) (π : M.Ty PP) :
    (∀ q, GR q ≤ δ → ev (ψ * actA PP b U π) q = 0) ∧ L2 (ψ * actA PP b U π) ∧ L2 (z * (ψ * actA PP b U π)) ∧
      L2 (gg * (zi * th (ψ * actA PP b U π))) ∧ L2 (gg * (zbi * thb (ψ * actA PP b U π))) := by
  choose β hβg hβp using hb
  have hA : actA PP b U π = ∑ π', β π π' * U π' := by
    rw [actA_eq]; exact Finset.sum_congr rfl fun π' _ => hβp π π' (U π')
  rw [hA]
  obtain ⟨Cψ, hψv⟩ := hψ
  have hψ' : Van δ ψ := ⟨Cψ, hψv⟩
  refine ⟨fun q hq => by rw [ev_mul, (hψv q).1 hq, zero_mul], ?_, ?_, ?_, ?_⟩
  · rw [Finset.mul_sum]
    exact L2.sum _ _ fun π' _ => by rw [← mul_assoc]; exact (hψ'.mul_bdd (hβg π π').1).l2 (hU π').1
  · simp only [Finset.mul_sum]
    refine L2.sum _ _ fun π' _ => ?_
    have : z * (ψ * (β π π' * U π')) = (ψ * β π π') * (z * U π') := by ring
    rw [this]; exact (hψ'.mul_bdd (hβg π π').1).l2 (hU π').2.1
  · simp only [Finset.mul_sum, map_sum]
    refine L2.sum _ _ fun π' _ => ?_
    have : gg * (zi * th (ψ * (β π π' * U π'))) = (th ψ * β π π') * (gg * (zi * U π')) +
        (ψ * th (β π π')) * (gg * (zi * U π')) + (ψ * β π π') * (gg * (zi * th (U π'))) := by
      rw [th_mul, th_mul]; ring
    rw [this]
    have hz := L2.square_integrable_gamma_zeta_inv hτ (hU π').2.1
    exact (((hψ1.mul_bdd (hβg π π').1).l2 hz).add ((hψ'.mul_bdd (hβg π π').2.1).l2 hz)).add
      ((hψ'.mul_bdd (hβg π π').1).l2 (hU π').2.2.1)
  · simp only [Finset.mul_sum, map_sum]
    refine L2.sum _ _ fun π' _ => ?_
    have : gg * (zbi * thb (ψ * (β π π' * U π'))) = (thb ψ * β π π') * (gg * (zbi * U π')) +
        (ψ * thb (β π π')) * (gg * (zbi * U π')) + (ψ * β π π') * (gg * (zbi * thb (U π'))) := by
      rw [thb_mul, thb_mul]; ring
    rw [this]
    have hz := L2.square_integrable_gamma_zetabar_inv hτ (hU π').2.1
    exact (((hψ2.mul_bdd (hβg π π').1).l2 hz).add ((hψ'.mul_bdd (hβg π π').2.2).l2 hz)).add
      ((hψ'.mul_bdd (hβg π π').1).l2 (hU π').2.2.2)

end

end Formalism.FourierDecayAlt.P.MAx2.J0

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.MAx2.J0

theorem adjoint_at_zero : Formalism.FourierDecayAlt.MA.JAdjZero := by
  intro P L j m hr hτ hL hD
  obtain ⟨k, r, T, T', uu, uu'⟩ := P
  simp only at hr
  subst hr
  intro φ ε hε hφ h0 hb β hβ X hX v w hl ha
  have hG : ∀ q, Gq (Pz k T T' uu uu') q = GR q := fun q => by simp [Gq, GR]
  have hφS : toSm (Pz k T T' uu uu') (fun q => (φ (Gq (Pz k T T' uu uu') q) : ℂ)) = phiS hφ := by
    simp only [hG]
    exact dif_pos (phi_smooth hφ)
  rw [hφS]
  have hδ : (0 : ℝ) < ε / 2 := by positivity
  obtain ⟨v0, v1, v2⟩ := van_phi hτ hφ hε h0 hb
  have hbm : MulMat (ε / 2) β := mulmat_closure hL hτ hδ hβ
  have hv := square_integrable_words hL hτ hD v (fun a h => ha a (List.mem_append_left _ h)) (show v.length + 1 ≤ m by omega)
  have hw := square_integrable_words hL hτ hD w (fun a h => ha a (List.mem_append_right _ h)) (show w.length + 1 ≤ m by omega)
  have hF := fun π => F_facts hτ v0 v1 v2 hbm hv π
  rw [act_mul _ β v.prod, act_mul _ (star X) w.prod]
  unfold ipA
  rcases hX with ((⟨y, rfl⟩ | ⟨y, rfl⟩) | ⟨y, rfl⟩) | ⟨y, rfl⟩
  · rw [Ahat0 L y, star_one, act_one, act_one]
  · refine Finset.sum_congr rfl fun π _ => ?_
    rw [raising_action hL hτ, raising_star_action hL hτ]
    obtain ⟨f0v, f0, f1, f2, f3⟩ := hF π
    obtain ⟨g0, g1, g2, g3⟩ := hw π
    exact (adjR hτ hδ f0v f0 f1 f2 f3 g0 g1 g2 g3 _).1
  · rw [Ahatv0 L y, star_one, act_one, act_one]
  · refine Finset.sum_congr rfl fun π _ => ?_
    rw [raising_variant_action hL hτ, R0vs_act hL hτ]
    obtain ⟨f0v, f0, f1, f2, f3⟩ := hF π
    obtain ⟨g0, g1, g2, g3⟩ := hw π
    exact (adjR hτ hδ f0v f0 f1 f2 f3 g0 g1 g2 g3 _).2

end Formalism.FourierDecayAlt.P

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx2.Adj

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.P.MAx1.An MeasureTheory
open scoped ComplexConjugate

noncomputable section

variable {r : ℕ} {TT : ℝ}

theorem ext_conj (f : Qp r TT → ℂ) : ext (fun q => conj (f q)) = fun x => conj (ext f x) := by
  funext x; by_cases hx : x ∈ Qset r TT <;> simp [ext, hx]

theorem ext_add (f g : Qp r TT → ℂ) : ext (f + g) = ext f + ext g := by
  funext x; by_cases hx : x ∈ Qset r TT <;> simp [ext, hx]

theorem ext_out (f : Qp r TT → ℂ) {x : E r} (hx : x ∉ Qset r TT) : ext f x = 0 := by
  simp [ext, hx]

def cj (f : SmQ r TT) : SmQ r TT :=
  ⟨fun q => conj ((f : Qp r TT → ℂ) q), by
    show ContDiffOn ℝ sm (ext fun q => conj ((f : Qp r TT → ℂ) q)) (Qset r TT)
    rw [ext_conj]
    exact (Complex.conjCLE.contDiff.comp_contDiffOn
      (f.2 : ContDiffOn ℝ sm (ext (f : Qp r TT → ℂ)) (Qset r TT))).congr fun x _ => by simp⟩

theorem cj_apply (f : SmQ r TT) (q : Qp r TT) : ((cj f : SmQ r TT) : Qp r TT → ℂ) q = conj ((f : Qp r TT → ℂ) q) :=
  rfl

theorem S_ext {f g : SmQ r TT} (h : ∀ q, (f : Qp r TT → ℂ) q = (g : Qp r TT → ℂ) q) : f = g :=
  Subtype.ext (funext h)

theorem cj_mul (f g : SmQ r TT) : cj (f * g) = cj f * cj g := S_ext fun q => by
  simp [cj_apply]

theorem test_zero_near {f : SmQ r TT} {x : E r} (hx : x ∉ tsupport (ext (f : Qp r TT → ℂ))) :
    ext (f : Qp r TT → ℂ) =ᶠ[nhds x] 0 :=
  notMem_tsupport_iff_eventuallyEq.1 hx

theorem test_contDiff {f : SmQ r TT} (hf : f ∈ Test r TT) : ContDiff ℝ sm (ext (f : Qp r TT → ℂ)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ Qset r TT
  · exact (f.2 : ContDiffOn ℝ sm (ext (f : Qp r TT → ℂ)) (Qset r TT)).contDiffAt ((Qset_open r TT).mem_nhds hx)
  · have h1 : x ∉ tsupport (ext (f : Qp r TT → ℂ)) := fun h => hx (hf.2 h)
    exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq (test_zero_near h1)

theorem test_integrable {f : SmQ r TT} (hf : f ∈ Test r TT) : Integrable (ext (f : Qp r TT → ℂ)) :=
  (test_contDiff hf).continuous.integrable_of_hasCompactSupport hf.1

theorem test_mul_left (g : SmQ r TT) {f : SmQ r TT} (hf : f ∈ Test r TT) : g * f ∈ Test r TT := by
  have he : ext ((g * f : SmQ r TT) : Qp r TT → ℂ) = ext (g : Qp r TT → ℂ) * ext (f : Qp r TT → ℂ) := by
    rw [Subalgebra.coe_mul, ext_mul]
  refine ⟨?_, ?_⟩
  · rw [he]; exact hf.1.mul_left
  · rw [he]; exact tsupport_mul_subset_right.trans hf.2

theorem test_mul_right {f : SmQ r TT} (hf : f ∈ Test r TT) (g : SmQ r TT) : f * g ∈ Test r TT := by
  rw [mul_comm]; exact test_mul_left g hf

theorem test_add {f g : SmQ r TT} (hf : f ∈ Test r TT) (hg : g ∈ Test r TT) : f + g ∈ Test r TT := by
  have he : ext ((f + g : SmQ r TT) : Qp r TT → ℂ) = ext (f : Qp r TT → ℂ) + ext (g : Qp r TT → ℂ) := by
    rw [Subalgebra.coe_add, ext_add]
  refine ⟨?_, ?_⟩
  · rw [he]; exact hf.1.add hg.1
  · rw [he]; exact (tsupport_add _ _).trans (Set.union_subset hf.2 hg.2)

theorem test_smul (c : ℂ) {f : SmQ r TT} (hf : f ∈ Test r TT) : c • f ∈ Test r TT := by
  rw [Algebra.smul_def]; exact test_mul_left _ hf

theorem test_neg {f : SmQ r TT} (hf : f ∈ Test r TT) : -f ∈ Test r TT := by
  rw [neg_eq_neg_one_mul]; exact test_mul_left _ hf

theorem test_zero : (0 : SmQ r TT) ∈ Test r TT := by
  have he : ext ((0 : SmQ r TT) : Qp r TT → ℂ) = 0 := by
    funext x; by_cases hx : x ∈ Qset r TT <;> simp [ext, hx]
  refine ⟨?_, ?_⟩
  · rw [he]; exact HasCompactSupport.zero
  · rw [he, tsupport_zero]; exact Set.empty_subset _

theorem test_sum {ι : Type*} (s : Finset ι) (f : ι → SmQ r TT) (hf : ∀ i ∈ s, f i ∈ Test r TT) :
    ∑ i ∈ s, f i ∈ Test r TT := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using test_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact test_add (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem wirt_zero_of_near (v : M.Var r) {F : E r → ℂ} {x : E r} (h : F =ᶠ[nhds x] 0) : wirt v F x = 0 := by
  rw [wirt_congr v h]
  simp [wirt]

theorem test_euler (v : M.Var r) {f : SmQ r TT} (hf : f ∈ Test r TT) : eulerQ v f ∈ Test r TT := by
  have hs : Function.support (ext ((eulerQ v f : SmQ r TT) : Qp r TT → ℂ)) ⊆ tsupport (ext (f : Qp r TT → ℂ)) := by
    intro x hx
    by_contra hn
    apply hx
    by_cases hq : x ∈ Qset r TT
    · rw [ext_of_mem _ hq, eulerQ_apply]
      simp only
      rw [wirt_zero_of_near v (test_zero_near hn), mul_zero]
    · exact ext_out _ hq
  refine ⟨hf.1.mono' hs, ?_⟩
  exact (closure_minimal hs (isClosed_tsupport _)).trans hf.2

theorem test_cj {f : SmQ r TT} (hf : f ∈ Test r TT) : cj f ∈ Test r TT := by
  have he : ext ((cj f : SmQ r TT) : Qp r TT → ℂ) = fun x => conj (ext (f : Qp r TT → ℂ) x) := ext_conj _
  have hs : Function.support (ext ((cj f : SmQ r TT) : Qp r TT → ℂ)) = Function.support (ext (f : Qp r TT → ℂ)) := by
    rw [he]; ext x; simp
  refine ⟨?_, ?_⟩
  · unfold HasCompactSupport tsupport; rw [hs]; exact hf.1
  · unfold tsupport; rw [hs]; exact hf.2

instance haarE : (volume : Measure (E r)).IsAddHaarMeasure := by
  have h1 : (volume : Measure ℂ).IsAddHaarMeasure := by infer_instance
  have h2 : (volume : Measure (Fin r → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact Measure.prod.instIsAddHaarMeasure (volume : Measure (Fin r → ℂ)) (volume : Measure ℂ)

theorem int_fderiv_zero {f : SmQ r TT} (hf : f ∈ Test r TT) (d : E r) :
    ∫ x, fderiv ℝ (ext (f : Qp r TT → ℂ)) x d = 0 := by
  have hF := test_contDiff hf
  have hdiff : Differentiable ℝ (ext (f : Qp r TT → ℂ)) := hF.differentiable (by simp [sm])
  have hcont : Continuous fun x => fderiv ℝ (ext (f : Qp r TT → ℂ)) x d :=
    (hF.continuous_fderiv (by simp [sm])).clm_apply continuous_const
  have hint : Integrable (fun x => fderiv ℝ (ext (f : Qp r TT → ℂ)) x d) :=
    hcont.integrable_of_hasCompactSupport (hf.1.fderiv_apply (𝕜 := ℝ) d)
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (E r)))
    (f := fun _ : E r => (1 : ℂ)) (g := ext (f : Qp r TT → ℂ)) (v := d)
    (by simp) (by simpa using hint) (by simpa using test_integrable hf)
    (fun x _ => differentiableAt_const _) (fun x _ => hdiff x)
  simpa using key

theorem int_wirt_zero (v : M.Var r) {f : SmQ r TT} (hf : f ∈ Test r TT) :
    ∫ x, wirt v (ext (f : Qp r TT → ℂ)) x = 0 := by
  have hF := test_contDiff hf
  have hint : ∀ d : E r, Integrable (fun x => fderiv ℝ (ext (f : Qp r TT → ℂ)) x d) := fun d =>
    ((hF.continuous_fderiv (by simp [sm])).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hf.1.fderiv_apply (𝕜 := ℝ) d)
  unfold wirt
  rw [integral_const_mul, integral_add (hint _) ((hint _).const_mul _), integral_const_mul,
    int_fderiv_zero hf, int_fderiv_zero hf]
  simp

def dR (x : E r) : ℝ := ∏ l, (Complex.normSq (x.1 l))⁻¹

theorem density_measurable : Measurable (dens0 (r := r)) := by
  unfold dens0
  exact Finset.measurable_prod _ fun l _ => ENNReal.measurable_ofReal.comp
    ((Complex.continuous_normSq.comp ((continuous_apply l).comp continuous_fst)).measurable.inv)

theorem density_lt_top (x : E r) : dens0 x < ⊤ := by
  unfold dens0
  exact ENNReal.prod_lt_top fun l _ => ENNReal.ofReal_lt_top

theorem density_toReal (x : E r) : (dens0 x).toReal = dR x := by
  unfold dens0 dR
  rw [ENNReal.toReal_prod]
  exact Finset.prod_congr rfl fun l _ => ENNReal.toReal_ofReal (inv_nonneg.2 (Complex.normSq_nonneg _))

theorem integral_base_measure (F : Qp r TT → ℂ) : ∫ q, F q ∂mu0 r TT = ∫ x, ((dR x : ℝ) : ℂ) * ext F x := by
  have hQ : MeasurableSet (Qset r TT) := (Qset_open r TT).measurableSet
  have e1 : ∫ q, F q ∂mu0 r TT = ∫ q : Qp r TT, ext F (q : E r) ∂mu0 r TT := by
    congr 1; funext q; simp [ext, q.2]
  rw [e1, mu0, integral_subtype_comap hQ (fun x => ext F x),
    setIntegral_withDensity_eq_setIntegral_toReal_smul density_measurable (ae_of_all _ fun x => density_lt_top x) _ hQ,
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [ext_out _ hx])]
  congr 1; funext x
  rw [Complex.real_smul, density_toReal]

def evq (q : Qp r TT) : SmQ r TT →+* ℂ :=
  (Pi.evalRingHom (fun _ : Qp r TT => ℂ) q).comp (smSub r TT).val.toRingHom

theorem evq_apply (q : Qp r TT) (f : SmQ r TT) : evq q f = (f : Qp r TT → ℂ) q := rfl

theorem inv_val (u : SmQ r TT) (hu : ∀ q, (u : Qp r TT → ℂ) q ≠ 0) (q : Qp r TT) :
    ((Ring.inverse u : SmQ r TT) : Qp r TT → ℂ) q = ((u : Qp r TT → ℂ) q)⁻¹ := by
  have h1 := congrArg (evq q) (Ring.mul_inverse_cancel u (isUnit_of_ne u hu))
  rw [map_mul, map_one, evq_apply, evq_apply] at h1
  exact (inv_eq_of_mul_eq_one_right h1).symm

theorem coordE_vc (l : Fin r) (x : E r) : coordE (M.vc l) x = x.1 l := by
  have h : ((ofLex (M.vc l : M.Var r)).1 : ℕ) < r := by simp [M.vc]
  unfold coordE zE
  rw [dif_pos h]
  simp [M.vc]

theorem coordE_vcb (l : Fin r) (x : E r) : coordE (M.vcb l) x = conj (x.1 l) := by
  have h : ((ofLex (M.vcb l : M.Var r)).1 : ℕ) < r := by simp [M.vcb]
  unfold coordE zE
  rw [dif_pos h]
  simp [M.vcb]

theorem coordE_vc_ne (l : Fin r) (q : Qp r TT) : coordE (M.vc l) q.1 ≠ 0 := by
  rw [coordE_vc]; exact q.2.1 l

theorem coordE_vcb_ne (l : Fin r) (q : Qp r TT) : coordE (M.vcb l) q.1 ≠ 0 := by
  rw [coordE_vcb]; simpa using q.2.1 l

def d0Q : SmQ r TT := ∏ l, Ring.inverse (coordQ (M.vc l)) * Ring.inverse (coordQ (M.vcb l))

theorem density_value (q : Qp r TT) : ((d0Q : SmQ r TT) : Qp r TT → ℂ) q = ((dR q.1 : ℝ) : ℂ) := by
  rw [← evq_apply, d0Q, map_prod]
  unfold dR
  push_cast
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [map_mul, evq_apply, evq_apply, inv_val _ (fun q => coordE_vc_ne l q), inv_val _ (fun q => coordE_vcb_ne l q)]
  show (coordE (M.vc l) q.1)⁻¹ * (coordE (M.vcb l) q.1)⁻¹ = _
  rw [coordE_vc, coordE_vcb, ← mul_inv, Complex.mul_conj]

theorem dR_ext (Ψ : SmQ r TT) (x : E r) :
    ((dR x : ℝ) : ℂ) * ext (Ψ : Qp r TT → ℂ) x = ext ((Ψ * d0Q : SmQ r TT) : Qp r TT → ℂ) x := by
  by_cases hx : x ∈ Qset r TT
  · rw [ext_of_mem _ hx, ext_of_mem _ hx, Subalgebra.coe_mul, Pi.mul_apply, density_value]; ring
  · rw [ext_out _ hx, ext_out _ hx, mul_zero]

def IE (Ψ : SmQ r TT) : ℂ := ∫ x, ext (Ψ : Qp r TT → ℂ) x

theorem inner_eq_integral_alt (f g : SmQ r TT) : ip0 f g = IE (f * cj g * d0Q) := by
  unfold ip0 IE
  rw [integral_base_measure (fun q => (f : Qp r TT → ℂ) q * conj ((g : Qp r TT → ℂ) q))]
  congr 1; funext x
  exact dR_ext (f * cj g) x

theorem IE_add {Φ Ψ : SmQ r TT} (hΦ : Φ ∈ Test r TT) (hΨ : Ψ ∈ Test r TT) : IE (Φ + Ψ) = IE Φ + IE Ψ := by
  unfold IE
  rw [Subalgebra.coe_add, ext_add]
  exact integral_add (test_integrable hΦ) (test_integrable hΨ)

theorem inner_add_left_alt {f₁ f₂ : SmQ r TT} (h₁ : f₁ ∈ Test r TT) (h₂ : f₂ ∈ Test r TT) (g : SmQ r TT) :
    ip0 (f₁ + f₂) g = ip0 f₁ g + ip0 f₂ g := by
  rw [inner_eq_integral_alt, inner_eq_integral_alt, inner_eq_integral_alt, add_mul, add_mul,
    IE_add (test_mul_right (test_mul_right h₁ _) _) (test_mul_right (test_mul_right h₂ _) _)]

theorem cj_add (g₁ g₂ : SmQ r TT) : cj (g₁ + g₂) = cj g₁ + cj g₂ := S_ext fun q => by simp [cj_apply]

theorem inner_add_right_alt {f : SmQ r TT} (hf : f ∈ Test r TT) (g₁ g₂ : SmQ r TT) :
    ip0 f (g₁ + g₂) = ip0 f g₁ + ip0 f g₂ := by
  rw [inner_eq_integral_alt, inner_eq_integral_alt, inner_eq_integral_alt, cj_add, mul_add, add_mul,
    IE_add (test_mul_right (test_mul_right hf _) _) (test_mul_right (test_mul_right hf _) _)]

theorem inner_smul_left_alt (z : ℂ) (f g : SmQ r TT) : ip0 (z • f) g = z * ip0 f g := by
  unfold ip0
  rw [← integral_const_mul]
  congr 1; funext q
  simp [mul_assoc]

theorem inner_smul_right_alt (z : ℂ) (f g : SmQ r TT) : ip0 f (z • g) = conj z * ip0 f g := by
  unfold ip0
  rw [← integral_const_mul]
  congr 1; funext q
  simp; ring

theorem inner_neg_right_alt (f g : SmQ r TT) : ip0 f (-g) = -ip0 f g := by
  unfold ip0
  rw [← integral_neg]
  congr 1; funext q
  simp

theorem inner_conj_symm_alt (f g : SmQ r TT) : ip0 f g = conj (ip0 g f) := by
  unfold ip0
  rw [← integral_conj]
  congr 1; funext q
  simp [mul_comm]

theorem inner_zero_left_alt (g : SmQ r TT) : ip0 0 g = 0 := by unfold ip0; simp

theorem inner_zero_right_alt (f : SmQ r TT) : ip0 f 0 = 0 := by unfold ip0; simp

theorem inner_sum_left_alt {ι : Type*} (s : Finset ι) (h : ι → SmQ r TT) (hh : ∀ i ∈ s, h i ∈ Test r TT)
    (g : SmQ r TT) : ip0 (∑ i ∈ s, h i) g = ∑ i ∈ s, ip0 (h i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [inner_zero_left_alt]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      inner_add_left_alt (hh a (Finset.mem_insert_self a s))
        (test_sum s h fun i hi => hh i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hh i (Finset.mem_insert_of_mem hi)]

theorem inner_sum_right_alt {ι : Type*} {f : SmQ r TT} (hf : f ∈ Test r TT) (s : Finset ι) (h : ι → SmQ r TT) :
    ip0 f (∑ i ∈ s, h i) = ∑ i ∈ s, ip0 f (h i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [inner_zero_right_alt]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, inner_add_right_alt hf, ih]

theorem add_fst (a b : (anQ r TT).Pr) (f : SmQ r TT) : (a + b).1 f = a.1 f + b.1 f := rfl
theorem add_snd (a b : (anQ r TT).Pr) (g : SmQ r TT) : (a + b).2.unop g = a.2.unop g + b.2.unop g := rfl
theorem mul_fst (a b : (anQ r TT).Pr) (f : SmQ r TT) : (a * b).1 f = a.1 (b.1 f) := rfl
theorem mul_snd (a b : (anQ r TT).Pr) (g : SmQ r TT) : (a * b).2.unop g = b.2.unop (a.2.unop g) := rfl
theorem one_fst (f : SmQ r TT) : (1 : (anQ r TT).Pr).1 f = f := rfl
theorem one_snd (g : SmQ r TT) : (1 : (anQ r TT).Pr).2.unop g = g := rfl
theorem star_fst (a : (anQ r TT).Pr) (f : SmQ r TT) : (star a).1 f = a.2.unop f := rfl
theorem star_snd (a : (anQ r TT).Pr) (g : SmQ r TT) : (star a).2.unop g = a.1 g := rfl
theorem alg_fst (z : ℂ) (f : SmQ r TT) : (algebraMap ℂ (anQ r TT).Pr z).1 f = z • f := rfl
theorem alg_snd (z : ℂ) (g : SmQ r TT) : (algebraMap ℂ (anQ r TT).Pr z).2.unop g = conj z • g := rfl

theorem isAdj_one : IsAdj (1 : (anQ r TT).Pr) :=
  ⟨fun f hf => by rw [one_fst]; exact hf, fun g hg => by rw [one_snd]; exact hg,
    fun f _ g _ => by rw [one_fst, one_snd]⟩

theorem isAdj_add {a b : (anQ r TT).Pr} (ha : IsAdj a) (hb : IsAdj b) : IsAdj (a + b) :=
  ⟨fun f hf => by rw [add_fst]; exact test_add (ha.1 f hf) (hb.1 f hf),
    fun g hg => by rw [add_snd]; exact test_add (ha.2.1 g hg) (hb.2.1 g hg),
    fun f hf g hg =>
      calc ip0 ((a + b).1 f) g = ip0 (a.1 f + b.1 f) g := rfl
        _ = ip0 (a.1 f) g + ip0 (b.1 f) g := inner_add_left_alt (ha.1 f hf) (hb.1 f hf) g
        _ = ip0 f (a.2.unop g) + ip0 f (b.2.unop g) :=
          congrArg₂ (· + ·) (ha.2.2 f hf g hg) (hb.2.2 f hf g hg)
        _ = ip0 f (a.2.unop g + b.2.unop g) := (inner_add_right_alt hf _ _).symm
        _ = ip0 f ((a + b).2.unop g) := rfl⟩

theorem isAdj_mul {a b : (anQ r TT).Pr} (ha : IsAdj a) (hb : IsAdj b) : IsAdj (a * b) :=
  ⟨fun f hf => by rw [mul_fst]; exact ha.1 _ (hb.1 f hf),
    fun g hg => by rw [mul_snd]; exact hb.2.1 _ (ha.2.1 g hg),
    fun f hf g hg => (ha.2.2 _ (hb.1 f hf) g hg).trans (hb.2.2 f hf _ (ha.2.1 g hg))⟩

theorem isAdj_alg (z : ℂ) : IsAdj (algebraMap ℂ (anQ r TT).Pr z) :=
  ⟨fun f hf => by rw [alg_fst]; exact test_smul z hf,
    fun g hg => by rw [alg_snd]; exact test_smul _ hg,
    fun f _ g _ => by rw [alg_fst, alg_snd, inner_smul_left_alt, inner_smul_right_alt, Complex.conj_conj]⟩

theorem isAdj_smul (z : ℂ) {a : (anQ r TT).Pr} (ha : IsAdj a) : IsAdj (z • a) := by
  rw [Algebra.smul_def]; exact isAdj_mul (isAdj_alg z) ha

theorem isAdj_star {a : (anQ r TT).Pr} (ha : IsAdj a) : IsAdj (star a) :=
  ⟨fun f hf => by rw [star_fst]; exact ha.2.1 f hf,
    fun g hg => by rw [star_snd]; exact ha.1 g hg,
    fun f hf g hg =>
      calc ip0 ((star a).1 f) g = ip0 (a.2.unop f) g := rfl
        _ = conj (ip0 g (a.2.unop f)) := inner_conj_symm_alt _ _
        _ = conj (ip0 (a.1 g) f) := congrArg conj (ha.2.2 g hg f hf).symm
        _ = ip0 f (a.1 g) := (inner_conj_symm_alt _ _).symm
        _ = ip0 f ((star a).2.unop g) := rfl⟩

theorem wq_nonneg (k : ℕ) {x : E r} (hx : x ∈ Qset r TT) : 0 ≤ wq k x TT := by
  unfold wq
  exact mul_nonneg (Finset.prod_nonneg fun l _ => pow_nonneg (Complex.normSq_nonneg _) _)
    (pow_nonneg (sub_nonneg.2 hx.2.le) _)

theorem wq_cont (k : ℕ) : Continuous fun x : E r => wq k x TT := by
  unfold wq
  exact (continuous_finsetProd _ fun l _ =>
      (Complex.continuous_normSq.comp ((continuous_apply l).comp continuous_fst)).pow _).mul
    (((Complex.continuous_normSq.comp continuous_snd).sub continuous_const).pow _)

def Bar (v w : M.Var r) : Prop :=
  dirE v = dirE w ∧ ((if (ofLex v).2 = 0 then -Complex.I else Complex.I) =
    conj (if (ofLex w).2 = 0 then -Complex.I else Complex.I)) ∧ ∀ x : E r, coordE v x = conj (coordE w x)

theorem bar_c (l : Fin r) : Bar (M.vc l) (M.vcb l) := by
  refine ⟨?_, ?_, fun x => ?_⟩
  · simp [dirE, M.vc, M.vcb]
  · simp [M.vc, M.vcb]
  · rw [coordE_vc, coordE_vcb, Complex.conj_conj]

theorem bar_cb (l : Fin r) : Bar (M.vcb l) (M.vc l) := by
  refine ⟨?_, ?_, fun x => ?_⟩
  · simp [dirE, M.vc, M.vcb]
  · simp [M.vc, M.vcb]
  · rw [coordE_vc, coordE_vcb]

theorem conjugate_zeta_pair : Bar (M.vz : M.Var r) M.vzb := by
  refine ⟨?_, ?_, fun x => ?_⟩
  · simp [dirE, M.vz, M.vzb]
  · simp [M.vz, M.vzb]
  · rw [coordE_vz, coordE_vzb, Complex.conj_conj]

theorem bar_zb : Bar (M.vzb : M.Var r) M.vz := by
  refine ⟨?_, ?_, fun x => ?_⟩
  · simp [dirE, M.vz, M.vzb]
  · simp [M.vz, M.vzb]
  · rw [coordE_vz, coordE_vzb]

theorem wirt_conj {v w : M.Var r} (hb : Bar v w) {F : E r → ℂ} {x : E r} (hF : DifferentiableAt ℝ F x) :
    wirt v (fun y => conj (F y)) x = conj (wirt w F x) := by
  have he : (fun y => conj (F y)) = (Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘ F := by funext y; simp
  have hd : fderiv ℝ (fun y => conj (F y)) x = (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ F x) := by
    rw [he]; exact ((Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp x hF.hasFDerivAt).fderiv
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
  unfold wirt
  rw [hd, hb.1, hb.2.1]
  by_cases h : (ofLex w).2 = 0
  · simp [h, h2, map_add, map_mul]
  · simp [h, h2, map_add, map_mul]

theorem ev_cj {v w : M.Var r} (hb : Bar v w) (g : SmQ r TT) : eulerQ v (cj g) = cj (eulerQ w g) :=
  S_ext fun q => by
    rw [eulerQ_apply, cj_apply, eulerQ_apply]
    have he : ext ((cj g : SmQ r TT) : Qp r TT → ℂ) = fun y => conj (ext (g : Qp r TT → ℂ) y) := ext_conj _
    rw [he, wirt_conj hb (ext_smooth_diff g.2 q.1 q.2), hb.2.2, map_mul]

theorem cj_coord {v w : M.Var r} (hb : Bar v w) : cj (coordQ w : SmQ r TT) = coordQ v :=
  S_ext fun q => by
    rw [cj_apply]
    exact (hb.2.2 q.1).symm

theorem cj_inv (u : SmQ r TT) (hu : ∀ q, (u : Qp r TT → ℂ) q ≠ 0) : cj (Ring.inverse u) = Ring.inverse (cj u) :=
  S_ext fun q => by
    rw [cj_apply, inv_val u hu, inv_val (cj u) (fun q => by rw [cj_apply]; simpa using hu q), cj_apply, map_inv₀]

theorem cj_one : cj (1 : SmQ r TT) = 1 := S_ext fun q => by simp [cj_apply]

theorem cj_gg : cj (ggQ r TT) = ggQ r TT := S_ext fun q => by
  rw [cj_apply, gg_apply, coordE_vz, coordE_vzb]
  simp [mul_comm]

theorem unit_coord (hTT : 0 ≤ TT) (v : M.Var r) (q : Qp r TT) : ((coordQ v : SmQ r TT) : Qp r TT → ℂ) q ≠ 0 :=
  coordE_ne q.2 hTT v

theorem inv_mul_coord (hTT : 0 ≤ TT) (v : M.Var r) : (Ring.inverse (coordQ v) : SmQ r TT) * coordQ v = 1 :=
  Ring.inverse_mul_cancel _ (isUnit_of_ne _ (unit_coord hTT v))

theorem IE_inv_euler (hTT : 0 ≤ TT) (v : M.Var r) {Ψ : SmQ r TT} (hΨ : Ψ ∈ Test r TT) :
    IE (Ring.inverse (coordQ v) * eulerQ v Ψ) = 0 := by
  unfold IE
  rw [← int_wirt_zero v hΨ]
  congr 1; funext x
  by_cases hx : x ∈ Qset r TT
  · rw [ext_of_mem _ hx, Subalgebra.coe_mul, Pi.mul_apply, inv_val _ (unit_coord hTT v), eulerQ_apply]
    show (coordE v x)⁻¹ * (coordE v x * wirt v (ext (Ψ : Qp r TT → ℂ)) x) = _
    rw [← mul_assoc, inv_mul_cancel₀ (coordE_ne hx hTT v), one_mul]
  · rw [ext_out _ hx, wirt_zero_of_near v (test_zero_near fun h => hx (hΨ.2 h))]

theorem ev_inv_coord (hTT : 0 ≤ TT) (v w : M.Var r) :
    eulerQ v (Ring.inverse (coordQ w) : SmQ r TT) = (if v = w then (-1 : ℂ) else 0) • Ring.inverse (coordQ w) := by
  have h := Formalism.FourierDecayAlt.P.MAx1.eci (Formalism.FourierDecayAlt.P.analytic_laws r TT hTT) v w
  refine h.trans ?_
  split_ifs with hvw
  · simp only [neg_smul, one_smul]; rfl
  · simp only [zero_smul]; rfl

theorem ev_prod (hTT : 0 ≤ TT) (v : M.Var r) {ι : Type*} (s : Finset ι) (g : ι → SmQ r TT) (a : ι → ℂ)
    (h : ∀ i, eulerQ v (g i) = a i • g i) : eulerQ v (∏ i ∈ s, g i) = (∑ i ∈ s, a i) • ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty, zero_smul]
    exact Formalism.FourierDecayAlt.P.MAx1.ev_one (Formalism.FourierDecayAlt.P.analytic_laws r TT hTT) v
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Formalism.FourierDecayAlt.P.analytic_leibniz r TT v, h, ih, add_smul,
      smul_mul_assoc, mul_smul_comm]

theorem ev_d0Q (hTT : 0 ≤ TT) (v : M.Var r) : eulerQ v (d0Q : SmQ r TT) =
    (∑ m, ((if v = M.vc m then (-1 : ℂ) else 0) + (if v = M.vcb m then (-1 : ℂ) else 0))) • d0Q := by
  unfold d0Q
  apply ev_prod hTT v
  intro m
  rw [Formalism.FourierDecayAlt.P.analytic_leibniz r TT v, ev_inv_coord hTT, ev_inv_coord hTT, add_smul, smul_mul_assoc,
    mul_smul_comm]

theorem ev_d0Q_alt (hTT : 0 ≤ TT) : eulerQ M.vz (d0Q : SmQ r TT) = 0 := by
  rw [ev_d0Q hTT]
  have h : ∀ m : Fin r, ((if (M.vz : M.Var r) = M.vc m then (-1 : ℂ) else 0) +
      (if (M.vz : M.Var r) = M.vcb m then (-1 : ℂ) else 0)) = 0 := fun m => by
    rw [if_neg (Formalism.FourierDecayAlt.P.MAx1.vc_vz m).symm, if_neg (Formalism.FourierDecayAlt.P.MAx1.vcb_vz m).symm, add_zero]
  simp [h]

theorem ev_d0Q_zb (hTT : 0 ≤ TT) : eulerQ M.vzb (d0Q : SmQ r TT) = 0 := by
  rw [ev_d0Q hTT]
  have h : ∀ m : Fin r, ((if (M.vzb : M.Var r) = M.vc m then (-1 : ℂ) else 0) +
      (if (M.vzb : M.Var r) = M.vcb m then (-1 : ℂ) else 0)) = 0 := fun m => by
    rw [if_neg (Formalism.FourierDecayAlt.P.MAx1.vc_vzb m).symm, if_neg (Formalism.FourierDecayAlt.P.MAx1.vcb_vzb m).symm, add_zero]
  simp [h]

theorem ev_d0Q_c (hTT : 0 ≤ TT) (l : Fin r) : eulerQ (M.vc l) (d0Q : SmQ r TT) = (-1 : ℂ) • d0Q := by
  rw [ev_d0Q hTT]
  congr 1
  have h : ∀ m : Fin r, ((if (M.vc l : M.Var r) = M.vc m then (-1 : ℂ) else 0) +
      (if (M.vc l : M.Var r) = M.vcb m then (-1 : ℂ) else 0)) = if l = m then (-1 : ℂ) else 0 := fun m => by
    rw [if_neg (Formalism.FourierDecayAlt.P.MAx1.vc_vcb l m), add_zero]
    by_cases hlm : l = m
    · rw [if_pos hlm, if_pos ((Formalism.FourierDecayAlt.P.MAx1.vc_inj l m).2 hlm)]
    · rw [if_neg hlm, if_neg (fun h => hlm ((Formalism.FourierDecayAlt.P.MAx1.vc_inj l m).1 h))]
  simp [h]

theorem ev_d0Q_cb (hTT : 0 ≤ TT) (l : Fin r) : eulerQ (M.vcb l) (d0Q : SmQ r TT) = (-1 : ℂ) • d0Q := by
  rw [ev_d0Q hTT]
  congr 1
  have h : ∀ m : Fin r, ((if (M.vcb l : M.Var r) = M.vc m then (-1 : ℂ) else 0) +
      (if (M.vcb l : M.Var r) = M.vcb m then (-1 : ℂ) else 0)) = if l = m then (-1 : ℂ) else 0 := fun m => by
    rw [if_neg (Formalism.FourierDecayAlt.P.MAx1.vc_vcb m l).symm, zero_add]
    by_cases hlm : l = m
    · rw [if_pos hlm, if_pos ((Formalism.FourierDecayAlt.P.MAx1.vcb_inj l m).2 hlm)]
    · rw [if_neg hlm, if_neg (fun h => hlm ((Formalism.FourierDecayAlt.P.MAx1.vcb_inj l m).1 h))]
  simp [h]

theorem ev_kc (hTT : 0 ≤ TT) (l : Fin r) : eulerQ (M.vc l) (coordQ (M.vc l) * d0Q : SmQ r TT) = 0 := by
  rw [Formalism.FourierDecayAlt.P.analytic_leibniz r TT, ev_d0Q_c hTT, Formalism.FourierDecayAlt.P.analytic_coordinates r TT, if_pos rfl]
  simp

theorem ev_kcb (hTT : 0 ≤ TT) (l : Fin r) : eulerQ (M.vcb l) (coordQ (M.vcb l) * d0Q : SmQ r TT) = 0 := by
  rw [Formalism.FourierDecayAlt.P.analytic_leibniz r TT, ev_d0Q_cb hTT, Formalism.FourierDecayAlt.P.analytic_coordinates r TT, if_pos rfl]
  simp

theorem adj_fn (h hb : SmQ r TT) (hc : cj hb = h) : IsAdj ((anQ r TT).fnP h hb) := by
  refine ⟨fun f hf => test_mul_left h hf, fun g hg => test_mul_left hb hg, fun f hf g hg => ?_⟩
  show ip0 (h * f) g = ip0 f (hb * g)
  unfold ip0
  congr 1; funext q
  have e := congrArg (fun u : SmQ r TT => (u : Qp r TT → ℂ) q) hc
  simp only [cj_apply] at e
  simp only [Subalgebra.coe_mul, Pi.mul_apply, map_mul, e]
  ring

theorem adj_der (hTT : 0 ≤ TT) {v w : M.Var r} (hb : Bar v w) (m mb κ : SmQ r TT)
    (hm : cj mb = m) (hκ : m * d0Q = Ring.inverse (coordQ v) * κ) (hκ0 : eulerQ v κ = 0)
    (a : (anQ r TT).Pr) (h1 : ∀ f, a.1 f = m * eulerQ v f) (h2 : ∀ g, a.2.unop g = -(mb * eulerQ w g)) :
    IsAdj a := by
  refine ⟨fun f hf => ?_, fun g hg => ?_, fun f hf g hg => ?_⟩
  · exact (congrArg (fun t : SmQ r TT => t ∈ Test r TT) (h1 f)).mpr (test_mul_left m (test_euler v hf))
  · exact (congrArg (fun t : SmQ r TT => t ∈ Test r TT) (h2 g)).mpr
      (test_neg (test_mul_left mb (test_euler w hg)))
  · have main : ip0 (m * eulerQ v f) g = ip0 f (-(mb * eulerQ w g)) := by
      rw [inner_neg_right_alt, eq_neg_iff_add_eq_zero, inner_eq_integral_alt, inner_eq_integral_alt,
        ← IE_add (test_mul_right (test_mul_right (test_mul_left m (test_euler v hf)) _) _)
          (test_mul_right (test_mul_right hf _) _)]
      have key : m * eulerQ v f * cj g * d0Q + f * cj (mb * eulerQ w g) * d0Q =
          Ring.inverse (coordQ v) * eulerQ v (f * cj g * κ) := by
        rw [cj_mul, hm, ← ev_cj hb, Formalism.FourierDecayAlt.P.analytic_leibniz r TT v (f * cj g) κ, hκ0,
          Formalism.FourierDecayAlt.P.analytic_leibniz r TT v f (cj g)]
        linear_combination (eulerQ v f * cj g + f * eulerQ v (cj g)) * hκ
      rw [key]
      exact IE_inv_euler hTT v (test_mul_right (test_mul_right hf _) _)
    calc ip0 (a.1 f) g = ip0 (m * eulerQ v f) g := congrArg (fun t => ip0 t g) (h1 f)
      _ = ip0 f (-(mb * eulerQ w g)) := main
      _ = ip0 f (a.2.unop g) := (congrArg (fun t => ip0 f t) (h2 g)).symm

end

end Formalism.FourierDecayAlt.P.MAx2.Adj

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.MAx2.Adj MeasureTheory
open scoped ComplexConjugate

theorem adjoint_closed : Formalism.FourierDecayAlt.MA.AdjClosed := fun _ _ =>
  ⟨isAdj_one, fun _ _ ha hb => ⟨isAdj_add ha hb, isAdj_mul ha hb⟩, fun z _ ha => isAdj_smul z ha,
    fun _ ha => isAdj_star ha⟩

theorem adjoint_algebra_of_parts : Formalism.FourierDecayAlt.MA.AdjAlgOfParts := by
  intro hG hC r TT hTT a ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact hG r TT hTT x hx
  | algebraMap z => exact isAdj_alg z
  | add x y _ _ hx hy => exact ((hC r TT).2.1 x y hx hy).1
  | mul x y _ _ hx hy => exact ((hC r TT).2.1 x y hx hy).2

theorem adjoint_matrix : Formalism.FourierDecayAlt.MA.AdjMatrix := by
  intro P a ha f g hf hg
  unfold ipA actA
  calc ∑ π, ip0 (∑ π', (a π π').1 (f π')) (g π)
      = ∑ π, ∑ π', ip0 ((a π π').1 (f π')) (g π) :=
        Finset.sum_congr rfl fun π _ => inner_sum_left_alt _ _ (fun π' _ => (ha π π').1 _ (hf π')) _
    _ = ∑ π, ∑ π', ip0 (f π') ((a π π').2.unop (g π)) :=
        Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun π' _ => (ha π π').2.2 _ (hf π') _ (hg π)
    _ = ∑ π', ∑ π, ip0 (f π') ((a π π').2.unop (g π)) := Finset.sum_comm
    _ = ∑ π', ip0 (f π') (∑ π, ((star a) π' π).1 (g π)) := by
        refine Finset.sum_congr rfl fun π' _ => ?_
        exact (inner_sum_right_alt (hf π') Finset.univ (fun π => ((star a) π' π).1 (g π))).symm

theorem measure_joint : Formalism.FourierDecayAlt.MA.MeasureJoint := by
  intro k r TT f hf
  have hQ : MeasurableSet (Qset r TT) := (Qset_open r TT).measurableSet
  have e1 : ∫⁻ q, ENNReal.ofReal (‖f q‖ ^ 2) ∂muq k r TT =
      ∫⁻ q : Qp r TT, (fun x => ENNReal.ofReal (‖ext f x‖ ^ 2)) (q : E r) ∂muq k r TT := by
    congr 1; funext q; simp [ext, q.2]
  have e2 : ∫⁻ q, ENNReal.ofReal (‖((Real.sqrt (wq k q.1 TT) : ℝ) : ℂ) * f q‖ ^ 2) ∂mu0 r TT =
      ∫⁻ q : Qp r TT, (fun x => ENNReal.ofReal (‖((Real.sqrt (wq k x TT) : ℝ) : ℂ) * ext f x‖ ^ 2)) (q : E r)
        ∂mu0 r TT := by
    congr 1; funext q; simp [ext, q.2]
  have hm1 : Measurable fun x : E r => dens0 x * ENNReal.ofReal (wq k x TT) :=
    density_measurable.mul (ENNReal.measurable_ofReal.comp (wq_cont k).measurable)
  rw [e1, e2, muq, mu0, lintegral_subtype_comap hQ (fun x => ENNReal.ofReal (‖ext f x‖ ^ 2)),
    lintegral_subtype_comap hQ (fun x => ENNReal.ofReal (‖((Real.sqrt (wq k x TT) : ℝ) : ℂ) * ext f x‖ ^ 2)),
    restrict_withDensity hQ, restrict_withDensity hQ,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ hm1
      (ae_of_all _ fun x => ENNReal.mul_lt_top (density_lt_top x) ENNReal.ofReal_lt_top),
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ density_measurable (ae_of_all _ fun x => density_lt_top x)]
  refine setLIntegral_congr_fun hQ (fun x hx => ?_)
  have hw := wq_nonneg (TT := TT) k hx
  simp only [Pi.mul_apply]
  rw [mul_assoc, ← ENNReal.ofReal_mul hw]
  congr 2
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt hw]

theorem adjoint_generators : Formalism.FourierDecayAlt.MA.AdjGens := by
  intro r TT hTT a ha
  have uc : ∀ v : M.Var r, ∀ q : Qp r TT, ((coordQ v : SmQ r TT) : Qp r TT → ℂ) q ≠ 0 := unit_coord hTT
  rcases ha with ((((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ha)
  · exact adj_fn _ _ (cj_coord (bar_c l))
  · exact adj_fn _ _ ((cj_inv _ (uc _)).trans (congrArg Ring.inverse (cj_coord (bar_c l))))
  · exact adj_fn _ _ (cj_coord (bar_cb l))
  · exact adj_fn _ _ ((cj_inv _ (uc _)).trans (congrArg Ring.inverse (cj_coord (bar_cb l))))
  · exact adj_der hTT (bar_c l) 1 1 (coordQ (M.vc l) * d0Q) cj_one
      (by rw [← mul_assoc, inv_mul_coord hTT, one_mul]) (ev_kc hTT l) _
      (fun f => (one_mul _).symm) (fun g => by rw [one_mul]; rfl)
  · exact adj_der hTT (bar_cb l) 1 1 (coordQ (M.vcb l) * d0Q) cj_one
      (by rw [← mul_assoc, inv_mul_coord hTT, one_mul]) (ev_kcb hTT l) _
      (fun f => (one_mul _).symm) (fun g => by rw [one_mul]; rfl)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact adj_fn _ _ (cj_coord conjugate_zeta_pair)
    · exact adj_fn _ _ ((cj_inv _ (uc _)).trans (congrArg Ring.inverse (cj_coord conjugate_zeta_pair)))
    · exact adj_fn _ _ (cj_coord bar_zb)
    · exact adj_fn _ _ ((cj_inv _ (uc _)).trans (congrArg Ring.inverse (cj_coord bar_zb)))
    · exact adj_fn _ _ cj_gg
    · exact adj_fn _ _ ((cj_inv _ gg_ne).trans (congrArg Ring.inverse cj_gg))
    · exact adj_der hTT conjugate_zeta_pair (Ring.inverse (coordQ M.vz)) (Ring.inverse (coordQ M.vzb)) d0Q
        ((cj_inv _ (uc _)).trans (congrArg Ring.inverse (cj_coord conjugate_zeta_pair))) rfl (ev_d0Q_alt hTT) _
        (fun f => rfl) (fun g => rfl)
    · exact adj_der hTT bar_zb (Ring.inverse (coordQ M.vzb)) (Ring.inverse (coordQ M.vz)) d0Q
        ((cj_inv _ (uc _)).trans (congrArg Ring.inverse (cj_coord bar_zb))) rfl (ev_d0Q_zb hTT) _
        (fun f => rfl) (fun g => rfl)

theorem adjoint_algebra : Formalism.FourierDecayAlt.MA.AdjAlg :=
  adjoint_algebra_of_parts adjoint_generators adjoint_closed

end Formalism.FourierDecayAlt.P
