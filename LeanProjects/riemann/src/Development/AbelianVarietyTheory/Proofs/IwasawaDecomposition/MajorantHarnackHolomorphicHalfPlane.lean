import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantConjugateTransfer

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Matrix

namespace GlobalTheory.MajHarnack

theorem schwarz_half {T R : ℝ} {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f {w | T < w.im})
    (hb : ∀ z : ℂ, T < z.im → ‖f z‖ ≤ R) {w w' : ℂ} (hw : T < w.im) (hw' : T < w'.im)
    (h0 : f w = 0) :
    ‖f w'‖ ≤ R * ‖(w' - w) / (w' - conj w - 2 * T * I)‖ := by
  set wb : ℂ := conj w + 2 * T * I with hwb
  set φ : ℂ → ℂ := fun ζ => (w - wb * ζ) / (1 - ζ) with hφ
  have hne : ∀ ζ ∈ Metric.ball (0 : ℂ) 1, (1 - ζ) ≠ 0 := by
    intro ζ hζ h
    have : ζ = 1 := by linear_combination -h
    simp [this] at hζ
  have hmaps : Set.MapsTo φ (Metric.ball (0 : ℂ) 1) {w | T < w.im} := by
    intro ζ hζ
    have h1 := hne ζ hζ
    have hn : 0 < Complex.normSq (1 - ζ) := Complex.normSq_pos.mpr h1
    have hζ' : ζ.re ^ 2 + ζ.im ^ 2 < 1 := by
      have h2 : ‖ζ‖ < 1 := by simpa using hζ
      have h3 : ‖ζ‖ ^ 2 < 1 := by nlinarith [norm_nonneg ζ]
      rw [Complex.sq_norm, Complex.normSq_apply] at h3
      nlinarith
    show T < ((w - wb * ζ) / (1 - ζ)).im
    rw [Complex.div_im, ← sub_div, lt_div_iff₀ hn, Complex.normSq_apply]
    simp [hwb]
    nlinarith [mul_pos (sub_pos.mpr hw) (sub_pos.mpr hζ')]
  have hdφ : DifferentiableOn ℂ φ (Metric.ball (0 : ℂ) 1) := by
    refine DifferentiableOn.div (by fun_prop) (by fun_prop) hne
  have hden : w' - wb ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp [hwb] at this
    linarith
  have hden' : w - wb ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp [hwb] at this
    linarith
  have hφ0 : φ 0 = w := by simp [hφ]
  have hζ : (w' - w) / (w' - wb) ∈ Metric.ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_div, div_lt_one (norm_pos_iff.mpr hden)]
    refine lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) ?_
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp [hwb]
    nlinarith [mul_pos (sub_pos.mpr hw) (sub_pos.mpr hw')]
  have hφ1 : φ ((w' - w) / (w' - wb)) = w' := by
    simp only [hφ]
    have : 1 - (w' - w) / (w' - wb) = (w - wb) / (w' - wb) := by field_simp; ring
    rw [this]
    field_simp
    ring
  have key := Complex.dist_le_div_mul_dist_of_mapsTo_ball (R₂ := R) (hd.comp hdφ hmaps)
    (fun ζ hζ => by
      simp only [Function.comp_apply, hφ0, h0, mem_closedBall_zero_iff]
      exact hb _ (hmaps hζ)) hζ
  simp only [Function.comp_apply, hφ0, hφ1, h0, dist_zero_right, div_one] at key
  rwa [sub_sub]

theorem rho_sq {T : ℝ} {w w' : ℂ} (hw : T < w.im) (hw' : T < w'.im) :
    ‖(w' - w) / (w' - conj w - 2 * T * I)‖ ^ 2 * (‖w - w'‖ ^ 2 + 4 * ((w.im - T) * (w'.im - T))) =
      ‖w - w'‖ ^ 2 := by
  have hden : w' - conj w - 2 * T * I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have e : ‖w - w'‖ ^ 2 + 4 * ((w.im - T) * (w'.im - T)) = ‖w' - conj w - 2 * T * I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp
    ring
  rw [e, norm_div, norm_sub_rev w' w]
  have := norm_pos_iff.mpr hden
  field_simp

theorem real_bound {a b p q ρ d m s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hρ : 0 ≤ ρ) (hd : 0 ≤ d) (hm : 0 < m) (hρd : ρ ^ 2 * (d + 4 * m) = d) (hba : b ≤ ρ * a)
    (hs : s = a ^ 2 - b ^ 2) (hs' : s ≤ p * a + q * b) :
    2 * s - (p ^ 2 - q ^ 2) ≤ (2 + d / m) * (p ^ 2 + q ^ 2) := by
  have hk : 0 < 1 - ρ ^ 2 := by
    by_contra h
    nlinarith
  have hK : 2 + d / m = 2 * (1 + ρ ^ 2) / (1 - ρ ^ 2) := by
    field_simp
    nlinarith
  have h1 : s ≤ 2 * a * (p + ρ * q) - (1 - ρ ^ 2) * a ^ 2 := by
    have : b ^ 2 ≤ (ρ * a) ^ 2 := by gcongr
    nlinarith [mul_le_mul_of_nonneg_left hba hq]
  have h2 : (1 - ρ ^ 2) * s ≤ (p + ρ * q) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left h1 hk.le, sq_nonneg ((1 - ρ ^ 2) * a - (p + ρ * q))]
  rw [hK, div_mul_eq_mul_div, le_div_iff₀ hk]
  nlinarith [mul_nonneg hρ (sq_nonneg (p - q)), mul_nonneg (sq_nonneg (1 - ρ)) (add_nonneg (sq_nonneg p) (sq_nonneg q))]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem span_pos {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) {c : Fin X.p0 → ℂ} (hc : c ≠ 0) :
    0 < (hermC τ.1 X.Gm (∑ a, c a • X.colP x τ a) (∑ a, c a • X.colP x τ a)).re := by
  rw [hermC_quad]
  exact quad_re_pos (X.gramPos_posDef hx τ) hc

theorem span_nonneg {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (c : Fin X.p0 → ℂ) :
    0 ≤ (hermC τ.1 X.Gm (∑ a, c a • X.colP x τ a) (∑ a, c a • X.colP x τ a)).re := by
  rw [hermC_quad]
  exact quad_re_nonneg (X.gramPos_posDef hx τ).posSemidef c

theorem ppos_span {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (c : Fin X.p0 → ℂ) :
    X.ppos x τ (∑ a, c a • X.colP x τ a) = ∑ a, c a • X.colP x τ a := by
  apply X.ppos_eq_of x τ (X.gramPos_det_ne hx τ)
  intro b
  show hermC τ.1 X.Gm (∑ a, c a • X.colP x τ a - ∑ a, c a • X.colP x τ a) (X.colP x τ b) = 0
  rw [sub_self, hermC_zero_left]

theorem ppos_congr (x : Frame X.Ψ r) (τ : X.Ψ) {u u' : Fin r → ℂ}
    (h : ∀ b, hermC τ.1 X.Gm u (X.colP x τ b) = hermC τ.1 X.Gm u' (X.colP x τ b)) :
    X.ppos x τ u = X.ppos x τ u' := by
  simp only [Data.ppos_eq, h]

theorem ppos_neg {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u : Fin r → ℂ) :
    X.ppos x τ (u - X.ppos x τ u) = 0 := by
  rw [Data.ppos_sub, X.ppos_ppos hx, sub_self]

theorem herm_pos_neg {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.ppos x τ u) (v - X.ppos x τ v) = 0 := by
  rw [X.hermC_ppos_left hx, ppos_neg X hx, hermC_zero_right]

theorem Hf_pos {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u v : Fin r → ℂ) :
    X.Hf x τ (X.ppos x τ u) v = hermC τ.1 X.Gm (X.ppos x τ u) v := by
  rw [Data.Hf_eq_two_ppos, X.ppos_ppos hx]; ring

theorem Hf_neg {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u v : Fin r → ℂ) :
    X.Hf x τ (u - X.ppos x τ u) v = - hermC τ.1 X.Gm (u - X.ppos x τ u) v := by
  rw [Data.Hf_eq_two_ppos, ppos_neg X hx, hermC_zero_left]; ring

theorem herm_right_neg {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm u (v - X.ppos x τ v) =
      - X.Hf x τ (u - X.ppos x τ u) (v - X.ppos x τ v) := by
  rw [Hf_neg X hx, hermC_sub_left, herm_pos_neg X hx]; ring

theorem herm_split {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm u v = X.Hf x τ (X.ppos x τ u) (X.ppos x τ v) -
      X.Hf x τ (u - X.ppos x τ u) (v - X.ppos x τ v) := by
  have h := herm_right_neg X hx τ u v
  rw [hermC_sub_right, X.hermC_ppos_right hx] at h
  rw [Hf_pos X hx]
  linear_combination h

theorem herm_self_re {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u : Fin r → ℂ) :
    (hermC τ.1 X.Gm u u).re = X.maj x τ (X.ppos x τ u) - X.maj x τ (u - X.ppos x τ u) := by
  rw [herm_split X hx, X.Hf_self hx, X.Hf_self hx]; simp

theorem maj_eq {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u : Fin r → ℂ) :
    X.maj x τ u = 2 * (hermC τ.1 X.Gm (X.ppos x τ u) (X.ppos x τ u)).re -
      (hermC τ.1 X.Gm u u).re := by
  have h := X.Hf_self hx τ u
  rw [Data.Hf_eq_two_ppos, X.hermC_ppos_left hx] at h
  have := congrArg Complex.re h
  simp at this
  linarith

theorem maj_split {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u : Fin r → ℂ) :
    X.maj x τ u = X.maj x τ (X.ppos x τ u) + X.maj x τ (u - X.ppos x τ u) := by
  rw [maj_eq X hx τ u, herm_self_re X hx τ u, ← Hf_pos X hx, X.Hf_self hx]
  simp; ring

theorem cs' {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u v : Fin r → ℂ) :
    ‖X.Hf x τ u v‖ ≤ Real.sqrt (X.maj x τ u) * Real.sqrt (X.maj x τ v) := by
  rw [← Real.sqrt_mul (MajorantConjugateTransfer.maj_nonneg X hx τ u)]
  exact Real.le_sqrt_of_sq_le (MajorantConjugateTransfer.cs X hx τ u v)

noncomputable def cross (y x : Frame X.Ψ r) (τ : X.Ψ) : Matrix (Fin X.p0) (Fin X.p0) ℂ :=
  Matrix.of fun b a => hermC τ.1 X.Gm (X.colP y τ a) (X.colP x τ b)

theorem cross_mulVec (y x : Frame X.Ψ r) (τ : X.Ψ) (c : Fin X.p0 → ℂ) (b : Fin X.p0) :
    (cross X y x τ *ᵥ c) b = hermC τ.1 X.Gm (∑ a, c a • X.colP y τ a) (X.colP x τ b) := by
  rw [hermC_sum_left]
  simp only [cross, Matrix.mulVec, dotProduct, Matrix.of_apply, hermC_smul_left, mul_comm]

theorem cross_det {y x : Frame X.Ψ r} (hy : y ∈ X.dom) (hx : x ∈ X.dom) (τ : X.Ψ) :
    (cross X y x τ).det ≠ 0 := by
  intro h
  obtain ⟨c, hc, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have hp := span_pos X hy τ hc
  have hne : (∑ a, c a • X.colP y τ a) ≠ 0 := by
    intro e; rw [e, hermC_zero_left] at hp; simp at hp
  have := X.neg_of_perp hx τ hne fun b => by rw [← cross_mulVec, h0]; rfl
  linarith

theorem diff_det {n : ℕ} {s : Set ℂ} {M : ℂ → Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ a b, DifferentiableOn ℂ (fun z => M z a b) s) :
    DifferentiableOn ℂ (fun z => (M z).det) s := by
  simp only [Matrix.det_apply']
  refine DifferentiableOn.fun_sum fun σ _ => DifferentiableOn.const_mul ?_ _
  exact DifferentiableOn.fun_finsetProd fun i _ => h _ _

theorem diff_herm {s : Set ℂ} {x : ℂ → Frame X.Ψ r} (hx : DifferentiableOn ℂ x s) (τ : X.Ψ)
    (a : Fin X.p0) (v : Fin r → ℂ) :
    DifferentiableOn ℂ (fun z => hermC τ.1 X.Gm (X.colP (x z) τ a) v) s := by
  unfold hermC
  refine DifferentiableOn.fun_sum fun i _ => DifferentiableOn.fun_sum fun j _ => ?_
  refine DifferentiableOn.mul_const (DifferentiableOn.mul_const ?_ _) _
  exact differentiableOn_pi.mp (differentiableOn_pi.mp (differentiableOn_pi.mp hx τ) i) _

theorem neg_le {T : ℝ} {x : ℂ → Frame X.Ψ r} (hd : DifferentiableOn ℂ x {w | T < w.im})
    (hx : ∀ w : ℂ, T < w.im → x w ∈ X.dom) {w w' : ℂ} (hw : T < w.im) (hw' : T < w'.im)
    (τ : X.Ψ) (c : Fin X.p0 → ℂ) (u : Fin r → ℂ) (hu : u = ∑ a, c a • X.colP (x w') τ a) :
    Real.sqrt (X.maj (x w) τ (u - X.ppos (x w) τ u)) ≤
      ‖(w' - w) / (w' - conj w - 2 * T * I)‖ * Real.sqrt (X.maj (x w) τ (X.ppos (x w) τ u)) := by
  classical
  have h0 := hx w hw
  set m : Fin X.p0 → ℂ := fun b => hermC τ.1 X.Gm u (X.colP (x w) τ b) with hm
  set γ : ℂ → Fin X.p0 → ℂ := fun z => (cross X (x z) (x w) τ)⁻¹ *ᵥ m with hγ
  set U : ℂ → Fin r → ℂ := fun z => ∑ a, γ z a • X.colP (x z) τ a with hU
  have hunit : ∀ z : ℂ, T < z.im → IsUnit (cross X (x z) (x w) τ).det := fun z hz =>
    isUnit_iff_ne_zero.mpr (cross_det X (hx z hz) h0 τ)
  have hPU : ∀ z : ℂ, T < z.im → X.ppos (x w) τ (U z) = X.ppos (x w) τ u := by
    intro z hz
    refine ppos_congr X _ τ fun b => ?_
    simp only [hU]
    rw [← cross_mulVec, hγ, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hunit z hz),
      Matrix.one_mulVec]
  have hUw' : U w' = u := by
    have : m = cross X (x w') (x w) τ *ᵥ c := by
      funext b; rw [cross_mulVec, ← hu]
    simp only [hU, hγ]
    rw [this, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hunit w' hw'), Matrix.one_mulVec, hu]
  have hdγ : ∀ a, DifferentiableOn ℂ (fun z => γ z a) {w | T < w.im} := by
    intro a
    have hc : ∀ a b, DifferentiableOn ℂ (fun z => cross X (x z) (x w) τ a b) {w | T < w.im} :=
      fun a b => diff_herm X hd τ b _
    have h1 : DifferentiableOn ℂ (fun z => ((cross X (x z) (x w) τ).updateCol a m).det /
        (cross X (x z) (x w) τ).det) {w | T < w.im} := by
      refine DifferentiableOn.div (diff_det fun i j => ?_) (diff_det hc)
        fun z hz => cross_det X (hx z hz) h0 τ
      simp only [Matrix.updateCol_apply]
      split_ifs
      · exact differentiableOn_const _
      · exact hc _ _
    refine h1.congr fun z hz => ?_
    have h2 := congrFun (Matrix.det_smul_inv_mulVec_eq_cramer _ m (hunit z hz)) a
    rw [Matrix.cramer_apply] at h2
    rw [eq_div_iff (cross_det X (hx z hz) h0 τ), ← h2, mul_comm]
    rfl
  set e := u - X.ppos (x w) τ u with he
  set f : ℂ → ℂ := fun z => hermC τ.1 X.Gm (U z) e with hf
  have hdf : DifferentiableOn ℂ f {w | T < w.im} := by
    simp only [hf, hU, hermC_sum_left, hermC_smul_left]
    exact DifferentiableOn.fun_sum fun a _ => (hdγ a).mul (diff_herm X hd τ a e)
  have hf0 : f w = 0 := by
    simp only [hf, hU]
    rw [← ppos_span X h0, he, herm_pos_neg X h0]
  set A := Real.sqrt (X.maj (x w) τ (X.ppos (x w) τ u))
  set B := Real.sqrt (X.maj (x w) τ e) with hB
  have hb : ∀ z : ℂ, T < z.im → ‖f z‖ ≤ A * B := by
    intro z hz
    simp only [hf]
    rw [he, herm_right_neg X h0, norm_neg]
    refine (cs' X h0 τ _ _).trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
    refine Real.sqrt_le_sqrt ?_
    have h1 := herm_self_re X h0 τ (U z)
    have h2 : 0 ≤ (hermC τ.1 X.Gm (U z) (U z)).re := span_nonneg X (hx z hz) τ _
    rw [← hPU z hz]
    linarith
  have key := schwarz_half hdf hb hw hw' hf0
  have hfw : ‖f w'‖ = B * B := by
    simp only [hf]
    rw [hUw', he, herm_right_neg X h0, norm_neg, X.Hf_self h0, hB,
      Real.mul_self_sqrt (MajorantConjugateTransfer.maj_nonneg X h0 τ _), Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (MajorantConjugateTransfer.maj_nonneg X h0 τ _)]
  rw [hfw] at key
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  rcases hB0.eq_or_lt with h | h
  · exact h.symm.trans_le (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
  · refine le_of_mul_le_mul_right ?_ h
    exact key.trans_eq (by ring)

end GlobalTheory.MajHarnack

namespace GlobalTheory

open MajHarnack in

theorem maj_harnack : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N)
    (T : ℝ) (x : ℂ → Frame X.Ψ N), DifferentiableOn ℂ x {w | T < w.im} →
    (∀ w : ℂ, T < w.im → x w ∈ X.dom) → ∀ w w' : ℂ, T < w.im → T < w'.im →
    ∀ (τ : X.Ψ) (v : Fin N → ℂ), X.maj (x w') τ v ≤
      (2 + ‖w - w'‖ ^ 2 / ((w.im - T) * (w'.im - T))) * X.maj (x w) τ v := by
  intro E _ _ _ N X T x hd hx w w' hw hw' τ v
  have h0 := hx w hw
  have h1 := hx w' hw'
  set u := X.ppos (x w') τ v with hu
  have hba := neg_le X hd hx hw hw' τ _ u (X.ppos_eq (x w') τ v)
  have nn := MajorantConjugateTransfer.maj_nonneg X h0 τ
  have key := real_bound (s := (hermC τ.1 X.Gm u u).re)
    (p := Real.sqrt (X.maj (x w) τ (X.ppos (x w) τ v)))
    (q := Real.sqrt (X.maj (x w) τ (v - X.ppos (x w) τ v)))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (norm_nonneg _) (sq_nonneg _) (mul_pos (sub_pos.mpr hw) (sub_pos.mpr hw')) (rho_sq hw hw') hba
    (by rw [Real.sq_sqrt (nn _), Real.sq_sqrt (nn _), herm_self_re X h0])
    (by
      rw [hu, ← X.hermC_ppos_right h1, ← hu, herm_split X h0]
      refine (Complex.re_le_norm _).trans ((norm_sub_le _ _).trans ?_)
      exact add_le_add (cs' X h0 τ _ _) (cs' X h0 τ _ _))
  rw [Real.sq_sqrt (nn _), Real.sq_sqrt (nn _), ← herm_self_re X h0, ← maj_split X h0] at key
  rw [maj_eq X h1]
  exact key

end GlobalTheory
