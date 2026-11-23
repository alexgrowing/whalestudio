import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJGlobalBound
import GroundTheory.AutomorphicForms.GL2.GJGlobalEntire

open MeasureTheory Set Filter NumberField ComplexConjugate Asymptotics
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace GJGlobal

open Reduction AutomorphicForm RightCosetSpace GJMatrix

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem continuousOn_dite {f : {r : ℝ // 0 < r} → ℂ} (hf : Continuous f) :
    ContinuousOn (fun t : ℝ => if h : 0 < t then f ⟨t, h⟩ else 0) (Ioi 0) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have e : (Ioi (0 : ℝ)).domRestrict (fun t : ℝ => if h : 0 < t then f ⟨t, h⟩ else 0) =
      fun t : Ioi (0 : ℝ) => f ⟨t.1, t.2⟩ := by
    funext t
    rw [Set.domRestrict_apply, dif_pos (show (0 : ℝ) < t.1 from t.2)]
  rw [e]
  exact hf.comp (continuous_subtype_val.subtype_mk _)

theorem mellinConvergent_of_bound {J : ℝ → ℂ} (hJ : ContinuousOn J (Ioi 0)) {B : ℝ → ℝ} {V : ℝ}
    (hB : ∀ t : ℝ, 0 < t → ‖J t‖ ≤ V * B t) {w : ℂ}
    (hint : IntegrableOn (fun t : ℝ => t ^ (w.re - 1) * B t) (Ioi 0)) :
    MellinConvergent J w := by
  unfold MellinConvergent
  have hc : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (w - 1) • J t) (Ioi 0) := by
    refine ContinuousOn.smul (f := fun t : ℝ => (t : ℂ) ^ (w - 1)) (g := J) (fun t ht => ?_) hJ
    exact (Complex.continuousAt_ofReal_cpow_const t (w - 1)
      (Or.inr (ne_of_gt (show (0 : ℝ) < t from ht)))).continuousWithinAt
  refine Integrable.mono' (hint.const_mul V) (hc.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 0 < t) => ?_)
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re]
  calc t ^ (w.re - 1) * ‖J t‖ ≤ t ^ (w.re - 1) * (V * B t) :=
        mul_le_mul_of_nonneg_left (hB t ht) (Real.rpow_nonneg ht.le _)
    _ = V * (t ^ (w.re - 1) * B t) := by ring

theorem continuous_posInv : Continuous fun s : {r : ℝ // 0 < r} => s⁻¹ := by
  have h : Continuous fun s : {r : ℝ // 0 < r} => ((s : ℝ))⁻¹ :=
    continuous_subtype_val.inv₀ fun s => s.2.ne'
  exact h.subtype_mk _

theorem continuous_tsum_inv {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ}
    (hΦ : Φ ∈ matrixSchwartzBruhat K n) :
    Continuous (fun p : {r : ℝ // 0 < r} × AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n =>
      ∑' γ : GL (Fin n) K, Φ (((centralSection K n p.1 * p.2.1 * AdelicGLn.diagonal K n γ *
        p.2.2)⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) := by
  have hc := continuous_tsum_GL hΦ
  have hm : Continuous fun p : {r : ℝ // 0 < r} × AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n =>
      (p.1⁻¹, p.2.2⁻¹, p.2.1⁻¹) :=
    (continuous_posInv.comp continuous_fst).prodMk
      ((continuous_snd.comp continuous_snd).inv.prodMk (continuous_fst.comp continuous_snd).inv)
  have h := hc.comp hm
  refine h.congr fun p => ?_
  simp only [Function.comp_apply]
  rw [← (Equiv.inv (GL (Fin n) K)).tsum_eq]
  refine tsum_congr fun γ => ?_
  have e := inv_centralSection_mul p.1 p.2.1⁻¹ p.2.2 γ
  rw [inv_inv] at e
  simp only [Equiv.inv_apply]
  rw [e]

set_option maxHeartbeats 1600000 in

theorem globalZeta_entire_functionalEquation (hn : 2 ≤ n) (μ : Measure (normOneGL K n))
    [μ.IsHaarMeasure] (ν : Measure (AdelicGLn.AdelicGL K n)) [ν.IsHaarMeasure]
    {φ₁ φ₂ : AdelicGLn.AdelicGL K n → ℂ} (h₁ : φ₁ ∈ cuspForms K n) (h₂ : φ₂ ∈ cuspForms K n)
    (hA : ∀ (s : {r : ℝ // 0 < r}) (x : AdelicGLn.AdelicGL K n),
      φ₁ (centralSection K n s * x) = φ₁ x)
    {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ} (hΦ : Φ ∈ matrixSchwartzBruhat K n) :
    ∃ σ₀ : ℝ, ∃ Λ Λ' : ℂ → ℂ, Differentiable ℂ Λ ∧ Differentiable ℂ Λ' ∧
      (∀ s : ℂ, σ₀ < s.re → Integrable (zetaIntegrand Φ (matrixCoeff μ φ₁ φ₂) s) ν ∧
        globalZeta ν Φ (matrixCoeff μ φ₁ φ₂) s = Λ s) ∧
      (∀ s : ℂ, σ₀ < s.re → Integrable (zetaIntegrand (adelicMatrixFourier K Φ)
          (fun g => matrixCoeff μ φ₁ φ₂ g⁻¹) s) ν ∧
        globalZeta ν (adelicMatrixFourier K Φ) (fun g => matrixCoeff μ φ₁ φ₂ g⁻¹) s = Λ' s) ∧
      ∀ s : ℂ, Λ s = Λ' (1 - s) := by
  have hn0 : 0 < n := by omega
  have hΦh := adelicMatrixFourier_mem hΦ
  have hΦc : Continuous Φ := continuous_of_mem_matrixSchwartzBruhat hΦ
  have hΦhc : Continuous (adelicMatrixFourier K Φ) := continuous_of_mem_matrixSchwartzBruhat hΦh
  have h₁c : Continuous φ₁ := h₁.1.continuous
  have h₂c : Continuous φ₂ := h₂.1.continuous
  set V : ℝ := (μ (fundamentalDomain (rationalGLOne K n))).toReal ^ 2 with hV

  set Ξ₁ : AdelicGLn.AdelicGL K n → ℂ := fun g => Φ (g : Matrix (Fin n) (Fin n) 𝔸[K]) with hΞ₁
  set Ξ₂ : AdelicGLn.AdelicGL K n → ℂ := fun g => adelicMatrixFourier K Φ
    ((g⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) with hΞ₂
  have hΞ₁c : Continuous Ξ₁ := hΦc.comp Units.continuous_val
  have hΞ₂c : Continuous Ξ₂ := hΦhc.comp (Units.continuous_val.comp continuous_inv)
  set J₁ : ℝ → ℂ := fun t => if h : 0 < t then thetaPairing μ φ₁ φ₂ Ξ₁ ⟨t, h⟩ else 0 with hJ₁
  set J₂ : ℝ → ℂ := fun t => if h : 0 < t then thetaPairing μ φ₁ φ₂ Ξ₂ ⟨t, h⟩ else 0 with hJ₂
  set J' : ℝ → ℂ := fun u => J₂ u⁻¹ with hJ'

  obtain ⟨C₁, M₁, -, hC₁⟩ := exists_bound_tsum hΦ h₁ h₂
  obtain ⟨C₂, M₂, -, hC₂⟩ := exists_bound_tsum hΦh h₂ h₁
  obtain ⟨_, _, _, hsum₂⟩ := exists_bound_GL_inv hn0 hΦ h₁ h₂ 0
  have hB₁ : ∀ (t : {r : ℝ // 0 < r}) (x y : normOneGL K n),
      ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ *
        ‖∑' γ : GL (Fin n) K, Ξ₁ (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
          AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n))‖ ≤
        C₁ * (max 1 (t : ℝ)⁻¹) ^ M₁ := by
    intro t x y
    obtain ⟨hs, hb⟩ := hC₁ x x.2 y y.2 t
    have hGL := tsum_norm_GL_le _ _ hs
    refine le_trans ?_ hb
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    simp only [hΞ₁, coe_mul_diagonal_mul]
    exact (norm_tsum_le_tsum_norm hGL.1).trans hGL.2
  have hB₂ : ∀ (t : {r : ℝ // 0 < r}) (x y : normOneGL K n),
      ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ *
        ‖∑' γ : GL (Fin n) K, Ξ₂ (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
          AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n))‖ ≤
        C₂ * (max 1 (t : ℝ)) ^ M₂ := by
    intro t x y
    obtain ⟨hs, hb⟩ := hC₂ y y.2 x x.2 t⁻¹
    have hGL := tsum_norm_GL_le _ _ hs
    have hsm := (hsum₂ t x y).1
    rw [mul_comm ‖φ₂ _‖]
    have e : ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ)⁻¹ = (t : ℝ) := inv_inv (t : ℝ)
    rw [e] at hb
    refine le_trans ?_ hb
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    refine (norm_tsum_le_tsum_norm hsm).trans ?_
    rw [tsum_norm_inv_eq]
    exact hGL.2
  have hB₁c : Continuous fun t : {r : ℝ // 0 < r} => C₁ * (max 1 (t : ℝ)⁻¹) ^ M₁ :=
    continuous_const.mul ((continuous_const.max (continuous_subtype_val.inv₀ fun t => t.2.ne')).rpow_const
      fun t => Or.inl (ne_of_gt (lt_of_lt_of_le one_pos (le_max_left _ _))))
  have hB₂c : Continuous fun t : {r : ℝ // 0 < r} => C₂ * (max 1 (t : ℝ)) ^ M₂ :=
    continuous_const.mul ((continuous_const.max continuous_subtype_val).rpow_const
      fun t => Or.inl (ne_of_gt (lt_of_lt_of_le one_pos (le_max_left _ _))))
  have hTP₁c : Continuous (thetaPairing μ φ₁ φ₂ Ξ₁) :=
    continuous_thetaPairing μ h₁c h₂c (continuous_tsum_GL hΦ) hB₁c hB₁
  have hTP₂c : Continuous (thetaPairing μ φ₁ φ₂ Ξ₂) :=
    continuous_thetaPairing μ h₁c h₂c (continuous_tsum_inv hΦh) hB₂c hB₂
  have hJ₁c : ContinuousOn J₁ (Ioi 0) := continuousOn_dite hTP₁c
  have hJ₂c : ContinuousOn J₂ (Ioi 0) := continuousOn_dite hTP₂c
  have hJ'c : ContinuousOn J' (Ioi 0) :=
    hJ₂c.comp (continuousOn_inv₀.mono fun t (ht : 0 < t) => ht.ne') fun t (ht : 0 < t) =>
      (show (0 : ℝ) < t⁻¹ from inv_pos.2 ht)

  have hsym : ∀ t : ℝ, 0 < t → J₁ t = (t : ℂ) ^ (-((n : ℝ) : ℂ)) * J' t⁻¹ := by
    intro t ht
    have hti : (0 : ℝ) < t⁻¹⁻¹ := by rw [inv_inv]; exact ht
    simp only [hJ₁, hJ', hJ₂, dif_pos ht, dif_pos hti]
    have e : (⟨t⁻¹⁻¹, hti⟩ : {r : ℝ // 0 < r}) = ⟨t, ht⟩ := Subtype.ext (inv_inv t)
    rw [e, thetaPairing_eq μ hn h₁ h₂ hΦ ⟨t, ht⟩]
    congr 1
    rw [Complex.ofReal_natCast, Complex.cpow_neg, Complex.cpow_natCast]
    push_cast
    rfl

  have hdec₁ : ∀ a : ℝ, J₁ =O[atTop] (· ^ (-a)) := by
    intro a
    obtain ⟨C, M, D, hb⟩ := exists_bound_GL hn0 hΦ h₁ h₂ a
    refine IsBigO.of_bound (V * D) ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
    simp only [hJ₁, dif_pos ht0]
    have h := norm_thetaPairing_le μ (Ξ := Ξ₁) (φ₁ := φ₁) (φ₂ := φ₂) ⟨t, ht0⟩
      (b := D * t ^ (-a)) fun x y => by
        have := hb ⟨t, ht0⟩ x y
        rw [if_neg (not_lt.2 ht)] at this
        exact this
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
    calc _ ≤ V * (D * t ^ (-a)) := h
      _ = V * D * t ^ (-a) := by ring
  have hdec' : ∀ a : ℝ, J' =O[atTop] (· ^ (-a)) := by
    intro a
    obtain ⟨C, M, D, hb⟩ := exists_bound_GL_inv hn0 hΦ h₁ h₂ a
    refine IsBigO.of_bound (V * D) ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
    have hu0 : 0 < u := lt_trans one_pos hu
    have hi0 : 0 < u⁻¹ := inv_pos.2 hu0
    have hi1 : u⁻¹ < 1 := inv_lt_one_of_one_lt₀ hu
    simp only [hJ', hJ₂, dif_pos hi0]
    have h := norm_thetaPairing_le μ (Ξ := Ξ₂) (φ₁ := φ₁) (φ₂ := φ₂) ⟨u⁻¹, hi0⟩
      (b := D * (u⁻¹) ^ a) fun x y => by
        have := hb ⟨u⁻¹, hi0⟩ x y
        rw [if_pos hi1] at this
        exact this
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hu0 _)]
    calc _ ≤ V * (D * (u⁻¹) ^ a) := h
      _ = V * D * u ^ (-a) := by rw [Real.inv_rpow hu0.le, Real.rpow_neg hu0.le]; ring
  obtain ⟨Λw, Λw', hΛ, hΛ', hΛeq, hΛ'eq, hfe⟩ :=
    exists_entire_of_symm (κ := (n : ℝ)) hJ₁c hJ'c hsym hdec₁ hdec'

  obtain ⟨c, -, hK⟩ := exists_integral_eq_mellin_thetaPairing μ hn0 ν
  obtain ⟨C₁', M₁', D₀, hb₁₀⟩ := exists_bound_GL hn0 hΦ h₁ h₂ 0
  obtain ⟨C₂', M₂', D₀', hb₂₀⟩ := exists_bound_GL_inv hn0 hΦ h₁ h₂ 0
  set w₀ : ℂ := ((n : ℂ) - 1) / 2 with hw₀
  refine ⟨max (max M₁' 0) (max M₂' 0) - ((n : ℝ) - 1) / 2,
    fun s => (c : ℂ) * Λw (s + w₀), fun s => (c : ℂ) * Λw' (s + w₀),
    (hΛ.comp (differentiable_id.add_const _)).const_mul _,
    (hΛ'.comp (differentiable_id.add_const _)).const_mul _, ?_, ?_, ?_⟩
  ·
    intro s hs
    set σ : ℝ := (s + w₀).re with hσ
    have hσre : σ = s.re + ((n : ℝ) - 1) / 2 := by
      rw [hσ, Complex.add_re, hw₀]
      simp
    have hσM : max M₁' 0 < σ := by
      have := le_max_left (max M₁' 0) (max M₂' 0)
      linarith
    obtain ⟨C, M, D, hb⟩ := exists_bound_GL hn0 hΦ h₁ h₂ (σ + 1)
    set B : ℝ → ℝ := fun t => if t < 1 then C₁' * t ^ (-max M₁' 0) else D * t ^ (-(σ + 1))
      with hBdef
    have hbB : ∀ (t : {r : ℝ // 0 < r}) (x y : normOneGL K n),
        Summable (fun γ : GL (Fin n) K => ‖Ξ₁ (centralSection K n t *
          (x : AdelicGLn.AdelicGL K n)⁻¹ * AdelicGLn.diagonal K n γ *
            (y : AdelicGLn.AdelicGL K n))‖) ∧
        ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ *
          ∑' γ : GL (Fin n) K, ‖Ξ₁ (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
            AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n))‖ ≤ B t := by
      intro t x y
      refine ⟨(hb t x y).1, ?_⟩
      by_cases ht : (t : ℝ) < 1
      · have := (hb₁₀ t x y).2
        rw [if_pos ht] at this
        simp only [hBdef, if_pos ht]
        exact this
      · have := (hb t x y).2
        rw [if_neg ht] at this
        simp only [hBdef, if_neg ht]
        exact this
    have hint : IntegrableOn (fun t : ℝ => t ^ ((s + w₀).re - 1) * B t) (Ioi 0) :=
      integrableOn_rpow_mul_ite (by linarith) (by linarith)
    obtain ⟨hI, hEq⟩ := hK φ₁ φ₂ Ξ₁ (s + w₀) B h₁c h₂c hΞ₁c h₁.1.isLeftInvariant hA
      (fun t x y hx hy => hbB t ⟨x, hx⟩ ⟨y, hy⟩) hint
    refine ⟨hI, ?_⟩
    have hconv : MellinConvergent J₁ (s + w₀) := by
      refine mellinConvergent_of_bound hJ₁c (V := V) (fun t ht => ?_) hint
      simp only [hJ₁, dif_pos ht]
      exact norm_thetaPairing_le μ ⟨t, ht⟩ fun x y => hbB ⟨t, ht⟩ x y
    show ∫ g, Ξ₁ g * matrixCoeff μ φ₁ φ₂ g * detPow g (s + w₀) ∂ν = (c : ℂ) * Λw (s + w₀)
    rw [hEq]
    show (c : ℂ) * mellin J₁ (s + w₀) = (c : ℂ) * Λw (s + w₀)
    rw [hΛeq _ hconv]
  ·
    intro s hs
    set σ : ℝ := (s + w₀).re with hσ
    have hσre : σ = s.re + ((n : ℝ) - 1) / 2 := by
      rw [hσ, Complex.add_re, hw₀]
      simp
    have hσM : max M₂' 0 < σ := by
      have := le_max_right (max M₁' 0) (max M₂' 0)
      linarith
    obtain ⟨C, M, D, hb⟩ := exists_bound_GL_inv hn0 hΦ h₁ h₂ (σ + 1)
    set B : ℝ → ℝ := fun t => if t < 1 then D * t ^ (σ + 1) else C₂' * t ^ max M₂' 0
      with hBdef
    have hbB : ∀ (t : {r : ℝ // 0 < r}) (x y : normOneGL K n),
        Summable (fun γ : GL (Fin n) K => ‖Ξ₂ (centralSection K n t *
          (x : AdelicGLn.AdelicGL K n)⁻¹ * AdelicGLn.diagonal K n γ *
            (y : AdelicGLn.AdelicGL K n))‖) ∧
        ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ *
          ∑' γ : GL (Fin n) K, ‖Ξ₂ (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
            AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n))‖ ≤ B t := by
      intro t x y
      refine ⟨(hb t x y).1, ?_⟩
      by_cases ht : (t : ℝ) < 1
      · have := (hb t x y).2
        rw [if_pos ht] at this
        simp only [hBdef, if_pos ht]
        exact this
      · have := (hb₂₀ t x y).2
        rw [if_neg ht] at this
        simp only [hBdef, if_neg ht]
        exact this
    have hint : IntegrableOn (fun t : ℝ => t ^ ((-(s + w₀)).re - 1) * B t) (Ioi 0) := by
      rw [Complex.neg_re]
      exact integrableOn_rpow_mul_ite (by linarith) (by linarith)
    obtain ⟨hI, hEq⟩ := hK φ₁ φ₂ Ξ₂ (-(s + w₀)) B h₁c h₂c hΞ₂c h₁.1.isLeftInvariant hA
      (fun t x y hx hy => hbB t ⟨x, hx⟩ ⟨y, hy⟩) hint
    have := isInvInvariant_haar ν hn0
    have hfun : zetaIntegrand (adelicMatrixFourier K Φ) (fun g => matrixCoeff μ φ₁ φ₂ g⁻¹) s =
        fun g => (fun h => Ξ₂ h * matrixCoeff μ φ₁ φ₂ h * detPow h (-(s + w₀))) g⁻¹ := by
      funext g
      simp only [zetaIntegrand, hΞ₂, inv_inv, detPow_inv, neg_neg, ← hw₀]
    refine ⟨?_, ?_⟩
    · rw [hfun]
      exact hI.comp_inv
    · have hconv2 : MellinConvergent J₂ (-(s + w₀)) := by
        refine mellinConvergent_of_bound hJ₂c (V := V) (fun t ht => ?_) hint
        simp only [hJ₂, dif_pos ht]
        exact norm_thetaPairing_le μ ⟨t, ht⟩ fun x y => hbB ⟨t, ht⟩ x y
      have hconv : MellinConvergent J' (s + w₀) := by
        have h := (MellinConvergent.comp_rpow (f := J₂) (s := s + w₀) (a := -1)
          (by norm_num)).2 (by
            rw [show (s + w₀) / ((-1 : ℝ) : ℂ) = -(s + w₀) by push_cast; ring]
            exact hconv2)
        unfold MellinConvergent at h ⊢
        refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
        simp only [hJ', Real.rpow_neg_one]
      show ∫ g, zetaIntegrand (adelicMatrixFourier K Φ) (fun g => matrixCoeff μ φ₁ φ₂ g⁻¹) s g ∂ν =
        (c : ℂ) * Λw' (s + w₀)
      rw [hfun, integral_comp_inv ν hn0 (fun h => Ξ₂ h * matrixCoeff μ φ₁ φ₂ h * detPow h (-(s + w₀))), hEq]
      show (c : ℂ) * mellin J₂ (-(s + w₀)) = (c : ℂ) * Λw' (s + w₀)
      rw [hΛ'eq _ hconv, hJ', mellin_comp_inv]
  · intro s
    simp only
    rw [hfe]
    congr 2
    rw [hw₀]
    push_cast
    ring

end GJGlobal

end

end GroundTheory.Automorphic
