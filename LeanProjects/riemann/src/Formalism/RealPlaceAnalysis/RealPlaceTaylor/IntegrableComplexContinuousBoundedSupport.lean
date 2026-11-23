import Formalism.RealPlaceAnalysis.SmoothVectorGrowthBound
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.MemUnitaryGroupIffMulConjTranspose
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexificationHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexifiedDerivativeCommutator
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CasComm
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SmoothOnGroupSum

open MeasureTheory Matrix Filter Topology
open scoped ContDiff ENNReal

set_option linter.unusedSimpArgs false

noncomputable section

namespace Formalism.REAL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section F4BA
variable {n : ℕ} {ε : Fin n → Bool}

lemma curve_mem_indefinite_unitary {g X : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hX : inG ε X) (t : ℝ) :
    inUJ ε (g * NormedSpace.exp ((t : ℂ) • X)) :=
  indefinite_unitary_mul_mem ε hg (exp_indefinite_unitary_holds n ε X hX t)

lemma mul_exp_zero_smul_eq (g X : Matrix (Fin n) (Fin n) ℂ) :
    g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by
  simp [NormedSpace.exp_zero]

lemma hasDerivAt_smooth_curve {f : Matrix (Fin n) (Fin n) ℂ → ℂ} {g X : Matrix (Fin n) (Fin n) ℂ}
    (hf : SmoothOnG ε f) (hX : inG ε X) (hg : inUJ ε g) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (Rd X f g) 0 := by
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  have hγ := hasDerivAt_mul_exp_smul_zero g X
  have hFd : DifferentiableAt ℝ F g :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
  have hcomp : HasDerivAt (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X)))
      (fderiv ℝ F g (g * X)) 0 :=
    hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ (mul_exp_zero_smul_eq g X).symm
  have hev : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0]
      (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) := by
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
      hγ.continuousAt.preimage_mem_nhds (by rw [mul_exp_zero_smul_eq]; exact hU.mem_nhds hgU)
    filter_upwards [hmem] with t ht
    exact hfF _ ht (curve_mem_indefinite_unitary hg hX t)
  rw [right_derivative_extends n ε f F U g X hU hgU hg hF hfF hX]
  exact hcomp.congr_of_eventuallyEq hev

lemma smooth_on_group_congr {f h : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f)
    (e : ∀ g, inUJ ε g → f g = h g) : SmoothOnG ε h := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  exact ⟨U, F, hU, hgU, hF, fun g hg hgJ => (e g hgJ).symm.trans (hfF g hg hgJ)⟩

lemma smooth_on_group_add {f h : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f) (hh : SmoothOnG ε h) :
    SmoothOnG ε (fun x => f x + h x) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  obtain ⟨U', H, hU', hgU', hH, hhH⟩ := hh g₀ hg₀
  exact ⟨U ∩ U', fun x => F x + H x, hU.inter hU', ⟨hgU, hgU'⟩,
    (hF.mono Set.inter_subset_left).add (hH.mono Set.inter_subset_right),
    fun g hg hgJ => by simp only; rw [hfF g hg.1 hgJ, hhH g hg.2 hgJ]⟩

lemma smooth_on_group_mul {f h : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f) (hh : SmoothOnG ε h) :
    SmoothOnG ε (fun x => f x * h x) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  obtain ⟨U', H, hU', hgU', hH, hhH⟩ := hh g₀ hg₀
  exact ⟨U ∩ U', fun x => F x * H x, hU.inter hU', ⟨hgU, hgU'⟩,
    (hF.mono Set.inter_subset_left).mul (hH.mono Set.inter_subset_right),
    fun g hg hgJ => by simp only; rw [hfF g hg.1 hgJ, hhH g hg.2 hgJ]⟩

lemma smooth_on_group_const_fun (c : ℂ) : SmoothOnG ε (fun _ : Matrix (Fin n) (Fin n) ℂ => c) :=
  fun _ _ => ⟨Set.univ, fun _ => c, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

lemma smooth_on_group_const_mul (c : ℂ) {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f) :
    SmoothOnG ε (fun x => c * f x) := smooth_on_group_mul (smooth_on_group_const_fun c) hf

lemma smooth_on_group_conj {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f) :
    SmoothOnG ε (fun x => starRingEnd ℂ (f x)) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U, fun x => starRingEnd ℂ (F x), hU, hgU, ?_, fun g hg hgJ => by
    have := hfF g hg hgJ; simp only at this ⊢; rw [this]⟩
  have := (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn hF
  exact this

lemma smooth_real_comp {h : Matrix (Fin n) (Fin n) ℂ → ℝ} (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hh : SmoothOnG ε (fun x => ((h x : ℝ) : ℂ))) :
    SmoothOnG ε (fun x => ((ψ (h x) : ℝ) : ℂ)) := by
  intro g₀ hg₀
  obtain ⟨U, H, hU, hgU, hH, hhH⟩ := hh g₀ hg₀
  refine ⟨U, fun x => ((ψ (H x).re : ℝ) : ℂ), hU, hgU, ?_, fun g hg hgJ => by
    have := hhH g hg hgJ; simp only at this ⊢; rw [← this, Complex.ofReal_re]⟩
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn
    ((hψ.comp Complex.reCLM.contDiff).comp_contDiffOn hH)

lemma smooth_right_derivative_alt {f : Matrix (Fin n) (Fin n) ℂ → ℂ} {X : Matrix (Fin n) (Fin n) ℂ}
    (hf : SmoothOnG ε f) (hX : inG ε X) : SmoothOnG ε (Rd X f) :=
  rdSmooth_of right_derivative_extends n ε f X hf hX

lemma smooth_complexified_derivative {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (Z : Matrix (Fin n) (Fin n) ℂ)
    (hf : SmoothOnG ε f) : SmoothOnG ε (Ec ε Z f) := by
  obtain ⟨h1, h2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε Z
  exact smooth_on_group_add (smooth_right_derivative_alt hf h1) (smooth_on_group_const_mul Complex.I (smooth_right_derivative_alt hf h2))

lemma smooth_lie_derivative {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (a b : Fin n) (hf : SmoothOnG ε f) :
    SmoothOnG ε (Eab ε a b f) := smooth_complexified_derivative _ hf

lemma smooth_iterated_lie_derivative {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f) :
    ∀ w : List (Fin n × Fin n), SmoothOnG ε (Eword ε w f)
  | [] => hf
  | p :: w => smooth_lie_derivative p.1 p.2 (smooth_iterated_lie_derivative hf w)

lemma right_derivative_congr {f h : Matrix (Fin n) (Fin n) ℂ → ℂ} {g X : Matrix (Fin n) (Fin n) ℂ}
    (e : ∀ x, inUJ ε x → f x = h x) (hX : inG ε X) (hg : inUJ ε g) : Rd X f g = Rd X h g := by
  unfold Rd
  congr 1
  funext t
  exact e _ (curve_mem_indefinite_unitary hg hX t)

lemma right_derivative_mul {f h : Matrix (Fin n) (Fin n) ℂ → ℂ} {g X : Matrix (Fin n) (Fin n) ℂ}
    (hf : SmoothOnG ε f) (hh : SmoothOnG ε h) (hX : inG ε X) (hg : inUJ ε g) :
    Rd X (fun x => f x * h x) g = Rd X f g * h g + f g * Rd X h g := by
  have H := (hasDerivAt_smooth_curve hf hX hg).mul (hasDerivAt_smooth_curve hh hX hg)
  rw [mul_exp_zero_smul_eq] at H
  exact H.deriv

lemma right_derivative_conj {f : Matrix (Fin n) (Fin n) ℂ → ℂ} {g X : Matrix (Fin n) (Fin n) ℂ}
    (hf : SmoothOnG ε f) (hX : inG ε X) (hg : inUJ ε g) :
    Rd X (fun x => starRingEnd ℂ (f x)) g = starRingEnd ℂ (Rd X f g) := by
  have H := (hasDerivAt_smooth_curve hf hX hg).star
  exact H.deriv

lemma right_derivative_real_comp {h : Matrix (Fin n) (Fin n) ℂ → ℝ} (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hh : SmoothOnG ε (fun x => ((h x : ℝ) : ℂ))) {g X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) (hg : inUJ ε g) :
    Rd X (fun x => ((ψ (h x) : ℝ) : ℂ)) g =
      ((deriv ψ (h g) * (Rd X (fun x => ((h x : ℝ) : ℂ)) g).re : ℝ) : ℂ) := by
  have D := hasDerivAt_smooth_curve hh hX hg
  have D2 : HasDerivAt (fun t : ℝ => h (g * NormedSpace.exp ((t : ℂ) • X)))
      (Rd X (fun x => ((h x : ℝ) : ℂ)) g).re 0 := by
    have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) D
    have e : (⇑Complex.reCLM ∘ fun t : ℝ => ((h (g * NormedSpace.exp ((t : ℂ) • X)) : ℝ) : ℂ)) =
        fun t : ℝ => h (g * NormedSpace.exp ((t : ℂ) • X)) := by
      funext t; simp
    rw [e, Complex.reCLM_apply] at this
    exact this
  have hd : DifferentiableAt ℝ ψ (h g) := hψ.differentiable (by simp) _
  have D3 := hd.hasDerivAt.comp_of_eq (0 : ℝ) D2 (by rw [mul_exp_zero_smul_eq])
  exact D3.ofReal_comp.deriv

lemma right_derivative_const_zero {g X : Matrix (Fin n) (Fin n) ℂ} :
    Rd X (fun _ : Matrix (Fin n) (Fin n) ℂ => (0 : ℂ)) g = 0 := by
  simp [Rd]

end F4BA

section F4BB
variable {n : ℕ} {ε : Fin n → Bool}

lemma real_part_single_mem (ε : Fin n → Bool) (a b : Fin n) : inG ε (cpart1 ε (Matrix.single a b 1)) :=
  (complex_parts_mem_lie_algebra_holds n ε _).1

lemma imaginary_part_single_mem (ε : Fin n → Bool) (a b : Fin n) : inG ε (cpart2 ε (Matrix.single a b 1)) :=
  (complex_parts_mem_lie_algebra_holds n ε _).2.1

lemma lie_derivative_def (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    Eab ε a b f g = Rd (cpart1 ε (Matrix.single a b 1)) f g +
      Complex.I * Rd (cpart2 ε (Matrix.single a b 1)) f g := rfl

lemma lie_derivative_congr {f h : Matrix (Fin n) (Fin n) ℂ → ℂ} (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ}
    (e : ∀ x, inUJ ε x → f x = h x) (hg : inUJ ε g) : Eab ε a b f g = Eab ε a b h g := by
  rw [lie_derivative_def, lie_derivative_def, right_derivative_congr e (real_part_single_mem ε a b) hg, right_derivative_congr e (imaginary_part_single_mem ε a b) hg]

lemma lie_derivative_mul {f h : Matrix (Fin n) (Fin n) ℂ → ℂ} (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ}
    (hf : SmoothOnG ε f) (hh : SmoothOnG ε h) (hg : inUJ ε g) :
    Eab ε a b (fun x => f x * h x) g = Eab ε a b f g * h g + f g * Eab ε a b h g := by
  rw [lie_derivative_def, lie_derivative_def, lie_derivative_def, right_derivative_mul hf hh (real_part_single_mem ε a b) hg,
    right_derivative_mul hf hh (imaginary_part_single_mem ε a b) hg]
  ring

lemma lie_derivative_add_smul {f h : Matrix (Fin n) (Fin n) ℂ → ℂ} (a b : Fin n) (c : ℂ)
    {g : Matrix (Fin n) (Fin n) ℂ} (hf : SmoothOnG ε f) (hh : SmoothOnG ε h) (hg : inUJ ε g) :
    Eab ε a b (fun x => f x + c * h x) g = Eab ε a b f g + c * Eab ε a b h g := by
  rw [lie_derivative_def, lie_derivative_def, lie_derivative_def,
    (right_derivative_linear n ε f h _ _ 0 c g hf hh (real_part_single_mem ε a b) (real_part_single_mem ε a b) hg).2.2,
    (right_derivative_linear n ε f h _ _ 0 c g hf hh (imaginary_part_single_mem ε a b) (imaginary_part_single_mem ε a b) hg).2.2]
  ring

lemma lie_derivative_const_zero (a b : Fin n) (g : Matrix (Fin n) (Fin n) ℂ) :
    Eab ε a b (fun _ => (0 : ℂ)) g = 0 := by
  rw [lie_derivative_def, right_derivative_const_zero, right_derivative_const_zero]; ring

lemma signature_conj_single (ε : Fin n → Bool) (a b : Fin n) :
    Jm ε * (Matrix.single a b (1 : ℂ))ᴴ * Jm ε = ((sgn ε a b : ℝ) : ℂ) • Matrix.single b a 1 := by
  rw [Matrix.conjTranspose_single, star_one]
  ext i j
  simp only [Jm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, Matrix.single_apply,
    smul_eq_mul, sgn]
  by_cases hi : b = i <;> by_cases hj : a = j
  · subst hi; subst hj
    by_cases ha : ε a = true <;> by_cases hb : ε b = true <;> simp [ha, hb]
  all_goals simp [hi, hj]

lemma signature_sign_mul_self (ε : Fin n → Bool) (a b : Fin n) :
    ((sgn ε a b : ℝ) : ℂ) * ((sgn ε a b : ℝ) : ℂ) = 1 := by
  unfold sgn; split_ifs <;> simp

lemma signature_sign_symm (ε : Fin n → Bool) (a b : Fin n) : sgn ε b a = sgn ε a b := by
  unfold sgn
  by_cases h : ε a = ε b
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

lemma real_part_single_swap (ε : Fin n → Bool) (a b : Fin n) :
    cpart1 ε (Matrix.single b a 1) = ((-(sgn ε a b) : ℝ) : ℂ) • cpart1 ε (Matrix.single a b 1) := by
  have e1 := signature_conj_single ε a b
  have e2 := signature_conj_single ε b a
  rw [signature_sign_symm] at e2
  unfold cpart1
  rw [e1, e2]
  unfold sgn
  split_ifs
  · simp only [Complex.ofReal_one, Complex.ofReal_neg, one_smul]; module
  · simp only [Complex.ofReal_one, Complex.ofReal_neg, neg_neg, one_smul, neg_smul]; module

lemma imaginary_part_single_swap (ε : Fin n → Bool) (a b : Fin n) :
    cpart2 ε (Matrix.single b a 1) = ((sgn ε a b : ℝ) : ℂ) • cpart2 ε (Matrix.single a b 1) := by
  have e1 := signature_conj_single ε a b
  have e2 := signature_conj_single ε b a
  rw [signature_sign_symm] at e2
  unfold cpart2
  rw [e1, e2]
  unfold sgn
  split_ifs
  · simp only [Complex.ofReal_one, one_smul]; module
  · simp only [Complex.ofReal_one, Complex.ofReal_neg, one_smul, neg_smul]; module

lemma lie_derivative_swap {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ}
    (hf : SmoothOnG ε f) (hg : inUJ ε g) :
    Eab ε b a f g = -((sgn ε a b : ℝ) : ℂ) * Rd (cpart1 ε (Matrix.single a b 1)) f g +
      Complex.I * (((sgn ε a b : ℝ) : ℂ) * Rd (cpart2 ε (Matrix.single a b 1)) f g) := by
  rw [lie_derivative_def, real_part_single_swap, imaginary_part_single_swap,
    (right_derivative_linear n ε f f _ _ (-(sgn ε a b)) 0 g hf hf (real_part_single_mem ε a b) (real_part_single_mem ε a b) hg).2.1,
    (right_derivative_linear n ε f f _ _ (sgn ε a b) 0 g hf hf (imaginary_part_single_mem ε a b) (imaginary_part_single_mem ε a b) hg).2.1]
  push_cast; ring

lemma lie_derivative_conj {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ}
    (hf : SmoothOnG ε f) (hg : inUJ ε g) :
    Eab ε a b (fun x => starRingEnd ℂ (f x)) g =
      -((sgn ε a b : ℝ) : ℂ) * starRingEnd ℂ (Eab ε b a f g) := by
  rw [lie_derivative_swap a b hf hg, lie_derivative_def, right_derivative_conj hf (real_part_single_mem ε a b) hg,
    right_derivative_conj hf (imaginary_part_single_mem ε a b) hg]
  have hs := signature_sign_mul_self ε a b
  simp only [map_add, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
  linear_combination (starRingEnd ℂ (Rd (cpart1 ε (Matrix.single a b 1)) f g) +
    Complex.I * starRingEnd ℂ (Rd (cpart2 ε (Matrix.single a b 1)) f g)) * (-hs)

lemma lie_derivative_real_comp_le {h : Matrix (Fin n) (Fin n) ℂ → ℝ} (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hh : SmoothOnG ε (fun x => ((h x : ℝ) : ℂ))) (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : inUJ ε g) :
    ‖Eab ε a b (fun x => ((ψ (h x) : ℝ) : ℂ)) g‖ ≤ |deriv ψ (h g)| *
      (‖Rd (cpart1 ε (Matrix.single a b 1)) (fun x => ((h x : ℝ) : ℂ)) g‖ +
        ‖Rd (cpart2 ε (Matrix.single a b 1)) (fun x => ((h x : ℝ) : ℂ)) g‖) := by
  rw [lie_derivative_def, right_derivative_real_comp ψ hψ hh (real_part_single_mem ε a b) hg, right_derivative_real_comp ψ hψ hh (imaginary_part_single_mem ε a b) hg]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_mul, abs_mul, mul_add]
  gcongr
  · exact Complex.abs_re_le_norm _
  · exact Complex.abs_re_le_norm _

def lieDerivativeLogFrobeniusBound (ε : Fin n → Bool) (a b : Fin n) : ℝ :=
  2 * Real.sqrt (hs (cpart1 ε (Matrix.single a b (1 : ℂ)))) +
    2 * Real.sqrt (hs (cpart2 ε (Matrix.single a b (1 : ℂ))))

lemma lie_derivative_bound_nonneg (ε : Fin n → Bool) (a b : Fin n) : 0 ≤ lieDerivativeLogFrobeniusBound ε a b := by
  unfold lieDerivativeLogFrobeniusBound; positivity

lemma lie_derivative_log_frobenius_comp_le (hl : HhLip) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (a b : Fin n)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    ‖Eab ε a b (fun x => ((ψ (hh x) : ℝ) : ℂ)) g‖ ≤ |deriv ψ (hh g)| * lieDerivativeLogFrobeniusBound ε a b := by
  refine (lie_derivative_real_comp_le ψ hψ (hl n ε).1 a b hg).trans ?_
  gcongr
  unfold lieDerivativeLogFrobeniusBound
  exact add_le_add ((hl n ε).2 _ g (real_part_single_mem ε a b) hg) ((hl n ε).2 _ g (imaginary_part_single_mem ε a b) hg)

def VanishesOutsideBall (ε : Fin n → Bool) (R : ℝ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  ∀ g, inUJ ε g → R < hs g → f g = 0

lemma vanishing_outside_right_derivative {R : ℝ} {f : Matrix (Fin n) (Fin n) ℂ → ℂ} {X : Matrix (Fin n) (Fin n) ℂ}
    (hf : VanishesOutsideBall ε R f) (hX : inG ε X) : VanishesOutsideBall ε R (Rd X f) := by
  intro g hg hR
  unfold Rd
  have hc : ContinuousAt (fun t : ℝ => hs (g * NormedSpace.exp ((t : ℂ) • X))) 0 :=
    continuous_hs_real_place_taylor.continuousAt.comp (hasDerivAt_mul_exp_smul_zero g X).continuousAt
  have hev : ∀ᶠ t : ℝ in 𝓝 0, R < hs (g * NormedSpace.exp ((t : ℂ) • X)) :=
    hc.eventually (lt_mem_nhds (by
      show R < hs (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)); rw [mul_exp_zero_smul_eq]; exact hR))
  have hz : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
    filter_upwards [hev] with t ht
    exact hf _ (curve_mem_indefinite_unitary hg hX t) ht
  rw [hz.deriv_eq]
  simp

lemma vanishing_outside_lie_derivative {R : ℝ} {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (a b : Fin n) (hf : VanishesOutsideBall ε R f) :
    VanishesOutsideBall ε R (Eab ε a b f) := by
  intro g hg hR
  rw [lie_derivative_def, vanishing_outside_right_derivative hf (real_part_single_mem ε a b) g hg hR, vanishing_outside_right_derivative hf (imaginary_part_single_mem ε a b) g hg hR]
  ring

lemma vanishing_outside_mul_left {R : ℝ} {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (h : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hf : VanishesOutsideBall ε R f) : VanishesOutsideBall ε R (fun x => f x * h x) := by
  intro g hg hR; simp [hf g hg hR]

lemma continuous_smooth_on_group_eval {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f) :
    Continuous (fun g : UJ ε => f (toM g)) := by
  rw [continuous_iff_continuousAt]
  intro g
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf (toM g) g.2
  have hFc : ContinuousAt F (toM g) := (hF.continuousOn).continuousAt (hU.mem_nhds hgU)
  have h1 : ContinuousAt (fun g : UJ ε => F (toM g)) g := hFc.comp (continuous_coeMatrix ε).continuousAt
  refine h1.congr ?_
  have hpre : ∀ᶠ g' : UJ ε in 𝓝 g, toM g' ∈ U :=
    (continuous_coeMatrix ε).continuousAt.preimage_mem_nhds (hU.mem_nhds hgU)
  filter_upwards [hpre] with g' hg'
  exact (hfF _ hg' g'.2).symm

lemma isCompact_frobenius_ball_group (ε : Fin n → Bool) (R : ℝ) : IsCompact {g : UJ ε | hsG g ≤ R} := by
  have h := (isClosedEmbeddingMatrix n ε).1.isCompact_preimage ((hermitian_small_ball n ε).1 R)
  convert h using 1
  ext g
  exact ⟨fun hg => ⟨g.2, hg⟩, fun hg => hg.2⟩

lemma integrable_complex_continuous_bounded_support {F : UJ ε → ℂ} (hF : Continuous F) (R : ℝ) (hv : ∀ g, R < hsG g → F g = 0) :
    Integrable F (muG ε) := by
  refine hF.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro' (isCompact_frobenius_ball_group ε R)
    (isClosed_le (continuous_frobenius_on_group ε) continuous_const) ?_
  intro g hg
  exact hv g (lt_of_not_ge hg)

lemma integrable_of_vanishing_outside {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f) {R : ℝ}
    (hv : VanishesOutsideBall ε R f) : Integrable (fun g : UJ ε => f (toM g)) (muG ε) :=
  integrable_complex_continuous_bounded_support (continuous_smooth_on_group_eval hf) R (fun g hg => hv _ g.2 hg)

lemma integral_lie_derivative_eq_zero (hz : IntRdZero) {φ : Matrix (Fin n) (Fin n) ℂ → ℂ} (hφ : SmoothOnG ε φ) {R : ℝ}
    (hv : VanishesOutsideBall ε R φ) (a b : Fin n) :
    ∫ g : UJ ε, Eab ε a b φ (toM g) ∂(muG ε) = 0 := by
  have i1 := integrable_of_vanishing_outside (smooth_right_derivative_alt hφ (real_part_single_mem ε a b)) (vanishing_outside_right_derivative hv (real_part_single_mem ε a b))
  have i2 := integrable_of_vanishing_outside (smooth_right_derivative_alt hφ (imaginary_part_single_mem ε a b)) (vanishing_outside_right_derivative hv (imaginary_part_single_mem ε a b))
  simp only [lie_derivative_def]
  rw [integral_add i1 (i2.const_mul Complex.I), integral_const_mul,
    hz n ε φ _ R hφ (real_part_single_mem ε a b) hv, hz n ε φ _ R hφ (imaginary_part_single_mem ε a b) hv]
  ring

end F4BB

def cutoffProfile (t : ℝ) : ℝ := Real.smoothTransition (2 - t)

lemma contDiff_cutoff_profile : ContDiff ℝ ∞ cutoffProfile :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_const.sub contDiff_id)

lemma cutoff_profile_eq_one (t : ℝ) : 0 ≤ cutoffProfile t := Real.smoothTransition.nonneg _
lemma cutoff_profile_le_one (t : ℝ) : cutoffProfile t ≤ 1 := Real.smoothTransition.le_one _
lemma cutoff_profile_eq_one_near {t : ℝ} (h : t ≤ 1) : cutoffProfile t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)
lemma cutoff_profile_eq_zero {t : ℝ} (h : 2 ≤ t) : cutoffProfile t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)
lemma antitone_cutoff_profile : Antitone cutoffProfile := fun x y h =>
  Real.smoothTransition.monotone (by linarith)

lemma exists_cutoff_deriv_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ t, |deriv cutoffProfile t| ≤ B := by
  have hc : Continuous (deriv cutoffProfile) := contDiff_cutoff_profile.continuous_deriv (by simp)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  by_cases h1 : t < 1
  · have : deriv cutoffProfile t = 0 := by
      have hev : cutoffProfile =ᶠ[𝓝 t] fun _ => 1 := by
        filter_upwards [Iio_mem_nhds h1] with s hs
        exact cutoff_profile_eq_one_near (le_of_lt hs)
      rw [hev.deriv_eq]; simp
    rw [this]; simp
  by_cases h2 : 2 < t
  · have : deriv cutoffProfile t = 0 := by
      have hev : cutoffProfile =ᶠ[𝓝 t] fun _ => 0 := by
        filter_upwards [Ioi_mem_nhds h2] with s hs
        exact cutoff_profile_eq_zero (le_of_lt hs)
      rw [hev.deriv_eq]; simp
    rw [this]; simp
  have := hC t ⟨le_of_not_gt h1, le_of_not_gt h2⟩
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

def cutoffDerivBound : ℝ := Classical.choose exists_cutoff_deriv_bound
lemma cutoffDerivBound_nonneg : 0 ≤ cutoffDerivBound := (Classical.choose_spec exists_cutoff_deriv_bound).1
lemma abs_deriv_cutoff_profile_le (t : ℝ) : |deriv cutoffProfile t| ≤ cutoffDerivBound := (Classical.choose_spec exists_cutoff_deriv_bound).2 t

def radialCutoff (R t : ℝ) : ℝ := cutoffProfile (t / R)

lemma contDiff_radialCutoff (R : ℝ) : ContDiff ℝ ∞ (radialCutoff R) :=
  contDiff_cutoff_profile.comp (contDiff_id.div_const R)

lemma hasDerivAt_cutoff_alt (R t : ℝ) :
    HasDerivAt (radialCutoff R) (deriv cutoffProfile (t / R) * (1 / R)) t := by
  have h1 : HasDerivAt (fun s : ℝ => s / R) (1 / R) t := (hasDerivAt_id t).div_const R
  have h2 : HasDerivAt cutoffProfile (deriv cutoffProfile (t / R)) (t / R) :=
    (contDiff_cutoff_profile.differentiable (by simp) _).hasDerivAt
  exact h2.comp t h1

lemma abs_deriv_cutoff_le {R : ℝ} (hR : 0 < R) (t : ℝ) : |deriv (radialCutoff R) t| ≤ cutoffDerivBound / R := by
  rw [(hasDerivAt_cutoff_alt R t).deriv, abs_mul, abs_of_pos (by positivity : 0 < 1 / R)]
  have := abs_deriv_cutoff_profile_le (t / R)
  calc |deriv cutoffProfile (t / R)| * (1 / R) ≤ cutoffDerivBound * (1 / R) := by gcongr
    _ = cutoffDerivBound / R := by ring

def weightProfileAlt (a R t : ℝ) : ℝ := radialCutoff R t ^ 2 * Real.exp (2 * a * t)

lemma contDiff_weight_profile (a R : ℝ) : ContDiff ℝ ∞ (weightProfileAlt a R) :=
  ((contDiff_radialCutoff R).pow 2).mul (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))

lemma abs_deriv_weight_profile_le {a R : ℝ} (ha : 0 ≤ a) (hR : 1 ≤ R) (t : ℝ) :
    |deriv (weightProfileAlt a R) t| ≤ radialCutoff R t * Real.exp (2 * a * t) * (2 * cutoffDerivBound + 2 * a) := by
  have hR0 : 0 < R := by linarith
  have hc := hasDerivAt_cutoff_alt R t
  have he : HasDerivAt (fun s => Real.exp (2 * a * s)) (Real.exp (2 * a * t) * (2 * a)) t := by
    have := ((hasDerivAt_id t).const_mul (2 * a)).exp
    simpa using this
  have hd : HasDerivAt (weightProfileAlt a R)
      ((2 : ℕ) * radialCutoff R t ^ (2 - 1) * (deriv cutoffProfile (t / R) * (1 / R)) * Real.exp (2 * a * t) +
        radialCutoff R t ^ 2 * (Real.exp (2 * a * t) * (2 * a))) t :=
    (hc.pow 2).mul he
  rw [hd.deriv]
  have hχ0 : 0 ≤ radialCutoff R t := cutoff_profile_eq_one _
  have hχ1 : radialCutoff R t ≤ 1 := cutoff_profile_le_one _
  have hE : 0 < Real.exp (2 * a * t) := Real.exp_pos _
  have hd' : |deriv cutoffProfile (t / R) * (1 / R)| ≤ cutoffDerivBound := by
    have h1 := abs_deriv_cutoff_le hR0 t
    rw [(hasDerivAt_cutoff_alt R t).deriv] at h1
    refine h1.trans ?_
    rw [div_le_iff₀ hR0]
    nlinarith [cutoffDerivBound_nonneg]
  have hsq : radialCutoff R t ^ 2 ≤ radialCutoff R t := by nlinarith
  push_cast
  simp only [pow_one]
  calc |2 * radialCutoff R t * (deriv cutoffProfile (t / R) * (1 / R)) * Real.exp (2 * a * t) +
        radialCutoff R t ^ 2 * (Real.exp (2 * a * t) * (2 * a))|
      ≤ |2 * radialCutoff R t * (deriv cutoffProfile (t / R) * (1 / R)) * Real.exp (2 * a * t)| +
        |radialCutoff R t ^ 2 * (Real.exp (2 * a * t) * (2 * a))| := abs_add_le _ _
    _ = 2 * radialCutoff R t * |deriv cutoffProfile (t / R) * (1 / R)| * Real.exp (2 * a * t) +
        radialCutoff R t ^ 2 * (Real.exp (2 * a * t) * (2 * a)) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hχ0, abs_of_pos hE,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ radialCutoff R t ^ 2 * (Real.exp (2 * a * t) * (2 * a)))]
        norm_num
    _ ≤ 2 * radialCutoff R t * cutoffDerivBound * Real.exp (2 * a * t) +
        radialCutoff R t * (Real.exp (2 * a * t) * (2 * a)) := by
        gcongr
    _ = radialCutoff R t * Real.exp (2 * a * t) * (2 * cutoffDerivBound + 2 * a) := by ring

lemma dim_le_frobenius {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    (n : ℝ) ≤ hs g := by
  have h1 := (indefinite_unitary_inv_closed n ε g hg).2
  have ht : Matrix.trace ((Jm ε * gᴴ * Jm ε) * g) = n := by rw [h1]; simp
  have hre : (n : ℝ) = (Matrix.trace ((Jm ε * gᴴ * Jm ε) * g)).re := by rw [ht]; simp
  have e : ∀ i j, (Jm ε * gᴴ * Jm ε) i j =
      (if ε i then 1 else -1) * star (g j i) * (if ε j then 1 else -1) := by
    intro i j
    simp [Jm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  rw [hre]
  generalize Jm ε * gᴴ * Jm ε = A at e
  unfold hs
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => ?_
  refine (Complex.re_le_norm _).trans ?_
  rw [e, norm_mul, norm_mul, norm_mul, norm_star]
  have n1 : ∀ b : Bool, ‖(if b = true then (1 : ℂ) else -1)‖ = 1 := by
    intro b; cases b <;> simp
  rw [n1, n1]
  ring_nf; rfl

lemma log_frobenius_nonneg {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    0 ≤ hh g := by
  unfold hh
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp [hs]
  · apply Real.log_nonneg
    have := dim_le_frobenius hg
    have : (1 : ℝ) ≤ n := by exact_mod_cast hpos
    linarith

lemma one_le_exponential_weight {n : ℕ} {ε : Fin n → Bool} {a : ℝ} (ha : 0 ≤ a) (g : UJ ε) :
    1 ≤ Real.exp (2 * a * hh (toM g)) := by
  rw [Real.one_le_exp_iff]
  have := log_frobenius_nonneg g.2
  positivity

lemma cutoff_vanishes_far {n : ℕ} {R : ℝ} (hR : 0 < R) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : Real.exp (2 * R) < hs x) : radialCutoff R (hh x) = 0 := by
  unfold radialCutoff
  apply cutoff_profile_eq_zero
  rw [le_div_iff₀ hR]
  unfold hh
  have hpos : 0 < hs x := (Real.exp_pos _).trans hx
  have := Real.log_lt_log (Real.exp_pos _) hx
  rw [Real.log_exp] at this
  linarith

section F4BML
variable {n : ℕ} {ε : Fin n → Bool}

lemma smooth_on_group_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (h : ∀ i ∈ s, SmoothOnG ε (f i)) : SmoothOnG ε (fun x => ∑ i ∈ s, f i x) := by
  first | exact UpperTheory.Reformulated.B.Qh27.smooth_on_group_sum .. | (apply UpperTheory.Reformulated.B.Qh27.smooth_on_group_sum <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qh27.smooth_on_group_sum <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh27.smooth_on_group_sum <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qh27.smooth_on_group_sum <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh27.smooth_on_group_sum <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qh27.smooth_on_group_sum n ε ι s f h | exact @UpperTheory.Reformulated.B.Qh27.smooth_on_group_sum n ε ι s f | exact @UpperTheory.Reformulated.B.Qh27.smooth_on_group_sum n ε ι s | exact @UpperTheory.Reformulated.B.Qh27.smooth_on_group_sum n ε ι | exact @UpperTheory.Reformulated.B.Qh27.smooth_on_group_sum n ε | exact @UpperTheory.Reformulated.B.Qh27.smooth_on_group_sum n

def signedCasimirDifference (ε : Fin n → Bool) (u : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun x => ∑ i, ∑ j, ((sgn ε i j : ℝ) : ℂ) * Eab ε j i (Eab ε i j u) x

lemma smooth_signedCasimir {u : Matrix (Fin n) (Fin n) ℂ → ℂ} (hu : SmoothOnG ε u) : SmoothOnG ε (signedCasimirDifference ε u) :=
  smooth_on_group_sum _ _ fun i _ => smooth_on_group_sum _ _ fun j _ =>
    smooth_on_group_const_mul _ (smooth_lie_derivative j i (smooth_lie_derivative i j hu))

def radialWeight (a R : ℝ) (x : Matrix (Fin n) (Fin n) ℂ) : ℂ := ((weightProfileAlt a R (hh x) : ℝ) : ℂ)

lemma smooth_weight (hl : HhLip) (a R : ℝ) : SmoothOnG ε (radialWeight (n := n) a R) :=
  smooth_real_comp _ (contDiff_weight_profile a R) (hl n ε).1

lemma weight_vanishing_outside (a : ℝ) {R : ℝ} (hR : 0 < R) :
    VanishesOutsideBall ε (Real.exp (2 * R)) (radialWeight (n := n) a R) := by
  intro g _ hg
  simp [radialWeight, weightProfileAlt, cutoff_vanishes_far hR hg]

lemma weight_profile_nonneg (a R t : ℝ) : 0 ≤ weightProfileAlt a R t := by
  unfold weightProfileAlt; positivity

lemma weight_profile_le_exp (a R t : ℝ) : weightProfileAlt a R t ≤ Real.exp (2 * a * t) := by
  unfold weightProfileAlt
  have h0 := cutoff_profile_eq_one (t / R)
  have h1 := cutoff_profile_le_one (t / R)
  have : radialCutoff R t ^ 2 ≤ 1 := by unfold radialCutoff; nlinarith
  calc radialCutoff R t ^ 2 * Real.exp (2 * a * t) ≤ 1 * Real.exp (2 * a * t) := by
        gcongr
    _ = _ := one_mul _

lemma lie_derivative_weight_le (hl : HhLip) {a R : ℝ} (ha : 0 ≤ a) (hR : 1 ≤ R) (i j : Fin n)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    ‖Eab ε i j (radialWeight a R) g‖ ≤ radialCutoff R (hh g) * Real.exp (2 * a * hh g) *
      ((2 * cutoffDerivBound + 2 * a) * lieDerivativeLogFrobeniusBound ε i j) := by
  refine (lie_derivative_log_frobenius_comp_le hl (weightProfileAlt a R) (contDiff_weight_profile a R) i j hg).trans ?_
  have := abs_deriv_weight_profile_le ha hR (hh g)
  calc |deriv (weightProfileAlt a R) (hh g)| * lieDerivativeLogFrobeniusBound ε i j ≤
        radialCutoff R (hh g) * Real.exp (2 * a * hh g) * (2 * cutoffDerivBound + 2 * a) * lieDerivativeLogFrobeniusBound ε i j := by
        gcongr; exact lie_derivative_bound_nonneg ε i j
    _ = _ := by ring

lemma measurable_exponential_weight (a : ℝ) : Measurable (fun g : UJ ε => Real.exp (2 * a * hh (toM g))) :=
  Real.measurable_exp.comp (measurable_const.mul
    (Real.measurable_log.comp (continuous_frobenius_on_group ε).measurable))

lemma aestronglyMeasurable_weighted_norm_sq (a : ℝ) {u : Matrix (Fin n) (Fin n) ℂ → ℂ} (hu : SmoothOnG ε u) :
    AEStronglyMeasurable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2)
      (muG ε) :=
  ((measurable_exponential_weight a).mul ((continuous_smooth_on_group_eval hu).norm.pow 2).measurable).aestronglyMeasurable

lemma integrable_of_ofReal {F : UJ ε → ℝ} (h : Integrable (fun g => ((F g : ℝ) : ℂ)) (muG ε)) :
    Integrable F (muG ε) := by
  have := h.re
  simpa using this

lemma amgm_mul_le (x y e : ℝ) (he : 0 ≤ e) : x * y * e ≤ x ^ 2 * e / 2 + y ^ 2 * e / 2 := by
  nlinarith [mul_nonneg he (sq_nonneg (x - y))]

lemma integral_lie_derivative_weight_identity (hl : HhLip) (hz : IntRdZero) (a : ℝ) {R : ℝ} (hR : 0 < R)
    {u : Matrix (Fin n) (Fin n) ℂ → ℂ} (hu : SmoothOnG ε u) (i j : Fin n) :
    ∫ g : UJ ε, radialWeight a R (toM g) * Eab ε i j u (toM g) * starRingEnd ℂ (Eab ε i j u (toM g))
        ∂(muG ε) =
      -∫ g : UJ ε, Eab ε i j (radialWeight a R) (toM g) * u (toM g) * starRingEnd ℂ (Eab ε i j u (toM g))
        ∂(muG ε) +
      ((sgn ε i j : ℝ) : ℂ) * ∫ g : UJ ε, radialWeight a R (toM g) * u (toM g) *
        starRingEnd ℂ (Eab ε j i (Eab ε i j u) (toM g)) ∂(muG ε) := by
  have wsm := smooth_weight (ε := ε) hl a R
  have wv := weight_vanishing_outside (ε := ε) a hR
  have hv := smooth_lie_derivative i j hu
  have hφs : SmoothOnG ε (fun x => (radialWeight a R x * u x) * starRingEnd ℂ (Eab ε i j u x)) :=
    smooth_on_group_mul (smooth_on_group_mul wsm hu) (smooth_on_group_conj hv)
  have hφv : VanishesOutsideBall ε (Real.exp (2 * R))
      (fun x => (radialWeight a R x * u x) * starRingEnd ℂ (Eab ε i j u x)) :=
    vanishing_outside_mul_left _ (vanishing_outside_mul_left _ wv)
  have h0 := integral_lie_derivative_eq_zero hz hφs hφv i j
  have key : ∀ g : UJ ε, Eab ε i j (fun x => (radialWeight a R x * u x) * starRingEnd ℂ (Eab ε i j u x))
      (toM g) = Eab ε i j (radialWeight a R) (toM g) * u (toM g) * starRingEnd ℂ (Eab ε i j u (toM g)) +
        radialWeight a R (toM g) * Eab ε i j u (toM g) * starRingEnd ℂ (Eab ε i j u (toM g)) +
        (-((sgn ε i j : ℝ) : ℂ)) * (radialWeight a R (toM g) * u (toM g) *
          starRingEnd ℂ (Eab ε j i (Eab ε i j u) (toM g))) := by
    intro g
    rw [lie_derivative_mul i j (smooth_on_group_mul wsm hu) (smooth_on_group_conj hv) g.2, lie_derivative_mul i j wsm hu g.2,
      lie_derivative_conj i j hv g.2]
    ring
  have i1 : Integrable (fun g : UJ ε => Eab ε i j (radialWeight a R) (toM g) * u (toM g) *
      starRingEnd ℂ (Eab ε i j u (toM g))) (muG ε) :=
    integrable_of_vanishing_outside (f := fun x => Eab ε i j (radialWeight a R) x * u x * starRingEnd ℂ (Eab ε i j u x))
      (smooth_on_group_mul (smooth_on_group_mul (smooth_lie_derivative i j wsm) hu) (smooth_on_group_conj hv))
      (vanishing_outside_mul_left _ (vanishing_outside_mul_left _ (vanishing_outside_lie_derivative i j wv)))
  have i2 : Integrable (fun g : UJ ε => radialWeight a R (toM g) * Eab ε i j u (toM g) *
      starRingEnd ℂ (Eab ε i j u (toM g))) (muG ε) :=
    integrable_of_vanishing_outside (f := fun x => radialWeight a R x * Eab ε i j u x * starRingEnd ℂ (Eab ε i j u x))
      (smooth_on_group_mul (smooth_on_group_mul wsm hv) (smooth_on_group_conj hv))
      (vanishing_outside_mul_left _ (vanishing_outside_mul_left _ wv))
  have i3 : Integrable (fun g : UJ ε => radialWeight a R (toM g) * u (toM g) *
      starRingEnd ℂ (Eab ε j i (Eab ε i j u) (toM g))) (muG ε) :=
    integrable_of_vanishing_outside (f := fun x => radialWeight a R x * u x * starRingEnd ℂ (Eab ε j i (Eab ε i j u) x))
      (smooth_on_group_mul (smooth_on_group_mul wsm hu) (smooth_on_group_conj (smooth_lie_derivative j i hv)))
      (vanishing_outside_mul_left _ (vanishing_outside_mul_left _ wv))
  rw [integral_congr_ae (Eventually.of_forall key)] at h0
  have e1 := integral_add (i1.add i2) (i3.const_mul (-((sgn ε i j : ℝ) : ℂ)))
  simp only [Pi.add_apply] at e1
  rw [integral_add i1 i2, integral_const_mul] at e1
  rw [e1] at h0
  linear_combination h0

end F4BML

section F4BML2
variable {n : ℕ} {ε : Fin n → Bool}

lemma weight_mul_conj_eq (a R : ℝ) (x : Matrix (Fin n) (Fin n) ℂ) (v : ℂ) :
    radialWeight a R x * v * starRingEnd ℂ v = ((weightProfileAlt a R (hh x) * ‖v‖ ^ 2 : ℝ) : ℂ) := by
  unfold radialWeight
  rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast; ring

lemma integrable_weight_derivative_product (hl : HhLip) (a : ℝ) {R : ℝ} (hR : 0 < R) {u : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hu : SmoothOnG ε u) (i j : Fin n) :
    Integrable (fun g : UJ ε => Eab ε i j (radialWeight a R) (toM g) * u (toM g) *
      starRingEnd ℂ (Eab ε i j u (toM g))) (muG ε) :=
  integrable_of_vanishing_outside (f := fun x => Eab ε i j (radialWeight a R) x * u x * starRingEnd ℂ (Eab ε i j u x))
    (smooth_on_group_mul (smooth_on_group_mul (smooth_lie_derivative i j (smooth_weight hl a R)) hu) (smooth_on_group_conj (smooth_lie_derivative i j hu)))
    (vanishing_outside_mul_left _ (vanishing_outside_mul_left _ (vanishing_outside_lie_derivative i j (weight_vanishing_outside a hR))))

lemma integrable_weight_product (hl : HhLip) (a : ℝ) {R : ℝ} (hR : 0 < R) {u h : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hu : SmoothOnG ε u) (hh' : SmoothOnG ε h) :
    Integrable (fun g : UJ ε => radialWeight a R (toM g) * u (toM g) * starRingEnd ℂ (h (toM g)))
      (muG ε) :=
  integrable_of_vanishing_outside (f := fun x => radialWeight a R x * u x * starRingEnd ℂ (h x))
    (smooth_on_group_mul (smooth_on_group_mul (smooth_weight hl a R) hu) (smooth_on_group_conj hh'))
    (vanishing_outside_mul_left _ (vanishing_outside_mul_left _ (weight_vanishing_outside a hR)))

lemma integrable_weighted_norm_sq (hl : HhLip) (a : ℝ) {R : ℝ} (hR : 0 < R) {v : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hv : SmoothOnG ε v) :
    Integrable (fun g : UJ ε => weightProfileAlt a R (hh (toM g)) * ‖v (toM g)‖ ^ 2) (muG ε) := by
  apply integrable_of_ofReal
  refine (integrable_weight_product hl a hR hv hv).congr (Eventually.of_forall fun g => ?_)
  exact weight_mul_conj_eq a R _ _

lemma sum_weighted_lie_derivative_bound (hl : HhLip) (hz : IntRdZero) {a : ℝ} (ha : 0 ≤ a) {R : ℝ} (hR : 1 ≤ R)
    {u : Matrix (Fin n) (Fin n) ℂ → ℂ} (hu : SmoothOnG ε u)
    (hu2 : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2) (muG ε))
    (hT2 : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖signedCasimirDifference ε u (toM g)‖ ^ 2)
      (muG ε)) :
    ∑ i, ∑ j, ∫ g : UJ ε, weightProfileAlt a R (hh (toM g)) * ‖Eab ε i j u (toM g)‖ ^ 2 ∂(muG ε) ≤
      ∑ i, ∑ j, ((2 * cutoffDerivBound + 2 * a) * lieDerivativeLogFrobeniusBound ε i j) ^ 2 *
          ∫ g : UJ ε, Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2 ∂(muG ε) +
        ∫ g : UJ ε, Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2 ∂(muG ε) +
        ∫ g : UJ ε, Real.exp (2 * a * hh (toM g)) * ‖signedCasimirDifference ε u (toM g)‖ ^ 2 ∂(muG ε) := by
  have hR0 : 0 < R := by linarith
  set Nu := ∫ g : UJ ε, Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2 ∂(muG ε) with hNu
  set NT := ∫ g : UJ ε, Real.exp (2 * a * hh (toM g)) * ‖signedCasimirDifference ε u (toM g)‖ ^ 2 ∂(muG ε) with hNT
  set I : Fin n → Fin n → ℝ := fun i j =>
    ∫ g : UJ ε, weightProfileAlt a R (hh (toM g)) * ‖Eab ε i j u (toM g)‖ ^ 2 ∂(muG ε) with hIdef
  set K : Fin n → Fin n → ℝ := fun i j => (2 * cutoffDerivBound + 2 * a) * lieDerivativeLogFrobeniusBound ε i j with hK
  set C1 : Fin n → Fin n → ℂ := fun i j => ∫ g : UJ ε, Eab ε i j (radialWeight a R) (toM g) * u (toM g) *
      starRingEnd ℂ (Eab ε i j u (toM g)) ∂(muG ε) with hC1
  set C4 : ℂ := ∫ g : UJ ε, radialWeight a R (toM g) * u (toM g) * starRingEnd ℂ (signedCasimirDifference ε u (toM g))
    ∂(muG ε) with hC4

  have hI : ∀ i j, ((I i j : ℝ) : ℂ) = -C1 i j + ((sgn ε i j : ℝ) : ℂ) *
      ∫ g : UJ ε, radialWeight a R (toM g) * u (toM g) * starRingEnd ℂ (Eab ε j i (Eab ε i j u) (toM g))
        ∂(muG ε) := by
    intro i j
    rw [← integral_lie_derivative_weight_identity hl hz a hR0 hu i j]
    simp only [hIdef]
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    exact (weight_mul_conj_eq a R _ _).symm

  have hsum : ∑ i, ∑ j, ((sgn ε i j : ℝ) : ℂ) *
      ∫ g : UJ ε, radialWeight a R (toM g) * u (toM g) * starRingEnd ℂ (Eab ε j i (Eab ε i j u) (toM g))
        ∂(muG ε) = C4 := by
    have pw : ∀ g : UJ ε, radialWeight a R (toM g) * u (toM g) * starRingEnd ℂ (signedCasimirDifference ε u (toM g)) =
        ∑ i, ∑ j, ((sgn ε i j : ℝ) : ℂ) * (radialWeight a R (toM g) * u (toM g) *
          starRingEnd ℂ (Eab ε j i (Eab ε i j u) (toM g))) := by
      intro g
      simp only [signedCasimirDifference, map_sum, map_mul, Complex.conj_ofReal]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hC4, integral_congr_ae (Eventually.of_forall pw), integral_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ =>
        (integrable_weight_product hl a hR0 hu (smooth_lie_derivative j i (smooth_lie_derivative i j hu))).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ =>
        (integrable_weight_product hl a hR0 hu (smooth_lie_derivative j i (smooth_lie_derivative i j hu))).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
  have hIi : ∀ i j, Integrable (fun g : UJ ε => weightProfileAlt a R (hh (toM g)) * ‖Eab ε i j u (toM g)‖ ^ 2)
      (muG ε) := fun i j => integrable_weighted_norm_sq hl a hR0 (smooth_lie_derivative i j hu)
  have hC1b : ∀ i j, ‖C1 i j‖ ≤ I i j / 2 + K i j ^ 2 * Nu / 2 := by
    intro i j
    refine (norm_integral_le_integral_norm _).trans ?_
    have hb : ∀ g : UJ ε, ‖Eab ε i j (radialWeight a R) (toM g) * u (toM g) *
        starRingEnd ℂ (Eab ε i j u (toM g))‖ ≤
        weightProfileAlt a R (hh (toM g)) * ‖Eab ε i j u (toM g)‖ ^ 2 / 2 +
          K i j ^ 2 * (Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2) / 2 := by
      intro g
      have h1 := lie_derivative_weight_le hl ha hR i j g.2
      rw [norm_mul, norm_mul, Complex.norm_conj]
      have hχ := cutoff_profile_eq_one (hh (toM g) / R)
      have hE := Real.exp_pos (2 * a * hh (toM g))
      calc ‖Eab ε i j (radialWeight a R) (toM g)‖ * ‖u (toM g)‖ * ‖Eab ε i j u (toM g)‖
          ≤ radialCutoff R (hh (toM g)) * Real.exp (2 * a * hh (toM g)) * K i j * ‖u (toM g)‖ *
              ‖Eab ε i j u (toM g)‖ := by gcongr
        _ = (radialCutoff R (hh (toM g)) * ‖Eab ε i j u (toM g)‖) * (K i j * ‖u (toM g)‖) *
              Real.exp (2 * a * hh (toM g)) := by ring
        _ ≤ (radialCutoff R (hh (toM g)) * ‖Eab ε i j u (toM g)‖) ^ 2 * Real.exp (2 * a * hh (toM g)) / 2 +
              (K i j * ‖u (toM g)‖) ^ 2 * Real.exp (2 * a * hh (toM g)) / 2 :=
            amgm_mul_le _ _ _ hE.le
        _ = _ := by unfold weightProfileAlt; ring
    have hr1 : Integrable (fun g : UJ ε =>
        weightProfileAlt a R (hh (toM g)) * ‖Eab ε i j u (toM g)‖ ^ 2 / 2) (muG ε) :=
      Integrable.div_const (f := fun g : UJ ε =>
        weightProfileAlt a R (hh (toM g)) * ‖Eab ε i j u (toM g)‖ ^ 2) (hIi i j) 2
    have hr2 : Integrable (fun g : UJ ε =>
        K i j ^ 2 * (Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2) / 2) (muG ε) :=
      Integrable.div_const (f := fun g : UJ ε =>
        K i j ^ 2 * (Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2))
        (Integrable.const_mul (f := fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2)
          hu2 _) 2
    have hr : Integrable (fun g : UJ ε =>
        weightProfileAlt a R (hh (toM g)) * ‖Eab ε i j u (toM g)‖ ^ 2 / 2 +
          K i j ^ 2 * (Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2) / 2) (muG ε) :=
      Integrable.add (f := fun g : UJ ε => weightProfileAlt a R (hh (toM g)) * ‖Eab ε i j u (toM g)‖ ^ 2 / 2)
        (g := fun g : UJ ε => K i j ^ 2 * (Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2) / 2)
        hr1 hr2
    calc ∫ g : UJ ε, ‖Eab ε i j (radialWeight a R) (toM g) * u (toM g) *
          starRingEnd ℂ (Eab ε i j u (toM g))‖ ∂(muG ε)
        ≤ ∫ g : UJ ε, (weightProfileAlt a R (hh (toM g)) * ‖Eab ε i j u (toM g)‖ ^ 2 / 2 +
          K i j ^ 2 * (Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2) / 2) ∂(muG ε) :=
          integral_mono (integrable_weight_derivative_product hl a hR0 hu i j).norm hr hb
      _ = I i j / 2 + K i j ^ 2 * Nu / 2 := by
          rw [integral_add hr1 hr2, integral_div, integral_div, integral_const_mul]
  have hC4b : ‖C4‖ ≤ Nu / 2 + NT / 2 := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have hb : ∀ g : UJ ε, ‖radialWeight a R (toM g) * u (toM g) * starRingEnd ℂ (signedCasimirDifference ε u (toM g))‖ ≤
        Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2 / 2 +
          Real.exp (2 * a * hh (toM g)) * ‖signedCasimirDifference ε u (toM g)‖ ^ 2 / 2 := by
      intro g
      rw [norm_mul, norm_mul, Complex.norm_conj]
      have hw : ‖radialWeight a R (toM g)‖ ≤ Real.exp (2 * a * hh (toM g)) := by
        unfold radialWeight
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (weight_profile_nonneg _ _ _)]
        exact weight_profile_le_exp _ _ _
      have hE := Real.exp_pos (2 * a * hh (toM g))
      calc ‖radialWeight a R (toM g)‖ * ‖u (toM g)‖ * ‖signedCasimirDifference ε u (toM g)‖
          ≤ Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ * ‖signedCasimirDifference ε u (toM g)‖ := by gcongr
        _ = ‖u (toM g)‖ * ‖signedCasimirDifference ε u (toM g)‖ * Real.exp (2 * a * hh (toM g)) := by ring
        _ ≤ ‖u (toM g)‖ ^ 2 * Real.exp (2 * a * hh (toM g)) / 2 +
            ‖signedCasimirDifference ε u (toM g)‖ ^ 2 * Real.exp (2 * a * hh (toM g)) / 2 := amgm_mul_le _ _ _ hE.le
        _ = _ := by ring
    have hr1 : Integrable (fun g : UJ ε =>
        Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2 / 2) (muG ε) :=
      Integrable.div_const (f := fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2) hu2 2
    have hr2 : Integrable (fun g : UJ ε =>
        Real.exp (2 * a * hh (toM g)) * ‖signedCasimirDifference ε u (toM g)‖ ^ 2 / 2) (muG ε) :=
      Integrable.div_const (f := fun g : UJ ε =>
        Real.exp (2 * a * hh (toM g)) * ‖signedCasimirDifference ε u (toM g)‖ ^ 2) hT2 2
    have hr : Integrable (fun g : UJ ε =>
        Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2 / 2 +
          Real.exp (2 * a * hh (toM g)) * ‖signedCasimirDifference ε u (toM g)‖ ^ 2 / 2) (muG ε) :=
      Integrable.add (f := fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2 / 2)
        (g := fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖signedCasimirDifference ε u (toM g)‖ ^ 2 / 2) hr1 hr2
    calc ∫ g : UJ ε, ‖radialWeight a R (toM g) * u (toM g) * starRingEnd ℂ (signedCasimirDifference ε u (toM g))‖ ∂(muG ε)
        ≤ ∫ g : UJ ε, (Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2 / 2 +
          Real.exp (2 * a * hh (toM g)) * ‖signedCasimirDifference ε u (toM g)‖ ^ 2 / 2) ∂(muG ε) :=
          integral_mono (integrable_weight_product hl a hR0 hu (smooth_signedCasimir hu)).norm hr hb
      _ = Nu / 2 + NT / 2 := by
          rw [integral_add hr1 hr2, integral_div, integral_div]
  have hc : ((∑ i, ∑ j, I i j : ℝ) : ℂ) = ∑ i, ∑ j, -C1 i j + C4 := by
    push_cast
    simp only [hI, Finset.sum_add_distrib, hsum]
  have hre : ∑ i, ∑ j, I i j = ∑ i, ∑ j, -(C1 i j).re + C4.re := by
    have := congrArg Complex.re hc
    simpa [Complex.re_sum] using this
  have h1 : ∑ i, ∑ j, -(C1 i j).re ≤ ∑ i, ∑ j, (I i j / 2 + K i j ^ 2 * Nu / 2) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans (hC1b i j))
  have h2 : C4.re ≤ Nu / 2 + NT / 2 := (Complex.re_le_norm _).trans hC4b
  have h3 : ∑ i, ∑ j, (I i j / 2 + K i j ^ 2 * Nu / 2) =
      (∑ i, ∑ j, I i j) / 2 + (∑ i, ∑ j, K i j ^ 2 * Nu) / 2 := by
    simp only [Finset.sum_add_distrib, Finset.sum_div]
  linarith

end F4BML2

section Integrability
variable {n : ℕ} {ε : Fin n → Bool}

lemma integrable_of_monotone_bounded {X : Type*} [MeasurableSpace X] {μ : Measure X} {F : ℕ → X → ℝ} {f : X → ℝ}
    (hF : ∀ N, Integrable (F N) μ) (hF0 : ∀ N x, 0 ≤ F N x) (hmono : ∀ x, Monotone (fun N => F N x))
    (hlim : ∀ x, ∃ N, F N x = f x) (hle : ∀ N x, F N x ≤ f x) (hf : AEStronglyMeasurable f μ)
    {B : ℝ} (hB : ∀ N, ∫ x, F N x ∂μ ≤ B) : Integrable f μ := by
  have hf0 : ∀ x, 0 ≤ f x := fun x => (hF0 0 x).trans (hle 0 x)
  refine ⟨hf, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hf0)]
  have hsup : ∀ x, ENNReal.ofReal (f x) = ⨆ N, ENNReal.ofReal (F N x) := by
    intro x; apply le_antisymm
    · obtain ⟨N, hN⟩ := hlim x
      rw [← hN]; exact le_iSup (fun N => ENNReal.ofReal (F N x)) N
    · exact iSup_le fun N => ENNReal.ofReal_le_ofReal (hle N x)
  rw [lintegral_congr hsup, lintegral_iSup' (fun N => (hF N).aemeasurable.ennreal_ofReal)
    (Eventually.of_forall fun x => fun N M h => ENNReal.ofReal_le_ofReal (hmono x h))]
  refine lt_of_le_of_lt (iSup_le fun N => ?_) (ENNReal.ofReal_lt_top (r := B))
  rw [← ofReal_integral_eq_lintegral_ofReal (hF N) (Eventually.of_forall (hF0 N))]
  exact ENNReal.ofReal_le_ofReal (hB N)

lemma monotone_cutoff_in_radius {t : ℝ} (ht : 0 ≤ t) : Monotone (fun N : ℕ => radialCutoff ((N : ℝ) + 1) t) := by
  intro N M h
  unfold radialCutoff
  apply antitone_cutoff_profile
  have h1 : (N : ℝ) + 1 ≤ (M : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right h 1
  exact div_le_div_of_nonneg_left ht (by positivity) h1

lemma cutoff_eventually_one (t : ℝ) : ∃ N : ℕ, ∀ M, N ≤ M → radialCutoff ((M : ℝ) + 1) t = 1 := by
  refine ⟨⌈t⌉₊, fun M hM => ?_⟩
  unfold radialCutoff
  apply cutoff_profile_eq_one_near
  rw [div_le_one (by positivity)]
  have := Nat.le_ceil t
  have : (⌈t⌉₊ : ℝ) ≤ M := by exact_mod_cast hM
  linarith

lemma integrable_lie_derivative_weighted (hl : HhLip) (hz : IntRdZero) {a : ℝ} (ha : 0 ≤ a)
    {u : Matrix (Fin n) (Fin n) ℂ → ℂ} (hu : SmoothOnG ε u)
    (hu2 : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2) (muG ε))
    (hT2 : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖signedCasimirDifference ε u (toM g)‖ ^ 2)
      (muG ε)) (i j : Fin n) :
    Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖Eab ε i j u (toM g)‖ ^ 2)
      (muG ε) := by
  have hv := smooth_lie_derivative i j hu
  refine integrable_of_monotone_bounded (F := fun N g => weightProfileAlt a ((N : ℝ) + 1) (hh (toM g)) * ‖Eab ε i j u (toM g)‖ ^ 2)
    (fun N => integrable_weighted_norm_sq hl a (by positivity) hv)
    (fun N g => mul_nonneg (weight_profile_nonneg _ _ _) (by positivity)) ?_ ?_ ?_ (aestronglyMeasurable_weighted_norm_sq a hv)
    (B := ∑ i, ∑ j, ((2 * cutoffDerivBound + 2 * a) * lieDerivativeLogFrobeniusBound ε i j) ^ 2 *
          ∫ g : UJ ε, Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2 ∂(muG ε) +
        ∫ g : UJ ε, Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2 ∂(muG ε) +
        ∫ g : UJ ε, Real.exp (2 * a * hh (toM g)) * ‖signedCasimirDifference ε u (toM g)‖ ^ 2 ∂(muG ε)) ?_
  · intro g N M h
    have h0 := log_frobenius_nonneg g.2
    have hm := monotone_cutoff_in_radius h0 h
    have p0 := cutoff_profile_eq_one (hh (toM g) / ((N : ℝ) + 1))
    simp only [weightProfileAlt]
    have : radialCutoff ((N : ℝ) + 1) (hh (toM g)) ^ 2 ≤ radialCutoff ((M : ℝ) + 1) (hh (toM g)) ^ 2 := by
      unfold radialCutoff at hm p0 ⊢
      exact pow_le_pow_left₀ p0 hm 2
    gcongr
  · intro g
    obtain ⟨N, hN⟩ := cutoff_eventually_one (hh (toM g))
    refine ⟨N, ?_⟩
    simp only [weightProfileAlt, hN N le_rfl]
    ring
  · intro N g
    show weightProfileAlt a ((N : ℝ) + 1) (hh (toM g)) * ‖Eab ε i j u (toM g)‖ ^ 2 ≤
      Real.exp (2 * a * hh (toM g)) * ‖Eab ε i j u (toM g)‖ ^ 2
    gcongr
    exact weight_profile_le_exp _ _ _
  · intro N
    have h2 := sum_weighted_lie_derivative_bound hl hz ha (R := (N : ℝ) + 1) (by linarith [N.cast_nonneg (α := ℝ)]) hu hu2 hT2
    refine le_trans ?_ h2
    have hnn : ∀ i' j', 0 ≤ ∫ g : UJ ε, weightProfileAlt a ((N : ℝ) + 1) (hh (toM g)) *
        ‖Eab ε i' j' u (toM g)‖ ^ 2 ∂(muG ε) := fun i' j' =>
      integral_nonneg fun g => mul_nonneg (weight_profile_nonneg _ _ _) (by positivity)
    calc ∫ g : UJ ε, weightProfileAlt a ((N : ℝ) + 1) (hh (toM g)) * ‖Eab ε i j u (toM g)‖ ^ 2 ∂(muG ε)
        ≤ ∑ j', ∫ g : UJ ε, weightProfileAlt a ((N : ℝ) + 1) (hh (toM g)) * ‖Eab ε i j' u (toM g)‖ ^ 2
            ∂(muG ε) :=
          Finset.single_le_sum (f := fun j' => ∫ g : UJ ε, weightProfileAlt a ((N : ℝ) + 1) (hh (toM g)) *
            ‖Eab ε i j' u (toM g)‖ ^ 2 ∂(muG ε)) (fun j' _ => hnn i j') (Finset.mem_univ j)
      _ ≤ _ := Finset.single_le_sum (f := fun i' => ∑ j', ∫ g : UJ ε,
            weightProfileAlt a ((N : ℝ) + 1) (hh (toM g)) * ‖Eab ε i' j' u (toM g)‖ ^ 2 ∂(muG ε))
          (fun i' _ => Finset.sum_nonneg fun j' _ => hnn i' j') (Finset.mem_univ i)

end Integrability

section F4BUL
variable {n : ℕ} {ε : Fin n → Bool}

lemma integrable_mul_conj_of_weighted {a : ℝ} (ha : 0 ≤ a) {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hf : SmoothOnG ε f) (hf' : SmoothOnG ε f')
    (h2 : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖f (toM g)‖ ^ 2) (muG ε))
    (h2' : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖f' (toM g)‖ ^ 2) (muG ε)) :
    Integrable (fun g : UJ ε => f (toM g) * starRingEnd ℂ (f' (toM g))) (muG ε) := by
  have hb : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖f (toM g)‖ ^ 2 / 2 +
      Real.exp (2 * a * hh (toM g)) * ‖f' (toM g)‖ ^ 2 / 2) (muG ε) :=
    Integrable.add (f := fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖f (toM g)‖ ^ 2 / 2)
      (g := fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖f' (toM g)‖ ^ 2 / 2)
      (Integrable.div_const (f := fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖f (toM g)‖ ^ 2)
        h2 2)
      (Integrable.div_const (f := fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖f' (toM g)‖ ^ 2)
        h2' 2)
  refine hb.mono' ((continuous_smooth_on_group_eval hf).mul ((continuous_smooth_on_group_eval hf').star)).aestronglyMeasurable
    (Eventually.of_forall fun g => ?_)
  rw [norm_mul, Complex.norm_conj]
  have he := one_le_exponential_weight ha g
  have h1 := amgm_mul_le ‖f (toM g)‖ ‖f' (toM g)‖ 1 zero_le_one
  have h3 : 0 ≤ ‖f (toM g)‖ ^ 2 := by positivity
  have h4 : 0 ≤ ‖f' (toM g)‖ ^ 2 := by positivity
  nlinarith

def radialCutoffFunction (R : ℝ) (x : Matrix (Fin n) (Fin n) ℂ) : ℂ := ((radialCutoff R (hh x) : ℝ) : ℂ)

lemma smooth_cutoff (hl : HhLip) (R : ℝ) : SmoothOnG ε (radialCutoffFunction (n := n) R) :=
  smooth_real_comp _ (contDiff_radialCutoff R) (hl n ε).1

lemma cutoff_vanishing_outside {R : ℝ} (hR : 0 < R) : VanishesOutsideBall ε (Real.exp (2 * R)) (radialCutoffFunction (n := n) R) := by
  intro g _ hg
  simp [radialCutoffFunction, cutoff_vanishes_far hR hg]

lemma measurable_cutoff_alt (R : ℝ) : Measurable (fun g : UJ ε => radialCutoffFunction (n := n) R (toM g)) :=
  Complex.measurable_ofReal.comp ((contDiff_radialCutoff R).continuous.measurable.comp
    (Real.measurable_log.comp (continuous_frobenius_on_group ε).measurable))

lemma tendsto_integral_cutoff {F : UJ ε → ℂ} (hF : Integrable F (muG ε)) :
    Tendsto (fun N : ℕ => ∫ g : UJ ε, radialCutoffFunction ((N : ℝ) + 1) (toM g) * F g ∂(muG ε)) atTop
      (𝓝 (∫ g : UJ ε, F g ∂(muG ε))) := by
  refine tendsto_integral_of_dominated_convergence (fun g => ‖F g‖) (fun N => ?_) hF.norm
    (fun N => Eventually.of_forall fun g => ?_) (Eventually.of_forall fun g => ?_)
  · exact (measurable_cutoff_alt _).aestronglyMeasurable.mul hF.aestronglyMeasurable
  · rw [norm_mul]
    have h0 := cutoff_profile_eq_one (hh (toM g) / ((N : ℝ) + 1))
    have h1 := cutoff_profile_le_one (hh (toM g) / ((N : ℝ) + 1))
    have : ‖radialCutoffFunction (n := n) ((N : ℝ) + 1) (toM g)‖ ≤ 1 := by
      unfold radialCutoffFunction radialCutoff
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
    calc ‖radialCutoffFunction ((N : ℝ) + 1) (toM g)‖ * ‖F g‖ ≤ 1 * ‖F g‖ := by gcongr
      _ = ‖F g‖ := one_mul _
  · obtain ⟨N, hN⟩ := cutoff_eventually_one (hh (toM g))
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun M hM => ?_⟩)
    simp [radialCutoffFunction, hN M hM]

lemma integrable_lie_derivative_pairing (hl : HhLip) (hz : IntRdZero) {a : ℝ} (ha : 0 ≤ a)
    {u u' : Matrix (Fin n) (Fin n) ℂ → ℂ} (hu : SmoothOnG ε u) (hu' : SmoothOnG ε u')
    (hu2 : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2) (muG ε))
    (hu2' : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖u' (toM g)‖ ^ 2) (muG ε))
    (i j : Fin n)
    (hv2 : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖Eab ε i j u (toM g)‖ ^ 2)
      (muG ε))
    (hv2' : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖Eab ε j i u' (toM g)‖ ^ 2)
      (muG ε)) :
    ∫ g : UJ ε, Eab ε i j u (toM g) * starRingEnd ℂ (u' (toM g)) ∂(muG ε) =
      ((sgn ε i j : ℝ) : ℂ) * ∫ g : UJ ε, u (toM g) * starRingEnd ℂ (Eab ε j i u' (toM g)) ∂(muG ε) := by
  have hv := smooth_lie_derivative i j hu
  have hv' := smooth_lie_derivative j i hu'
  have P1 := integrable_mul_conj_of_weighted ha hv hu' hv2 hu2'
  have P2 := integrable_mul_conj_of_weighted ha hu hv' hu2 hv2'
  have P0 := integrable_mul_conj_of_weighted ha hu hu' hu2 hu2'
  set s : ℂ := ((sgn ε i j : ℝ) : ℂ) with hs
  set A : ℕ → ℂ := fun N => ∫ g : UJ ε, radialCutoffFunction ((N : ℝ) + 1) (toM g) *
    (Eab ε i j u (toM g) * starRingEnd ℂ (u' (toM g))) ∂(muG ε) with hA
  set Bq : ℕ → ℂ := fun N => ∫ g : UJ ε, radialCutoffFunction ((N : ℝ) + 1) (toM g) *
    (u (toM g) * starRingEnd ℂ (Eab ε j i u' (toM g))) ∂(muG ε) with hBq
  set C : ℕ → ℂ := fun N => ∫ g : UJ ε, Eab ε i j (radialCutoffFunction ((N : ℝ) + 1)) (toM g) * u (toM g) *
    starRingEnd ℂ (u' (toM g)) ∂(muG ε) with hC
  have hrel : ∀ N, A N = s * Bq N - C N := by
    intro N
    have hR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have csm := smooth_cutoff (ε := ε) hl ((N : ℝ) + 1)
    have cv := cutoff_vanishing_outside (ε := ε) hR
    have hφs : SmoothOnG ε (fun x => (radialCutoffFunction ((N : ℝ) + 1) x * u x) * starRingEnd ℂ (u' x)) :=
      smooth_on_group_mul (smooth_on_group_mul csm hu) (smooth_on_group_conj hu')
    have hφv : VanishesOutsideBall ε (Real.exp (2 * ((N : ℝ) + 1)))
        (fun x => (radialCutoffFunction ((N : ℝ) + 1) x * u x) * starRingEnd ℂ (u' x)) :=
      vanishing_outside_mul_left _ (vanishing_outside_mul_left _ cv)
    have h0 := integral_lie_derivative_eq_zero hz hφs hφv i j
    have key : ∀ g : UJ ε, Eab ε i j (fun x => (radialCutoffFunction ((N : ℝ) + 1) x * u x) * starRingEnd ℂ (u' x))
        (toM g) = Eab ε i j (radialCutoffFunction ((N : ℝ) + 1)) (toM g) * u (toM g) * starRingEnd ℂ (u' (toM g)) +
          radialCutoffFunction ((N : ℝ) + 1) (toM g) * (Eab ε i j u (toM g) * starRingEnd ℂ (u' (toM g))) +
          (-s) * (radialCutoffFunction ((N : ℝ) + 1) (toM g) * (u (toM g) * starRingEnd ℂ (Eab ε j i u' (toM g)))) := by
      intro g
      rw [lie_derivative_mul i j (smooth_on_group_mul csm hu) (smooth_on_group_conj hu') g.2, lie_derivative_mul i j csm hu g.2,
        lie_derivative_conj i j hu' g.2]
      ring
    have i1 : Integrable (fun g : UJ ε => Eab ε i j (radialCutoffFunction ((N : ℝ) + 1)) (toM g) * u (toM g) *
        starRingEnd ℂ (u' (toM g))) (muG ε) :=
      integrable_of_vanishing_outside (f := fun x => Eab ε i j (radialCutoffFunction ((N : ℝ) + 1)) x * u x * starRingEnd ℂ (u' x))
        (smooth_on_group_mul (smooth_on_group_mul (smooth_lie_derivative i j csm) hu) (smooth_on_group_conj hu'))
        (vanishing_outside_mul_left _ (vanishing_outside_mul_left _ (vanishing_outside_lie_derivative i j cv)))
    have i2 : Integrable (fun g : UJ ε => radialCutoffFunction ((N : ℝ) + 1) (toM g) *
        (Eab ε i j u (toM g) * starRingEnd ℂ (u' (toM g)))) (muG ε) :=
      integrable_of_vanishing_outside (f := fun x => radialCutoffFunction ((N : ℝ) + 1) x * (Eab ε i j u x * starRingEnd ℂ (u' x)))
        (smooth_on_group_mul csm (smooth_on_group_mul hv (smooth_on_group_conj hu'))) (vanishing_outside_mul_left _ cv)
    have i3 : Integrable (fun g : UJ ε => radialCutoffFunction ((N : ℝ) + 1) (toM g) *
        (u (toM g) * starRingEnd ℂ (Eab ε j i u' (toM g)))) (muG ε) :=
      integrable_of_vanishing_outside (f := fun x => radialCutoffFunction ((N : ℝ) + 1) x * (u x * starRingEnd ℂ (Eab ε j i u' x)))
        (smooth_on_group_mul csm (smooth_on_group_mul hu (smooth_on_group_conj hv'))) (vanishing_outside_mul_left _ cv)
    rw [integral_congr_ae (Eventually.of_forall key)] at h0
    have e1 := integral_add (i1.add i2) (i3.const_mul (-s))
    simp only [Pi.add_apply] at e1
    rw [integral_add i1 i2, integral_const_mul] at e1
    rw [e1] at h0
    simp only [hA, hBq, hC]
    linear_combination h0
  have hCt : Tendsto C atTop (𝓝 0) := by
    set P := ∫ g : UJ ε, ‖u (toM g) * starRingEnd ℂ (u' (toM g))‖ ∂(muG ε)
    have hb : ∀ N : ℕ, ‖C N‖ ≤ cutoffDerivBound * lieDerivativeLogFrobeniusBound ε i j * P * (1 / ((N : ℝ) + 1)) := by
      intro N
      have hR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      refine (norm_integral_le_integral_norm _).trans ?_
      have hpt : ∀ g : UJ ε, ‖Eab ε i j (radialCutoffFunction ((N : ℝ) + 1)) (toM g) * u (toM g) *
          starRingEnd ℂ (u' (toM g))‖ ≤ (cutoffDerivBound * lieDerivativeLogFrobeniusBound ε i j * (1 / ((N : ℝ) + 1))) *
            ‖u (toM g) * starRingEnd ℂ (u' (toM g))‖ := by
        intro g
        have h1 : ‖Eab ε i j (radialCutoffFunction ((N : ℝ) + 1)) (toM g)‖ ≤
            cutoffDerivBound * lieDerivativeLogFrobeniusBound ε i j * (1 / ((N : ℝ) + 1)) := by
          have := lie_derivative_log_frobenius_comp_le (ε := ε) hl (radialCutoff ((N : ℝ) + 1)) (contDiff_radialCutoff _) i j g.2
          refine this.trans ?_
          have h2 := abs_deriv_cutoff_le hR (hh (toM g))
          have hL := lie_derivative_bound_nonneg ε i j
          calc |deriv (radialCutoff ((N : ℝ) + 1)) (hh (toM g))| * lieDerivativeLogFrobeniusBound ε i j ≤
              cutoffDerivBound / ((N : ℝ) + 1) * lieDerivativeLogFrobeniusBound ε i j := by gcongr
            _ = _ := by ring
        rw [mul_assoc, norm_mul]
        gcongr
      have hi : Integrable (fun g : UJ ε => (cutoffDerivBound * lieDerivativeLogFrobeniusBound ε i j * (1 / ((N : ℝ) + 1))) *
          ‖u (toM g) * starRingEnd ℂ (u' (toM g))‖) (muG ε) :=
        Integrable.const_mul (f := fun g : UJ ε => ‖u (toM g) * starRingEnd ℂ (u' (toM g))‖)
          P0.norm _
      have i1 : Integrable (fun g : UJ ε => Eab ε i j (radialCutoffFunction ((N : ℝ) + 1)) (toM g) * u (toM g) *
          starRingEnd ℂ (u' (toM g))) (muG ε) :=
        integrable_of_vanishing_outside (f := fun x => Eab ε i j (radialCutoffFunction ((N : ℝ) + 1)) x * u x * starRingEnd ℂ (u' x))
          (smooth_on_group_mul (smooth_on_group_mul (smooth_lie_derivative i j (smooth_cutoff hl _)) hu) (smooth_on_group_conj hu'))
          (vanishing_outside_mul_left _ (vanishing_outside_mul_left _ (vanishing_outside_lie_derivative i j (cutoff_vanishing_outside hR))))
      refine (integral_mono i1.norm hi hpt).trans ?_
      rw [integral_const_mul]
      ring_nf; rfl
    have ht : Tendsto (fun N : ℕ => cutoffDerivBound * lieDerivativeLogFrobeniusBound ε i j * P * (1 / ((N : ℝ) + 1))) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (cutoffDerivBound * lieDerivativeLogFrobeniusBound ε i j * P)
      simpa using this
    exact squeeze_zero_norm hb ht
  have hAt : Tendsto A atTop (𝓝 (∫ g : UJ ε, Eab ε i j u (toM g) * starRingEnd ℂ (u' (toM g))
      ∂(muG ε))) := tendsto_integral_cutoff P1
  have hBt : Tendsto Bq atTop (𝓝 (∫ g : UJ ε, u (toM g) * starRingEnd ℂ (Eab ε j i u' (toM g))
      ∂(muG ε))) := tendsto_integral_cutoff P2
  have hAt2 : Tendsto A atTop (𝓝 (s * (∫ g : UJ ε, u (toM g) * starRingEnd ℂ (Eab ε j i u' (toM g))
      ∂(muG ε)) - 0)) := by
    have := (hBt.const_mul s).sub hCt
    refine this.congr' (Eventually.of_forall fun N => ?_)
    exact (hrel N).symm
  rw [sub_zero] at hAt2
  exact tendsto_nhds_unique hAt hAt2

end F4BUL

section F4BAlg
variable {n : ℕ} (ε : Fin n → Bool)

def smoothFunctionsOnGroup : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ) where
  carrier := {f | SmoothOnG ε f}
  add_mem' := fun hf hh => smooth_on_group_add hf hh
  zero_mem' := smooth_on_group_const_fun 0
  smul_mem' := fun c _ hf => smooth_on_group_const_mul c hf

def vanishingOnGroup : Submodule ℂ (smoothFunctionsOnGroup ε) where
  carrier := {f | ∀ g, inUJ ε g → (f : Matrix (Fin n) (Fin n) ℂ → ℂ) g = 0}
  add_mem' := by
    intro f h hf hh g hg
    show (f : Matrix (Fin n) (Fin n) ℂ → ℂ) g + (h : Matrix (Fin n) (Fin n) ℂ → ℂ) g = 0
    rw [hf g hg, hh g hg, add_zero]
  zero_mem' := fun _ _ => rfl
  smul_mem' := by
    intro c f hf g hg
    show c * (f : Matrix (Fin n) (Fin n) ℂ → ℂ) g = 0
    rw [hf g hg, mul_zero]

abbrev SmoothFunctionsModGroup := (smoothFunctionsOnGroup ε) ⧸ (vanishingOnGroup ε)

variable {ε}

lemma smoothFunctions_smooth (u : smoothFunctionsOnGroup ε) : SmoothOnG ε (u : Matrix (Fin n) (Fin n) ℂ → ℂ) := u.2

def quotientMkAlt (u : smoothFunctionsOnGroup ε) : SmoothFunctionsModGroup ε := Submodule.Quotient.mk u

lemma quotient_mk_eq_iff {u v : smoothFunctionsOnGroup ε} :
    quotientMkAlt u = quotientMkAlt v ↔ ∀ g, inUJ ε g → (u : Matrix (Fin n) (Fin n) ℂ → ℂ) g = (v : Matrix (Fin n) (Fin n) ℂ → ℂ) g := by
  unfold quotientMkAlt
  rw [Submodule.Quotient.eq]
  constructor
  · intro h g hg
    have := h g hg
    exact sub_eq_zero.1 this
  · intro h g hg
    show (u : Matrix (Fin n) (Fin n) ℂ → ℂ) g - (v : Matrix (Fin n) (Fin n) ℂ → ℂ) g = 0
    rw [h g hg, sub_self]

lemma quotient_mk_add (u v : smoothFunctionsOnGroup ε) : quotientMkAlt (u + v) = quotientMkAlt u + quotientMkAlt v := rfl
lemma quotient_mk_sub (u v : smoothFunctionsOnGroup ε) : quotientMkAlt (u - v) = quotientMkAlt u - quotientMkAlt v := rfl
lemma quotient_mk_smul (c : ℂ) (u : smoothFunctionsOnGroup ε) : quotientMkAlt (c • u) = c • quotientMkAlt u := rfl
lemma quotient_mk_zero : quotientMkAlt (0 : smoothFunctionsOnGroup ε) = 0 := rfl

lemma quotient_mk_surjective (m : SmoothFunctionsModGroup ε) : ∃ u : smoothFunctionsOnGroup ε, m = quotientMkAlt u := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  exact ⟨u, rfl⟩

variable (ε)

def lieOperatorSmooth (i j : Fin n) : smoothFunctionsOnGroup ε →ₗ[ℂ] SmoothFunctionsModGroup ε where
  toFun u := quotientMkAlt ⟨Eab ε i j u, smooth_lie_derivative i j u.2⟩
  map_add' u v := by
    rw [← quotient_mk_add, quotient_mk_eq_iff]
    intro g hg
    show Eab ε i j (fun x => (u : Matrix (Fin n) (Fin n) ℂ → ℂ) x + (v : Matrix (Fin n) (Fin n) ℂ → ℂ) x) g =
      Eab ε i j u g + Eab ε i j v g
    have := lie_derivative_add_smul i j 1 u.2 v.2 hg
    simp only [one_mul] at this
    exact this
  map_smul' c u := by
    rw [RingHom.id_apply, ← quotient_mk_smul, quotient_mk_eq_iff]
    intro g hg
    show Eab ε i j (fun x => c * (u : Matrix (Fin n) (Fin n) ℂ → ℂ) x) g = c * Eab ε i j u g
    have := lie_derivative_add_smul i j c (smooth_on_group_const_fun (ε := ε) 0) u.2 hg
    simp only [zero_add, lie_derivative_const_zero] at this
    exact this

def lieOperatorQuotient (i j : Fin n) : Module.End ℂ (SmoothFunctionsModGroup ε) :=
  (vanishingOnGroup ε).liftQ (lieOperatorSmooth ε i j) (by
    intro u hu
    rw [LinearMap.mem_ker]
    show quotientMkAlt _ = 0
    rw [← quotient_mk_zero, quotient_mk_eq_iff]
    intro g hg
    show Eab ε i j u g = 0
    rw [lie_derivative_congr (h := fun _ => (0 : ℂ)) i j (fun x hx => hu x hx) hg, lie_derivative_const_zero])

variable {ε}

lemma lie_operator_quotient_mk (i j : Fin n) (u : smoothFunctionsOnGroup ε) :
    lieOperatorQuotient ε i j (quotientMkAlt u) = quotientMkAlt ⟨Eab ε i j u, smooth_lie_derivative i j u.2⟩ := rfl

lemma lie_operators_gl_relations : GlRel (lieOperatorQuotient ε) := by
  intro a b c d
  apply Submodule.linearMap_qext
  refine LinearMap.ext fun u => ?_
  have hGl := fun g (hg : inUJ ε g) => eabGl_of complex_parts_mem_lie_algebra_holds right_derivative_linear
    (rdBracket_of right_derivative_extends (rdSmooth_of right_derivative_extends)) (rdSmooth_of right_derivative_extends) n ε u a b c d g
    u.2 hg
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.sub_apply, Module.End.mul_apply]
  change lieOperatorQuotient ε a b (lieOperatorQuotient ε c d (quotientMkAlt u)) - lieOperatorQuotient ε c d (lieOperatorQuotient ε a b (quotientMkAlt u)) =
    (if b = c then lieOperatorQuotient ε a d else 0) (quotientMkAlt u) - (if d = a then lieOperatorQuotient ε c b else 0) (quotientMkAlt u)
  simp only [lie_operator_quotient_mk]
  by_cases h1 : b = c <;> by_cases h2 : d = a <;>
    simp only [h1, h2, if_true, if_false, LinearMap.zero_apply, lie_operator_quotient_mk] at hGl ⊢
  · rw [← quotient_mk_sub, ← quotient_mk_sub, quotient_mk_eq_iff]
    intro g hg; have := hGl g hg
    simp only [Submodule.coe_sub, Submodule.coe_zero, Submodule.coe_mk, Pi.sub_apply,
      Pi.zero_apply, sub_zero, zero_sub, Submodule.coe_neg, Pi.neg_apply] at this ⊢
    linear_combination this
  · rw [← quotient_mk_sub, ← quotient_mk_zero, ← quotient_mk_sub, quotient_mk_eq_iff]
    intro g hg; have := hGl g hg
    simp only [Submodule.coe_sub, Submodule.coe_zero, Submodule.coe_mk, Pi.sub_apply,
      Pi.zero_apply, sub_zero, zero_sub, Submodule.coe_neg, Pi.neg_apply] at this ⊢
    linear_combination this
  · rw [← quotient_mk_sub, ← quotient_mk_zero, ← quotient_mk_sub, quotient_mk_eq_iff]
    intro g hg; have := hGl g hg
    simp only [Submodule.coe_sub, Submodule.coe_zero, Submodule.coe_mk, Pi.sub_apply,
      Pi.zero_apply, sub_zero, zero_sub, Submodule.coe_neg, Pi.neg_apply] at this ⊢
    linear_combination this
  · rw [← quotient_mk_sub, sub_zero, ← quotient_mk_zero, quotient_mk_eq_iff]
    intro g hg; have := hGl g hg
    simp only [Submodule.coe_sub, Submodule.coe_zero, Submodule.coe_mk, Pi.sub_apply,
      Pi.zero_apply, sub_zero, zero_sub, Submodule.coe_neg, Pi.neg_apply] at this ⊢
    linear_combination this

end F4BAlg

section F4BAlg2
variable {n : ℕ} {ε : Fin n → Bool}

lemma finset_sum_quotient_mk {ι : Type*} (s : Finset ι) (f : ι → smoothFunctionsOnGroup ε) :
    ∑ i ∈ s, quotientMkAlt (f i) = quotientMkAlt (∑ i ∈ s, f i) :=
  (map_sum (vanishingOnGroup ε).mkQ f s).symm

lemma coe_finset_sum_smooth {ι : Type*} (s : Finset ι) (f : ι → smoothFunctionsOnGroup ε) (x : Matrix (Fin n) (Fin n) ℂ) :
    ((∑ i ∈ s, f i : smoothFunctionsOnGroup ε) : Matrix (Fin n) (Fin n) ℂ → ℂ) x =
      ∑ i ∈ s, (f i : Matrix (Fin n) (Fin n) ℂ → ℂ) x := by
  rw [Submodule.coe_sum, Finset.sum_apply]

lemma smooth_casimir {u : Matrix (Fin n) (Fin n) ℂ → ℂ} (hu : SmoothOnG ε u) : SmoothOnG ε (CasF ε u) :=
  smooth_on_group_sum _ _ fun a _ => smooth_on_group_sum _ _ fun b _ => smooth_lie_derivative a b (smooth_lie_derivative b a hu)

lemma casimir_quotient_mk (u : smoothFunctionsOnGroup ε) :
    Cas (lieOperatorQuotient ε) (quotientMkAlt u) = quotientMkAlt ⟨CasF ε u, smooth_casimir (smoothFunctions_smooth u)⟩ := by
  unfold Cas
  simp only [LinearMap.sum_apply, Module.End.mul_apply, lie_operator_quotient_mk, finset_sum_quotient_mk]
  rw [quotient_mk_eq_iff]
  intro g _
  simp only [coe_finset_sum_smooth]
  rfl

def signedCasimirQuotient (ε : Fin n → Bool) : Module.End ℂ (SmoothFunctionsModGroup ε) :=
  ∑ i, ∑ j, ((sgn ε i j : ℝ) : ℂ) • (lieOperatorQuotient ε j i * lieOperatorQuotient ε i j)

lemma signedCasimir_quotient_mk (u : smoothFunctionsOnGroup ε) :
    signedCasimirQuotient ε (quotientMkAlt u) = quotientMkAlt ⟨signedCasimirDifference ε u, smooth_signedCasimir (smoothFunctions_smooth u)⟩ := by
  unfold signedCasimirQuotient
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
    lie_operator_quotient_mk, ← quotient_mk_smul, finset_sum_quotient_mk]
  rw [quotient_mk_eq_iff]
  intro g _
  simp only [coe_finset_sum_smooth, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  rfl

lemma signed_casimir_identity {A : Type*} [Ring A] [Algebra ℂ A] (E : Fin n → Fin n → A) :
    ∑ i, ∑ j, ((sgn ε i j : ℝ) : ℂ) • (E j i * E i j) = (2 : ℂ) • CasK ε E - Cas E := by
  rw [Finset.sum_comm]
  unfold CasK Cas
  rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [signature_sign_symm]
  unfold sgn
  by_cases h : ε a = ε b
  · rw [if_pos h, if_pos h]; simp only [Complex.ofReal_one, one_smul, two_smul]; abel
  · rw [if_neg h, if_neg h]; simp

def wordActionQuotient (ε : Fin n → Bool) : List (Fin n × Fin n) → SmoothFunctionsModGroup ε → SmoothFunctionsModGroup ε
  | [] => fun m => m
  | p :: w => fun m => lieOperatorQuotient ε p.1 p.2 (wordActionQuotient ε w m)

lemma word_action_quotient_mk (u : smoothFunctionsOnGroup ε) : ∀ w : List (Fin n × Fin n),
    wordActionQuotient ε w (quotientMkAlt u) = quotientMkAlt ⟨Eword ε w u, smooth_iterated_lie_derivative (smoothFunctions_smooth u) w⟩
  | [] => rfl
  | p :: w => by
    show lieOperatorQuotient ε p.1 p.2 (wordActionQuotient ε w (quotientMkAlt u)) = _
    rw [word_action_quotient_mk u w, lie_operator_quotient_mk]
    rfl

lemma word_action_smul (c : ℂ) (m : SmoothFunctionsModGroup ε) : ∀ w : List (Fin n × Fin n),
    wordActionQuotient ε w (c • m) = c • wordActionQuotient ε w m
  | [] => rfl
  | p :: w => by
    show lieOperatorQuotient ε p.1 p.2 (wordActionQuotient ε w (c • m)) = c • lieOperatorQuotient ε p.1 p.2 (wordActionQuotient ε w m)
    rw [word_action_smul c m w, map_smul]

lemma word_action_commute (X : Module.End ℂ (SmoothFunctionsModGroup ε)) (hX : ∀ i j, X * lieOperatorQuotient ε i j = lieOperatorQuotient ε i j * X)
    (m : SmoothFunctionsModGroup ε) : ∀ w : List (Fin n × Fin n), X (wordActionQuotient ε w m) = wordActionQuotient ε w (X m)
  | [] => rfl
  | p :: w => by
    show X (lieOperatorQuotient ε p.1 p.2 (wordActionQuotient ε w m)) = lieOperatorQuotient ε p.1 p.2 (wordActionQuotient ε w (X m))
    rw [← word_action_commute X hX m w, ← Module.End.mul_apply, hX, Module.End.mul_apply]

variable (ε)

def weightVectorsQuotient (W : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ)) : Set (SmoothFunctionsModGroup ε) :=
  {m | ∃ f ∈ W, ∃ hf : SmoothOnG ε f, m = quotientMkAlt ⟨f, hf⟩}

def wordFiltration (W : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ)) (k : ℕ) : Submodule ℂ (SmoothFunctionsModGroup ε) :=
  Submodule.span ℂ {x | ∃ w : List (Fin n × Fin n), ∃ m ∈ weightVectorsQuotient ε W, w.length ≤ k ∧ x = wordActionQuotient ε w m}

variable {ε}
variable {W : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ)}

lemma word_mem_filtration {k : ℕ} {w : List (Fin n × Fin n)} {m : SmoothFunctionsModGroup ε} (hm : m ∈ weightVectorsQuotient ε W)
    (hw : w.length ≤ k) : wordActionQuotient ε w m ∈ wordFiltration ε W k :=
  Submodule.subset_span ⟨w, m, hm, hw, rfl⟩

lemma filtration_mono {k k' : ℕ} (h : k ≤ k') : wordFiltration ε W k ≤ wordFiltration ε W k' :=
  Submodule.span_mono fun _ ⟨w, m, hm, hw, hx⟩ => ⟨w, m, hm, hw.trans h, hx⟩

lemma lie_operator_raises_filtration (i j : Fin n) {k : ℕ} {x : SmoothFunctionsModGroup ε} (hx : x ∈ wordFiltration ε W k) :
    lieOperatorQuotient ε i j x ∈ wordFiltration ε W (k + 1) := by
  have : wordFiltration ε W k ≤ (wordFiltration ε W (k + 1)).comap (lieOperatorQuotient ε i j) := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨w, m, hm, hw, rfl⟩
    exact word_mem_filtration (w := (i, j) :: w) hm (by simp; omega)
  exact this hx

lemma weight_vectors_stable (hsm : ∀ w ∈ W, SmoothOnG ε w)
    (hstab : ∀ w ∈ W, ∀ i j : Fin n, ε i = ε j → ∃ w' ∈ W, ∀ g, inUJ ε g → Eab ε i j w g = w' g)
    {m : SmoothFunctionsModGroup ε} (hm : m ∈ weightVectorsQuotient ε W) {c d : Fin n} (hcd : ε c = ε d) :
    lieOperatorQuotient ε c d m ∈ weightVectorsQuotient ε W := by
  obtain ⟨f, hfW, hf, rfl⟩ := hm
  obtain ⟨f', hf'W, he⟩ := hstab f hfW c d hcd
  refine ⟨f', hf'W, hsm f' hf'W, ?_⟩
  rw [lie_operator_quotient_mk, quotient_mk_eq_iff]
  exact he

lemma lie_operator_word_mem_filtration (hsm : ∀ w ∈ W, SmoothOnG ε w)
    (hstab : ∀ w ∈ W, ∀ i j : Fin n, ε i = ε j → ∃ w' ∈ W, ∀ g, inUJ ε g → Eab ε i j w g = w' g)
    {c d : Fin n} (hcd : ε c = ε d) {m : SmoothFunctionsModGroup ε} (hm : m ∈ weightVectorsQuotient ε W) :
    ∀ w : List (Fin n × Fin n), lieOperatorQuotient ε c d (wordActionQuotient ε w m) ∈ wordFiltration ε W w.length
  | [] => word_mem_filtration (w := []) (weight_vectors_stable hsm hstab hm hcd) le_rfl
  | p :: w => by
    have ih := lie_operator_word_mem_filtration hsm hstab hcd hm w
    have hgl := lie_operators_gl_relations (ε := ε) c d p.1 p.2
    have key : lieOperatorQuotient ε c d (lieOperatorQuotient ε p.1 p.2 (wordActionQuotient ε w m)) =
        lieOperatorQuotient ε p.1 p.2 (lieOperatorQuotient ε c d (wordActionQuotient ε w m)) +
          ((if d = p.1 then lieOperatorQuotient ε c p.2 else 0) (wordActionQuotient ε w m) -
            (if p.2 = c then lieOperatorQuotient ε p.1 d else 0) (wordActionQuotient ε w m)) := by
      have := congrArg (fun T => T (wordActionQuotient ε w m)) hgl
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
      rw [← this]; abel
    show lieOperatorQuotient ε c d (lieOperatorQuotient ε p.1 p.2 (wordActionQuotient ε w m)) ∈ wordFiltration ε W (w.length + 1)
    rw [key]
    refine add_mem (lie_operator_raises_filtration _ _ ih) (sub_mem ?_ ?_)
    · split_ifs
      · exact word_mem_filtration (w := (c, p.2) :: w) hm (by simp)
      · rw [LinearMap.zero_apply]; exact zero_mem _
    · split_ifs
      · exact word_mem_filtration (w := (p.1, d) :: w) hm (by simp)
      · rw [LinearMap.zero_apply]; exact zero_mem _

lemma compact_lie_operator_preserves_filtration (hsm : ∀ w ∈ W, SmoothOnG ε w)
    (hstab : ∀ w ∈ W, ∀ i j : Fin n, ε i = ε j → ∃ w' ∈ W, ∀ g, inUJ ε g → Eab ε i j w g = w' g)
    {c d : Fin n} (hcd : ε c = ε d) {k : ℕ} {x : SmoothFunctionsModGroup ε} (hx : x ∈ wordFiltration ε W k) :
    lieOperatorQuotient ε c d x ∈ wordFiltration ε W k := by
  have : wordFiltration ε W k ≤ (wordFiltration ε W k).comap (lieOperatorQuotient ε c d) := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨w, m, hm, hw, rfl⟩
    exact filtration_mono hw (lie_operator_word_mem_filtration hsm hstab hcd hm w)
  exact this hx

lemma compact_casimir_preserves_filtration (hsm : ∀ w ∈ W, SmoothOnG ε w)
    (hstab : ∀ w ∈ W, ∀ i j : Fin n, ε i = ε j → ∃ w' ∈ W, ∀ g, inUJ ε g → Eab ε i j w g = w' g)
    {k : ℕ} {x : SmoothFunctionsModGroup ε} (hx : x ∈ wordFiltration ε W k) : CasK ε (lieOperatorQuotient ε) x ∈ wordFiltration ε W k := by
  unfold CasK
  simp only [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
  split_ifs with h
  · rw [Module.End.mul_apply]
    exact compact_lie_operator_preserves_filtration hsm hstab h (compact_lie_operator_preserves_filtration hsm hstab h.symm hx)
  · rw [LinearMap.zero_apply]; exact zero_mem _

lemma casimir_scalar_on_filtration (hsm : ∀ w ∈ W, SmoothOnG ε w) {c : ℂ}
    (hcas : ∀ w ∈ W, ∀ g, inUJ ε g → CasF ε w g = c * w g)
    {k : ℕ} {x : SmoothFunctionsModGroup ε} (hx : x ∈ wordFiltration ε W k) : Cas (lieOperatorQuotient ε) x = c • x := by
  have hcomm := (casimir_central_holds (Module.End ℂ (SmoothFunctionsModGroup ε)) n ε (lieOperatorQuotient ε) lie_operators_gl_relations).1
  have : wordFiltration ε W k ≤ LinearMap.ker (Cas (lieOperatorQuotient ε) - c • (1 : Module.End ℂ (SmoothFunctionsModGroup ε))) := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨w, m, ⟨f, hfW, hf, rfl⟩, _, rfl⟩
    show (Cas (lieOperatorQuotient ε) - c • (1 : Module.End ℂ (SmoothFunctionsModGroup ε))) _ = 0
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero,
      word_action_commute _ hcomm, ← word_action_smul]
    congr 1
    rw [casimir_quotient_mk, ← quotient_mk_smul, quotient_mk_eq_iff]
    intro g hg
    show CasF ε f g = c * f g
    exact hcas f hfW g hg
  have h := this hx
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    sub_eq_zero] at h
  exact h

lemma signedCasimir_preserves_filtration (hsm : ∀ w ∈ W, SmoothOnG ε w)
    (hstab : ∀ w ∈ W, ∀ i j : Fin n, ε i = ε j → ∃ w' ∈ W, ∀ g, inUJ ε g → Eab ε i j w g = w' g)
    {c : ℂ} (hcas : ∀ w ∈ W, ∀ g, inUJ ε g → CasF ε w g = c * w g)
    {k : ℕ} {x : SmoothFunctionsModGroup ε} (hx : x ∈ wordFiltration ε W k) : signedCasimirQuotient ε x ∈ wordFiltration ε W k := by
  unfold signedCasimirQuotient
  rw [signed_casimir_identity, LinearMap.sub_apply, LinearMap.smul_apply, casimir_scalar_on_filtration hsm hcas hx]
  exact sub_mem (Submodule.smul_mem _ _ (compact_casimir_preserves_filtration hsm hstab hx)) (Submodule.smul_mem _ _ hx)

end F4BAlg2

section F4BMain
variable {n : ℕ} {ε : Fin n → Bool}

variable (ε) in
def evalSmoothFunctions : smoothFunctionsOnGroup ε →ₗ[ℂ] (UJ ε → ℂ) where
  toFun u := fun g => (u : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (ε) in
def evalQuotient : SmoothFunctionsModGroup ε →ₗ[ℂ] (UJ ε → ℂ) :=
  (vanishingOnGroup ε).liftQ (evalSmoothFunctions ε) (by
    intro u hu
    rw [LinearMap.mem_ker]
    funext g
    exact hu _ g.2)

lemma evalQuotient_mk (u : smoothFunctionsOnGroup ε) :
    evalQuotient ε (quotientMkAlt u) = fun g => (u : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g) := rfl

variable (ε) in
def weightedSquareIntegrable (a : ℝ) : Submodule ℂ (SmoothFunctionsModGroup ε) where
  carrier := {m | Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖evalQuotient ε m g‖ ^ 2)
    (muG ε)}
  zero_mem' := by
    show Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖evalQuotient ε 0 g‖ ^ 2) (muG ε)
    simp only [map_zero, Pi.zero_apply, norm_zero]
    simpa using (integrable_zero (UJ ε) ℝ (muG ε))
  add_mem' := by
    intro x y hx hy
    obtain ⟨u, rfl⟩ := quotient_mk_surjective x
    obtain ⟨v, rfl⟩ := quotient_mk_surjective y
    show Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) *
      ‖evalQuotient ε (quotientMkAlt u + quotientMkAlt v) g‖ ^ 2) (muG ε)
    have hx' : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) *
        ‖(u : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g)‖ ^ 2) (muG ε) := hx
    have hy' : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) *
        ‖(v : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g)‖ ^ 2) (muG ε) := hy
    rw [← quotient_mk_add, evalQuotient_mk]
    have hb : Integrable (fun g : UJ ε => 2 * (Real.exp (2 * a * hh (toM g)) *
        ‖(u : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g)‖ ^ 2) + 2 * (Real.exp (2 * a * hh (toM g)) *
        ‖(v : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g)‖ ^ 2)) (muG ε) :=
      Integrable.add (f := fun g : UJ ε => 2 * (Real.exp (2 * a * hh (toM g)) *
          ‖(u : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g)‖ ^ 2))
        (g := fun g : UJ ε => 2 * (Real.exp (2 * a * hh (toM g)) *
          ‖(v : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g)‖ ^ 2))
        (Integrable.const_mul (f := fun g : UJ ε => Real.exp (2 * a * hh (toM g)) *
          ‖(u : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g)‖ ^ 2) hx' 2)
        (Integrable.const_mul (f := fun g : UJ ε => Real.exp (2 * a * hh (toM g)) *
          ‖(v : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g)‖ ^ 2) hy' 2)
    refine hb.mono' (aestronglyMeasurable_weighted_norm_sq a (smoothFunctions_smooth (u + v))) (Eventually.of_forall fun g => ?_)
    have he := Real.exp_pos (2 * a * hh (toM g))
    have e1 : ((u + v : smoothFunctionsOnGroup ε) : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g) =
        (u : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g) + (v : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g) := rfl
    beta_reduce
    rw [e1, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 := norm_add_le ((u : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g))
      ((v : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g))
    have h2 : ‖(u : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g) + (v : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g)‖ ^ 2
        ≤ 2 * ‖(u : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g)‖ ^ 2 +
          2 * ‖(v : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g)‖ ^ 2 := by
      have := norm_nonneg ((u : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g) +
        (v : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g))
      nlinarith [sq_nonneg (‖(u : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g)‖ -
        ‖(v : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g)‖)]
    nlinarith
  smul_mem' := by
    intro c x hx
    obtain ⟨u, rfl⟩ := quotient_mk_surjective x
    show Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) *
      ‖evalQuotient ε (c • quotientMkAlt u) g‖ ^ 2) (muG ε)
    have hx' : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) *
        ‖(u : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g)‖ ^ 2) (muG ε) := hx
    rw [← quotient_mk_smul, evalQuotient_mk]
    refine (hx'.const_mul (‖c‖ ^ 2)).congr (Eventually.of_forall fun g => ?_)
    show ‖c‖ ^ 2 * (Real.exp (2 * a * hh (toM g)) * ‖(u : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g)‖ ^ 2) =
      Real.exp (2 * a * hh (toM g)) * ‖c * (u : Matrix (Fin n) (Fin n) ℂ → ℂ) (toM g)‖ ^ 2
    rw [norm_mul]; ring

lemma weighted_square_integrable_filtration (hl : HhLip) (hz : IntRdZero) {W : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ)}
    {c : ℂ} {a : ℝ} (ha : 0 ≤ a) (hsm : ∀ w ∈ W, SmoothOnG ε w)
    (hstab : ∀ w ∈ W, ∀ i j : Fin n, ε i = ε j → ∃ w' ∈ W, ∀ g, inUJ ε g → Eab ε i j w g = w' g)
    (hcas : ∀ w ∈ W, ∀ g, inUJ ε g → CasF ε w g = c * w g)
    (hint : ∀ w ∈ W, Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖w (toM g)‖ ^ 2)
      (muG ε)) :
    ∀ k : ℕ, ∀ w : List (Fin n × Fin n), w.length ≤ k → ∀ f ∈ W,
      Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖Eword ε w f (toM g)‖ ^ 2)
        (muG ε) := by
  intro k
  induction k with
  | zero =>
    intro w hw f hf
    have : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact hint f hf
  | succ k ih =>
    intro w hw f hf
    cases w with
    | nil => exact hint f hf
    | cons p w' =>
      have hw' : w'.length ≤ k := by simp at hw; omega
      have hu := smooth_iterated_lie_derivative (hsm f hf) w'
      have hu2 := ih w' hw' f hf
      have hVG : wordFiltration ε W k ≤ weightedSquareIntegrable ε a := by
        refine Submodule.span_le.2 ?_
        rintro x ⟨w'', m, ⟨f'', hf''W, hf'', rfl⟩, hw'', rfl⟩
        show Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) *
          ‖evalQuotient ε (wordActionQuotient ε w'' (quotientMkAlt ⟨f'', hf''⟩)) g‖ ^ 2) (muG ε)
        rw [word_action_quotient_mk, evalQuotient_mk]
        exact ih w'' hw'' f'' hf''W
      have hx : wordActionQuotient ε w' (quotientMkAlt ⟨f, hsm f hf⟩) ∈ wordFiltration ε W k :=
        word_mem_filtration ⟨f, hf, hsm f hf, rfl⟩ hw'
      have hT := hVG (signedCasimir_preserves_filtration hsm hstab hcas hx)
      have hT' : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) *
          ‖evalQuotient ε (signedCasimirQuotient ε (wordActionQuotient ε w' (quotientMkAlt ⟨f, hsm f hf⟩))) g‖ ^ 2) (muG ε) := hT
      rw [word_action_quotient_mk, signedCasimir_quotient_mk, evalQuotient_mk] at hT'
      exact integrable_lie_derivative_weighted hl hz ha hu hu2 hT' p.1 p.2

theorem square_integrable_of_lipschitz (hl : HhLip) (hz : IntRdZero) : SmoothVectorGrowthBound := by
  intro n ε W c a _ ha hsm hstab hcas hint w₁ w₂ f f' hf hf'
  have P : ∀ (w : List (Fin n × Fin n)) (f : Matrix (Fin n) (Fin n) ℂ → ℂ), f ∈ W →
      Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖Eword ε w f (toM g)‖ ^ 2)
        (muG ε) :=
    fun w f hf => weighted_square_integrable_filtration hl hz ha hsm hstab hcas hint w.length w le_rfl f hf
  refine ⟨smooth_iterated_lie_derivative (hsm f hf) w₁, P w₁ f hf, fun i j => ?_⟩
  exact integrable_lie_derivative_pairing hl hz ha (smooth_iterated_lie_derivative (hsm f hf) w₁) (smooth_iterated_lie_derivative (hsm f' hf') w₂)
    (P w₁ f hf) (P w₂ f' hf') i j (P ((i, j) :: w₁) f hf) (P ((j, i) :: w₂) f' hf')

end F4BMain

end Formalism.REAL
