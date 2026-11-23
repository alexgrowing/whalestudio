import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemiAbelianExponentialAlongDiscStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousLatticeVectorsAlongArc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameChangeEigenframeExponentialsHolArcStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousPeriodLatticeBasisArcStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialGrowthOfPeriodicIntegralSpansStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj

namespace GlobalTheory.ShFam.BdArc

theorem exists_period_basis_halfPlane
: ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)), GoodEmb c σ → 1 ≤ Dw.p + Dw.q → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ∀ s, (spMap (ψ u) ≫ x) s ∉ genBd Z) → ∃ (T₀ : ℝ) (m : ℕ) (lam : ℂ → Fin m → Fin g → ℂ), (∀ w : ℂ, T₀ < w.im → eTwoPi w ∈ Metric.ball (0 : ℂ) r) ∧ ContinuousOn lam {w : ℂ | T₀ < w.im} ∧ (∀ w : ℂ, T₀ < w.im → LinearIndependent ℝ (lam w) ∧ Submodule.span ℝ (Set.range (lam w)) = ⊤) ∧ (∀ w : ℂ, T₀ < w.im → ∀ ex : (Fin g → ℂ) → (Over.mk (spMap (ψ (eTwoPi w)) ≫ x ≫ genι Z) ⟶ Z.t.G), (∀ z z', ex (z + z') = ex z * ex z') → IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ Z.t.G.left from (ex z).left)) → (∀ j, IsDerivAt0 (fun z => (ex z).left) (Pi.single j 1) (spMap (dualMap (ψ (eTwoPi w))) ≫ fr.v (e j).1 (e j).2)) → ∀ z, ex z = 1 ↔ ∃ n : Fin m → ℤ, z = ∑ j, n j • lam w j) ∧ ∀ R : ℝ, ∃ (C : ℝ) (B : ℕ), ∀ w : ℂ, T₀ < w.im → |w.re| ≤ R → ‖lam w‖ ≤ C * w.im ^ B := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ A _ φ x fr ψ r g e hσ hpq harc hin
  obtain ⟨g', ρ, e', hρ, hρr, hol, hexp, -⟩ := GlobalTheory.T.exists_semi_abelian_exponential_along_disc Z.X Z.t.G (fun u => spMap (ψ u) ≫ x ≫ genι Z) r
    Z.t.semi harc.1.1 (GlobalTheory.ShFam.BdArc.LatSec.isHolTo_spMap harc.1 _)
  obtain ⟨h, hh⟩ := GlobalTheory.T.exists_frameChange_eigenframe_exponentials_holArc E H Dw l Xo c O β Z σ A φ x fr ψ r g e g' ρ e' harc hρ hρr hol hexp
  obtain ⟨ρ₀, m, lamE, hρ₀, hρ₀ρ, hcont, hlat, C, k, hC⟩ :=
    GlobalTheory.T.exists_continuous_period_lattice_basis_arc E H Dw l Xo c O β Z σ A φ x ψ r g' ρ e' hσ hpq harc hin hρ hρr hol hexp
  have hper : ∀ s : ℂ, s.re < 0 → ∀ z, (∃ n : Fin m → ℤ, z = ∑ j, n j • lamE (s + 2 * Real.pi * Complex.I) j) ↔
      ∃ n : Fin m → ℤ, z = ∑ j, n j • lamE s j := by
    intro s hs z
    have hs' : (s + 2 * Real.pi * Complex.I).re < 0 := by simpa using hs
    rw [← (hlat _ hs').2.2, ← (hlat s hs).2.2, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have hcb : Metric.closedBall (0 : ℂ) (ρ₀ / 2) ⊆ Metric.ball 0 ρ := Metric.closedBall_subset_ball (by linarith)
  obtain ⟨Ch, hCh⟩ := (isCompact_closedBall (0 : ℂ) (ρ₀ / 2)).exists_bound_of_continuousOn
    (fun u hu => ((hh u (hcb hu)).2.1).continuousWithinAt)
  have hCh0 : 0 ≤ Ch := (norm_nonneg _).trans (hCh 0 (Metric.mem_closedBall_self (by linarith)))
  set T₀ : ℝ := max 1 (Real.log (2 / ρ₀) / (2 * Real.pi)) with hT₀
  let sOf : ℂ → ℂ := fun w => 2 * Real.pi * Complex.I * w - (Real.log ρ₀ : ℂ)
  have hsOf : Continuous sOf := by fun_prop
  have hnorm : ∀ w : ℂ, ‖eTwoPi w‖ = Real.exp (-(2 * Real.pi * w.im)) := by
    intro w
    rw [eTwoPi, Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.mul_im]
  have hsmall : ∀ w : ℂ, T₀ < w.im → ‖eTwoPi w‖ < ρ₀ / 2 := by
    intro w hw
    have h1 : Real.log (2 / ρ₀) < 2 * Real.pi * w.im := by
      have := (le_max_right _ _).trans_lt hw
      rw [div_lt_iff₀ (by positivity)] at this
      linarith
    rw [hnorm]
    calc Real.exp (-(2 * Real.pi * w.im)) < Real.exp (-Real.log (2 / ρ₀)) := Real.exp_lt_exp.2 (by linarith)
      _ = ρ₀ / 2 := by rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  have hueq : ∀ w : ℂ, (ρ₀ : ℂ) * Complex.exp (sOf w) = eTwoPi w := by
    intro w
    simp only [sOf, eTwoPi]
    rw [Complex.exp_sub, ← Complex.ofReal_exp, Real.exp_log hρ₀, mul_div_cancel₀ _ (by exact_mod_cast hρ₀.ne')]
  have hexps : ∀ w : ℂ, ‖Complex.exp (sOf w)‖ = ‖eTwoPi w‖ / ρ₀ := by
    intro w
    rw [← hueq w, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ₀.le, mul_div_cancel_left₀ _ hρ₀.ne']
  have hexp2 : ∀ w : ℂ, T₀ < w.im → ‖Complex.exp (sOf w)‖ ≤ 1 / 2 := by
    intro w hw
    rw [hexps, div_le_iff₀ hρ₀]
    linarith [hsmall w hw]
  have hsre : ∀ w : ℂ, T₀ < w.im → (sOf w).re < 0 := by
    intro w hw
    have h1 := hexp2 w hw
    rw [Complex.norm_exp] at h1
    by_contra hc
    push_neg at hc
    have := Real.one_le_exp hc
    linarith
  have hub : ∀ w : ℂ, T₀ < w.im → eTwoPi w ∈ Metric.closedBall (0 : ℂ) (ρ₀ / 2) := fun w hw =>
    mem_closedBall_zero_iff.2 (hsmall w hw).le
  refine ⟨T₀, m, fun w j => (h (eTwoPi w)).inverse (lamE (sOf w) j), fun w hw => ?_, ?_, fun w hw => ?_,
    fun w hw ex hadd hex hd z => ?_, fun R => ?_⟩
  · exact Metric.ball_subset_ball (hρ₀ρ.le.trans hρr) (Metric.ball_subset_ball (by linarith) (mem_ball_zero_iff.2 (hsmall w hw)))
  · have hopen : IsOpen {w : ℂ | T₀ < w.im} := isOpen_lt continuous_const Complex.continuous_im
    refine fun w hw => ContinuousAt.continuousWithinAt ?_
    have hi : ContinuousAt (fun w => (h (eTwoPi w)).inverse) w :=
      ContinuousAt.comp (f := eTwoPi) (g := fun u => (h u).inverse) ((hh _ (hcb (hub w hw))).2.1)
        (by unfold eTwoPi; fun_prop)
    have hl : ContinuousAt (fun w => lamE (sOf w)) w :=
      ContinuousAt.comp (g := lamE) ((hcont.continuousAt (isOpen_lt Complex.continuous_re continuous_const |>.mem_nhds (hsre w hw))))
        hsOf.continuousAt
    exact continuousAt_pi.2 fun j => hi.clm_apply ((continuous_apply j).continuousAt.comp hl)
  · obtain ⟨L, hL⟩ := (hh _ (hcb (hub w hw))).1
    obtain ⟨hli, hsp, -⟩ := hlat _ (hsre w hw)
    simp only [← hL, ContinuousLinearMap.inverse_equiv]
    refine ⟨hli.map' (L.symm.toLinearEquiv.restrictScalars ℝ).toLinearMap (LinearEquiv.ker _), ?_⟩
    have : (Set.range fun j => (L.symm : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ)) (lamE (sOf w) j)) =
        (L.symm.toLinearEquiv.restrictScalars ℝ).toLinearMap '' Set.range (lamE (sOf w)) := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, hsp, Submodule.map_top, LinearEquiv.range]
  · obtain ⟨L, hL⟩ := (hh _ (hcb (hub w hw))).1
    have h1 := (hlat _ (hsre w hw)).2.2 (h (eTwoPi w) z)
    rw [hueq w] at h1
    rw [(hh _ (hcb (hub w hw))).2.2 ex hadd hex hd z, h1]
    simp only [← hL, ContinuousLinearMap.inverse_equiv, ContinuousLinearEquiv.coe_coe]
    refine exists_congr fun n => ?_
    rw [show ∑ j, n j • L.symm (lamE (sOf w) j) = L.symm (∑ j, n j • lamE (sOf w) j) by
        rw [map_sum]; exact Finset.sum_congr rfl fun j _ => (map_zsmul L.symm _ _).symm,
      ContinuousLinearEquiv.eq_symm_apply]
  · obtain ⟨C', hC'⟩ := GlobalTheory.T.polynomial_growth_of_periodic_integral_spans g' m lamE C k hcont (fun s hs => (hlat s hs).1) hper hC (2 * Real.pi * |R|)
    set D : ℝ := 1 + 2 * Real.pi + |Real.log ρ₀| + 2 * Real.pi * |R|
    refine ⟨Ch * max C' 0 * D ^ k, k, fun w hw hR => ?_⟩
    have hw1 : 1 ≤ w.im := (le_max_left _ _).trans hw.le
    have hsim : (sOf w).im = 2 * Real.pi * w.re := by simp [sOf, Complex.mul_re, Complex.mul_im]
    have hsre' : (sOf w).re = -(2 * Real.pi * w.im) - Real.log ρ₀ := by simp [sOf, Complex.mul_re, Complex.mul_im]
    have hsi : |(sOf w).im| ≤ 2 * Real.pi * |R| := by
      rw [hsim, abs_mul, abs_of_pos (by positivity)]
      exact mul_le_mul_of_nonneg_left (hR.trans (le_abs_self R)) (by positivity)
    have hb := hC' _ (hsre w hw) (hexp2 w hw) hsi
    have hsn : 1 + ‖sOf w‖ ≤ D * w.im := by
      have h2 := Complex.norm_le_abs_re_add_abs_im (sOf w)
      have h3 : |(sOf w).re| ≤ 2 * Real.pi * w.im + |Real.log ρ₀| := by
        rw [hsre']
        refine (abs_sub _ _).trans ?_
        rw [abs_neg, abs_of_pos (by positivity)]
      have h4 : 0 ≤ w.im - 1 := by linarith
      have h5 : 0 ≤ |Real.log ρ₀| + 2 * Real.pi * |R| + 1 := by positivity
      nlinarith [Real.pi_pos]
    have hpow : (1 + ‖sOf w‖) ^ k ≤ D ^ k * w.im ^ k := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hsn k
    have hlamn : ‖lamE (sOf w)‖ ≤ max C' 0 * (D ^ k * w.im ^ k) :=
      hb.trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans
        (mul_le_mul_of_nonneg_left hpow (le_max_right _ _)))
    have hCu := hCh _ (hub w hw)
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    calc ‖(h (eTwoPi w)).inverse (lamE (sOf w) j)‖ ≤ ‖(h (eTwoPi w)).inverse‖ * ‖lamE (sOf w) j‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ Ch * ‖lamE (sOf w)‖ := mul_le_mul hCu (norm_le_pi_norm _ j) (norm_nonneg _) hCh0
      _ ≤ Ch * (max C' 0 * (D ^ k * w.im ^ k)) := mul_le_mul_of_nonneg_left hlamn hCh0
      _ = Ch * max C' 0 * D ^ k * w.im ^ k := by ring

end GlobalTheory.ShFam.BdArc
