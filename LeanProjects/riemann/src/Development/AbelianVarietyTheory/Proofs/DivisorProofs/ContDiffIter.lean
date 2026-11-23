import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledKoszulTestFamilyHasDerivAtScaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothEventuallyZeroCutoffIntervalIntegralDeriStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugationDerivCutoffPolynomialMemUnitarySpanStatement

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A
open scoped ContDiff

namespace GlobalTheory.PsCo.Pc1.Homot

noncomputable def scF (G : ℝ → ℝ) (j : ℕ) (s y : ℝ) : ℝ := s ^ j * iteratedDeriv (j + 1) G (s * y)

lemma contDiff_iter {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (k : ℕ) : ContDiff ℝ ∞ (iteratedDeriv k G) := by
  rw [iteratedDeriv_eq_iterate]
  exact hG.iterate_deriv k

lemma scF_contDiff {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (j : ℕ) : ContDiff ℝ ∞ (Function.uncurry (scF G j)) := by
  have h := contDiff_iter hG (j + 1)
  exact (contDiff_fst.pow j).mul (h.comp (contDiff_fst.mul contDiff_snd))

lemma deriv_scF {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (j : ℕ) (s y : ℝ) : deriv (scF G j s) y = scF G (j + 1) s y := by
  have h := (contDiff_iter hG (j + 1)).differentiable (by simp)
  have h1 : HasDerivAt (fun y => s * y) s y := by simpa using (hasDerivAt_id y).const_mul s
  have h2 := ((h (s * y)).hasDerivAt.comp y h1).const_mul (s ^ j)
  have h3 : deriv (scF G j s) y = _ := h2.deriv
  rw [h3, scF, iteratedDeriv_succ (n := j + 1)]
  ring

lemma iter_scale {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (j : ℕ) (s y : ℝ) :
    iteratedDeriv (j + 1) (fun y => G (s * y)) y = s * scF G j s y := by
  rw [iteratedDeriv_comp_const_mul (hG.of_le (by exact_mod_cast le_top)) s, scF]
  ring

lemma iter_zero {G : ℝ → ℝ} (h0 : ∀ x, 1 ≤ x → G x = 0) (k : ℕ) {x : ℝ} (hx : 1 < x) : iteratedDeriv k G x = 0 := by
  have : G =ᶠ[nhds x] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy using h0 y (le_of_lt hy)
  rw [this.iteratedDeriv_eq k]
  simp

lemma scF_cont {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (j : ℕ) (y : ℝ) : Continuous fun s => scF G j s y :=
  (scF_contDiff hG j).continuous.comp (continuous_id.prodMk continuous_const)

theorem stHomot : GlobalTheory.PsCo.Pc1.StHomot := by
  intro n ε G p q hP hK t ht
  obtain ⟨hG, h0, -, -⟩ := hP
  have hI : ∀ j, IsCutFn (fun y => ∫ s in (1:ℝ)..t, scF G j s y) ∧
      ∀ y, deriv (fun y => ∫ s in (1:ℝ)..t, scF G j s y) y = ∫ s in (1:ℝ)..t, deriv (scF G j s) y := by
    intro j
    refine GlobalTheory.T.isSmoothEventuallyZeroCutoff_intervalIntegral_deriv (scF G j) 1 t (scF_contDiff hG j) ⟨2, ?_⟩
    intro s hs y hy
    rw [Set.uIcc_of_le ht] at hs
    have : 1 < s * y := by nlinarith [hs.1]
    simp [scF, iter_zero h0 _ this]
  have key : famF ε G p 1 - famF ε G p t = -∑ x : Mode ε, ∑ j ∈ Finset.range (nMode ε + 1),
      adBas ε (Matrix.single x.1.2 x.1.1 1) (fun y => ∫ s in (1:ℝ)..t, scF G j s y) (q x j) := by
    funext g
    set D : ℝ → ℂ := fun s => ∑ x : Mode ε, ∑ j ∈ Finset.range (nMode ε + 1),
      ((scF G (j + 1) s (rM ε g) : ℂ) * ev g (dZ ε (Matrix.single x.1.2 x.1.1 1) (rP ε) * q x j) +
        (scF G j s (rM ε g) : ℂ) * ev g (dZ ε (Matrix.single x.1.2 x.1.1 1) (q x j))) with hD
    have hc : ∀ j, Continuous fun s => (scF G j s (rM ε g) : ℂ) := fun j =>
      Complex.continuous_ofReal.comp (scF_cont hG j _)
    have hder : ∀ s ∈ Set.uIcc (1:ℝ) t, HasDerivAt (fun s : ℝ => famF ε G p s g) (D s) s := by
      intro s hs
      rw [Set.uIcc_of_le ht] at hs
      have hs0 : 0 < s := by linarith [hs.1]
      have h := GlobalTheory.T.scaledKoszulTestFamily_hasDerivAt_scale ε G p q hG hK s hs0 g
      convert h using 1
      rw [hD, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
      simp only [adBas, bas]
      rw [← iteratedDeriv_succ, iter_scale hG, iter_scale hG]
      push_cast
      field_simp
    have hDc : Continuous D := by
      rw [hD]
      refine continuous_finset_sum _ fun x _ => continuous_finset_sum _ fun j _ => ?_
      exact ((hc _).mul continuous_const).add ((hc _).mul continuous_const)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hDc.intervalIntegrable _ _)
    have hint : ∫ s in (1:ℝ)..t, D s = ∑ x : Mode ε, ∑ j ∈ Finset.range (nMode ε + 1),
        adBas ε (Matrix.single x.1.2 x.1.1 1) (fun y => ∫ s in (1:ℝ)..t, scF G j s y) (q x j) g := by
      rw [hD, intervalIntegral.integral_finset_sum]
      · refine Finset.sum_congr rfl fun x _ => ?_
        rw [intervalIntegral.integral_finset_sum]
        · refine Finset.sum_congr rfl fun j _ => ?_
          rw [intervalIntegral.integral_add (((hc _).mul_const _).intervalIntegrable _ _)
            (((hc _).mul_const _).intervalIntegrable _ _),
            intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
            intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
          simp only [adBas, bas, (hI j).2, deriv_scF hG]
        · intro j _
          exact (((hc _).mul continuous_const).add ((hc _).mul continuous_const)).intervalIntegrable _ _
      · intro x _
        refine (continuous_finset_sum _ fun j _ => ?_).intervalIntegrable _ _
        exact ((hc _).mul continuous_const).add ((hc _).mul continuous_const)
    simp only [Pi.sub_apply, Pi.neg_apply, Finset.sum_apply]
    rw [← hint, hftc]
    ring
  rw [key]
  exact neg_mem (Submodule.sum_mem _ fun x _ => Submodule.sum_mem _ fun j _ => GlobalTheory.T.conjugationDerivCutoffPolynomial_mem_unitarySpan ε _ _ _ (hI j).1)

end GlobalTheory.PsCo.Pc1.Homot
