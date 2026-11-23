import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.EisensteinMeromorphy.DiffContOfReg
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.EisensteinMeromorphy.HgtMulRight
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.EisensteinMeromorphy.MeromorphicOnOfWeak
import Development.WeilBound.ThetaLifts.LatticeBasics.EisCont
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHeckeFunctionalStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.SiegelWeilFormula
open GlobalTheory.Cont

namespace PositivityTheory.SiegelWeilFormula.Khead

private theorem isPreconnected_of_rightOf_subset_of_shift {U : Set ℂ} (σ₀ : ℝ) (hσ₀ : GlobalTheory.Cont.rightOf σ₀ ⊆ U)
    (hshift : ∀ s ∈ U, ∀ t : ℝ, 0 ≤ t → s + t ∈ U) : IsPreconnected U := by
  refine isPreconnected_of_forall ((σ₀ + 1 : ℝ) : ℂ) fun y hy => ?_
  obtain ⟨T, hT0, hT⟩ : ∃ T : ℝ, 0 ≤ T ∧ σ₀ < y.re + T :=
    ⟨|σ₀ - y.re| + 1, by positivity, by linarith [le_abs_self (σ₀ - y.re)]⟩
  have hA : y + (T : ℂ) ∈ {c : ℂ | σ₀ < c.re} := by
    show σ₀ < (y + (T : ℂ)).re
    rw [Complex.add_re, Complex.ofReal_re]
    exact hT
  have hB : ((σ₀ + 1 : ℝ) : ℂ) ∈ {c : ℂ | σ₀ < c.re} := by
    show σ₀ < (((σ₀ + 1 : ℝ) : ℂ)).re
    rw [Complex.ofReal_re]
    linarith
  refine ⟨segment ℝ y (y + T) ∪ segment ℝ (y + T) ((σ₀ + 1 : ℝ) : ℂ), ?_,
    Or.inr (right_mem_segment ℝ _ _), Or.inl (left_mem_segment ℝ _ _), ?_⟩
  · rintro w (hw | hw)
    · rw [segment_eq_image'] at hw
      obtain ⟨θ, hθ, rfl⟩ := hw
      have e : y + θ • (y + (T : ℂ) - y) = y + ((θ * T : ℝ) : ℂ) := by
        rw [add_sub_cancel_left, Complex.real_smul, Complex.ofReal_mul]
      show y + θ • (y + (T : ℂ) - y) ∈ U
      rw [e]
      exact hshift y hy _ (mul_nonneg hθ.1 hT0)
    · exact hσ₀ ((convex_halfSpace_re_gt σ₀).segment_subset hA hB hw)
  · exact IsPreconnected.union (y + (T : ℂ)) (right_mem_segment ℝ _ _) (left_mem_segment ℝ _ _)
      (convex_segment _ _).isPreconnected (convex_segment _ _).isPreconnected

theorem eisStrong_of : EisBL → EisStrong := by
  intro hBL F E _ _ _ _ _ σ d hS s₁ f hf
  obtain ⟨r', s', hY⟩ := hS
  obtain ⟨Ê, ⟨t, hsum, hdiff⟩, hweak⟩ := hBL F E σ d.B d.n d.Y r' s' d.ok.good d.ok.hn hY d.χ
    d.ok.hecke d.m d.ok.res d.b d.K d.a d.ok.frame d.ok.stdK d.ok.hgt s₁ f hf
  have h1 : ∀ x : G2 σ d.Y, (1 : ℝ) ≤ (ht2 x : ℝ) := one_le_height_GL2
  have hp : ∀ s₀ : ℂ, ∃ (k : ℕ) (H : ℂ → G2 σ d.Y → ℂ),
      An.Reg (fun x : G2 σ d.Y => (ht2 x : ℝ)) H s₀ ∧
      ∀ᶠ s in 𝓝[≠] s₀, ∀ x, H s x = (s - s₀) ^ k * Ê s x := by
    intro s₀
    obtain ⟨k, U, H, hU, hH, hμ⟩ := hweak s₀
    refine ⟨k, fun s => (H s).1, reg_of_weak hU hμ, ?_⟩
    filter_upwards [nhdsWithin_le_nhds hU, self_mem_nhdsWithin] with s hsU hsne
    exact hH s hsU hsne
  have hr : ∀ s : ℂ, t < s.re → An.Reg (fun x : G2 σ d.Y => (ht2 x : ℝ)) Ê s := by
    intro s hs
    obtain ⟨k, H, hreg, he⟩ := hp s
    exact hreg.remove h1 he ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs) hdiff
  have hinv := GlobalTheory.T.eisenstein_hecke_functional F E σ d.B d.n d.Y r' s' d.ok.good d.ok.hn hY d.b d.K d.a d.ok.frame
    d.ok.stdK d.ok.hgt d.χ s₁ f hf d.ok.hecke t Ê hsum
  obtain ⟨t', hmaj⟩ := majorant d ⟨r', s', hY⟩ hf
  intro s₀
  obtain ⟨U, p, G, hUo, hUr, hs₀, hp0, hreg, hGE⟩ := strip h1 hp hr s₀
  obtain ⟨hGd, hGc⟩ := diff_cont_of_reg hreg
  refine ⟨U, p, G, max t t', hUo, hUr, hs₀, hp0, hGd, hGc, ?_, ?_⟩
  · intro z hz γ hγ g
    obtain ⟨⟨σ₀, hσ₀⟩, hshift⟩ := hUr
    obtain ⟨R, hR⟩ : ∃ R : ℝ, R = max σ₀ t + 1 := ⟨_, rfl⟩
    have hz₀ : (R : ℂ) ∈ U := hσ₀ (show σ₀ < ((R : ℂ)).re by
      rw [Complex.ofReal_re]; linarith [le_max_left σ₀ t])
    have hev : (fun w => G w (γ * g)) =ᶠ[𝓝 (R : ℂ)] (fun w => G w g) := by
      have hopen : {w : ℂ | t < w.re} ∈ 𝓝 (R : ℂ) :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (show t < ((R : ℂ)).re by
          rw [Complex.ofReal_re]; linarith [le_max_right σ₀ t])
      filter_upwards [hopen] with w hw
      rw [hGE w hw, hGE w hw, hinv w hw γ hγ g]
    exact ((hGd (γ * g)).analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
      ((hGd g).analyticOnNhd hUo) (isPreconnected_of_rightOf_subset_of_shift σ₀ hσ₀ hshift) hz₀ hev hz
  · intro z hz
    have hzt : t < z.re := lt_of_le_of_lt (le_max_left _ _) hz
    refine ⟨hmaj z (lt_of_le_of_lt (le_max_right _ _) hz), fun g => ?_⟩
    rw [hGE z hzt g]
    congr 1
    rw [← (hsum z hzt g).tsum_eq]
    unfold PositivityTheory.SiegelWeilFormula.SD.eis GlobalTheory.Eis.cosetSum
    congr 1
    funext q
    simp only [GlobalTheory.Eis.term, eisTerm, flat, PositivityTheory.SiegelWeilFormula.SD.Ht, Real.coe_toNNReal _ (hgt_nonneg d.ok.hgt _)]

end PositivityTheory.SiegelWeilFormula.Khead
