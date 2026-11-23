import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BumpConvolutionSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyEqOfAgreeGLs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZOpSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterOperatorPreservesWave
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveTimeAverageIsWave
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterOperatorCommutesIntegral

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem integral_smul_integral_shift {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [CompleteSpace V] {g g' : ℝ → ℝ} {T T' : ℝ} (hg : IsBump g T) (hg' : IsBump g' T')
    {φ : ℝ → V} (hφ : Continuous φ) :
    ∫ t, (g t : ℂ) • ∫ s, (g' s : ℂ) • φ (t + s) = ∫ r, (gconv g g' r : ℂ) • φ r := by
  have cg : Continuous g := hg.1.continuous
  have cg' : Continuous g' := hg'.1.continuous
  let F : ℝ → ℝ → V := fun t r => ((g t * g' (r - t) : ℝ) : ℂ) • φ r
  have hFc : Continuous (Function.uncurry F) := by
    have : Function.uncurry F = fun p : ℝ × ℝ => ((g p.1 * g' (p.2 - p.1) : ℝ) : ℂ) • φ p.2 := rfl
    rw [this]
    fun_prop
  have hFs : HasCompactSupport (Function.uncurry F) := by
    refine HasCompactSupport.intro
      (K := Set.Icc (-|T|) |T| ×ˢ Set.Icc (-(|T| + |T'|)) (|T| + |T'|))
      (isCompact_Icc.prod isCompact_Icc) ?_
    rintro ⟨t, r⟩ h
    by_cases ht : T < |t|
    · simp [Function.uncurry, F, hg.2.2 t ht]
    · by_cases hr : T' < |r - t|
      · simp [Function.uncurry, F, hg'.2.2 _ hr]
      · exfalso
        apply h
        have h1 : |t| ≤ |T| := (not_lt.mp ht).trans (le_abs_self T)
        have h2 : |r - t| ≤ |T'| := (not_lt.mp hr).trans (le_abs_self T')
        have h3 : |r| ≤ |t| + |r - t| := by simpa using abs_add_le t (r - t)
        exact ⟨abs_le.mp h1, abs_le.mp (by linarith)⟩
  have hFi : Integrable (Function.uncurry F) (volume.prod volume) :=
    hFc.integrable_of_hasCompactSupport hFs
  have hL : ∀ t, (g t : ℂ) • ∫ s, (g' s : ℂ) • φ (t + s) = ∫ r, F t r := by
    intro t
    rw [← integral_add_left_eq_self (fun r => F t r) t, ← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [F, add_sub_cancel_left, Complex.ofReal_mul, mul_smul]
  have hR : ∀ r, (gconv g g' r : ℂ) • φ r = ∫ t, F t r := by
    intro r
    simp only [F, gconv]
    rw [integral_smul_const, integral_complex_ofReal]
  simp only [hL, hR]
  exact integral_integral_swap hFi

theorem wave_compose : RCalc → WaveSpeed → ∀ (n : ℕ) (E : KMod n) (u : ℝ → Mat n → E.V)
    (w w' : List (Bool × ℕ)) (g g' : ℝ → ℝ) (T T' : ℝ), IsWave E u → IsBump g T → IsBump g' T' →
    ∃ v : ℝ → Mat n → E.V, IsWave E v ∧
      (∀ x ∈ GLs n, v 0 x = zOp w' (fun x' => ∫ t, (g' t : ℂ) • u t x') x) ∧
      ∀ x ∈ GLs n, zOp w (fun x' => ∫ t, (g t : ℂ) • v t x') x =
        zOp (w ++ w') (fun x' => ∫ t, (gconv g g' t : ℂ) • u t x') x := by
  intro hR hS n E u w w' g g' T T' hu hg hg'
  have : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V
  have hu' : IsWave E (fun t => zOp w' (u t)) := WaveZ.isWave_zOp hR n E u w' hu
  have hv := WaveAvg.isWave_avg hS n E (fun t => zOp w' (u t)) g' T' hu' hg'
  refine ⟨_, hv, ?_, ?_⟩
  · intro x hx
    have h := ZOpAvg.zOp_avg n u g' T' w' hu.1 hg' x hx
    simp only [zero_add]
    exact h.symm
  · intro x hx
    have hb := isBump_gconv g g' T T' hg hg'
    have hφ : ∀ x' ∈ GLs n, Continuous fun r => zOp w' (u r) x' := fun x' hx' =>
      hu'.1.continuousOn.comp_continuous (f := fun r : ℝ => (r, x')) (by fun_prop)
        (fun r => ⟨trivial, hx'⟩)
    have h1 : ∀ x' ∈ GLs n, (∫ t, (g t : ℂ) • ∫ s, (g' s : ℂ) • zOp w' (u (t + s)) x') =
        ∫ r, (gconv g g' r : ℂ) • zOp w' (u r) x' := fun x' hx' =>
      integral_smul_integral_shift hg hg' (hφ x' hx')
    rw [zOp_agree_GLs n w _ _ h1 x hx,
      ZOpAvg.zOp_avg n (fun t => zOp w' (u t)) (gconv g g') (T + T') w hu'.1 hb x hx,
      ZOpAvg.zOp_avg n u (gconv g g') (T + T') (w ++ w') hu.1 hb x hx]
    simp only [Swap.zOp_append]

end GlobalTheory.CompanionTheory.WaveMult
