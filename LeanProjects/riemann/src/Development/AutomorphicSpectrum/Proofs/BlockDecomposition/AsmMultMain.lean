import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BumpConvolutionSupportStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoshTransformConvolutionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoshTransformCasimirRealStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelConvolutionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelWordOrderSwapStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelMultiplierLinearStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelMultiplierOnEigenfunctionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelDecompositionStatement

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem asmMult_main : AsmMult := by
  intro hL hU hR hS hE hQ h1 n _ _ μ _ E k k' val val' T T' hk hk'
  obtain ⟨m, c, w, g, ks, hb, hs, hv⟩ := hk
  obtain ⟨m', c', w', g', ks', hb', hs', hv'⟩ := hk'
  have hreg : ∀ i, KReg (ks i) := fun i => ⟨(hb i).2.1.continuousOn, (hb i).2.2.1⟩
  have hreg' : ∀ i, KReg (ks' i) := fun i => ⟨(hb' i).2.1.continuousOn, (hb' i).2.2.1⟩
  have hbp : ∀ p : Fin m × Fin m', IsBump (gconv (g p.1) (g' p.2)) (T + T') :=
    fun p => GlobalTheory.T.bump_convolution_support _ _ _ _ (hb p.1).1 (hb' p.2).1
  choose K hK using fun p : Fin m × Fin m' => h1 n μ E (w p.1 ++ w' p.2) (gconv (g p.1) (g' p.2)) (T + T') (hbp p)
  have hconv : ∀ y ∈ GLs n, conv μ E k k' y = ∑ p : Fin m × Fin m', (c p.1 * c' p.2) • K p y := by
    intro y hy
    rw [GlobalTheory.T.kernel_multiplier_linear hL n μ E c c' ks ks' k k' hreg hreg' hs hs' y hy, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [GlobalTheory.T.wave_kernel_convolution hL hU hR hS hE hQ n μ E (w i) (w' j) (g i) (g' j) T T' (ks i) (ks' j) (K (i, j))
      (hb i).1 (hb' j).1 (hb i).2 (hb' j).2 (hK (i, j)) y hy]
  have hconv' : ∀ y ∈ GLs n, conv μ E k' k y = ∑ p : Fin m × Fin m', (c p.1 * c' p.2) • K p y := by
    intro y hy
    rw [GlobalTheory.T.kernel_multiplier_linear hL n μ E c' c ks' ks k' k hreg' hreg hs' hs y hy, Finset.sum_comm, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hsw := GlobalTheory.T.wave_kernel_word_order_swap hS hR n μ E (w i) (w' j) _ (T + T') (K (i, j)) (hbp (i, j)) (hK (i, j))
    rw [gconv_comm] at hsw
    rw [GlobalTheory.T.wave_kernel_convolution hL hU hR hS hE hQ n μ E (w' j) (w i) (g' j) (g i) T' T (ks' j) (ks i) (K (i, j))
      (hb' j).1 (hb i).1 (hb' j).2 (hb i).2 hsw y hy, mul_comm]
  refine ⟨?_, fun y hy => by rw [hconv y hy, hconv' y hy], ?_,
    GlobalTheory.T.kernel_multiplier_on_eigenfunction hL n μ E k val T ⟨m, c, w, g, ks, hb, hs, hv⟩⟩
  · refine isMult_of_fintype μ E (fun p : Fin m × Fin m' => c p.1 * c' p.2) (fun p => w p.1 ++ w' p.2)
      (fun p => gconv (g p.1) (g' p.2)) K (fun p => ⟨hbp p, hK p⟩) hconv fun χ => ?_
    rw [Pi.mul_apply, hv χ, hv' χ, Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [zVal_append, ← GlobalTheory.T.cosh_transform_convolution _ _ _ _ _ (hb i).1 (hb' j).1]
    ring
  · haveI := FiniteDimensional.complete ℂ E.V
    choose N d w₁ K₁ hK₁ hadj hval using fun i =>
      GlobalTheory.T.wave_kernel_decomposition hL hU hR hS hE hQ h1 n μ E (w i) (g i) T (ks i) (hb i).1 (hb i).2
    refine ⟨fun χ => ∑ q : (Σ i, Fin (N i)), (conj (c q.1) * d q.1 q.2) * zVal (w₁ q.1 q.2) χ * coshT (g q.1) (cas χ), ?_, ?_⟩
    · refine isMult_of_fintype μ E (fun q : (Σ i, Fin (N i)) => conj (c q.1) * d q.1 q.2) (fun q => w₁ q.1 q.2)
        (fun q => g q.1) (fun q => K₁ q.1 q.2) (fun q => ⟨(hb q.1).1, hK₁ q.1 q.2⟩) (fun y hy => ?_) fun χ => rfl
      rw [hs _ (inv_mem_GLs hy), map_sum, Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := hadj i y hy
      rw [map_smulₛₗ, this, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [smul_smul]
    · intro χ hχ
      rw [hv χ, map_sum]
      beta_reduce
      rw [Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_mul, GlobalTheory.T.cosh_transform_casimir_real n χ (g i) T hχ (hb i).1, hval i χ hχ, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring

end GlobalTheory.CompanionTheory.WaveMult
