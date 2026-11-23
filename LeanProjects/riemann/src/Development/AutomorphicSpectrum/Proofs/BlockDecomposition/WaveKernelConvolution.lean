import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelCompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqSumOfKernel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralConvApplyEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KRegConv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvRightEquivariant

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem isOpen_GLs_kerconv (n : ℕ) : IsOpen (GLs n) := by
  have hc : Continuous fun g : Mat n => g.det := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage hc

theorem mul_unitary_mem_GLs_kerconv {n : ℕ} {y : Mat n} (hy : y ∈ GLs n)
    (k₂ : Matrix.unitaryGroup (Fin n) ℂ) : y * k₂.1 ∈ GLs n := by
  have h1 : y.det ≠ 0 := hy
  have h2 : (k₂.1 : Mat n).det ≠ 0 := by
    have h3 : (star k₂.1 * k₂.1 : Mat n) = 1 := Unitary.star_mul_self_of_mem k₂.2
    intro h0
    have h4 := congrArg Matrix.det h3
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at h4
    exact zero_ne_one h4
  change (y * k₂.1).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero h1 h2

theorem act_congr_kerconv {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n)
    (k : Mat n → (E.V →L[ℂ] E.V)) {f f' : Mat n → E.V} (h : ∀ x ∈ GLs n, f x = f' x)
    {x : Mat n} (hx : x ∈ GLs n) : act μ E k f x = act μ E k f' x := by
  unfold act
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have hy : (y.val).det ≠ 0 := by
    have := y.isUnit
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero
  have hxy : x * y.val ∈ GLs n := by
    change (x * y.val).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hx hy
  simp only [h _ hxy]

theorem one_mem_GLs_kerconv (n : ℕ) : (1 : Mat n) ∈ GLs n := by
  change (1 : Mat n).det ≠ 0
  simp

theorem conv_eq_of_isKer : LgFacts → Unimod → RCalc → WaveSpeed → WaveEx → KerUniq → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (w w' : List (Bool × ℕ)) (g g' : ℝ → ℝ) (T T' : ℝ) (k k' K : Mat n → (E.V →L[ℂ] E.V)), IsBump g T → IsBump g' T' → IsKer μ E w g k → IsKer μ E w' g' k' → IsKer μ E (w ++ w') (gconv g g') K → ∀ y ∈ GLs n, conv μ E k k' y = K y := by
  intro hLg _ hRC hWS hWE hKU n _ _ μ _ E w w' g g' T T' k k' K hg hg' hk hk' hK y hy
  have rk : KReg k := ⟨hk.1.continuousOn, hk.2.1⟩
  have rk' : KReg k' := ⟨hk'.1.continuousOn, hk'.2.1⟩
  have rK : KReg K := ⟨hK.1.continuousOn, hK.2.1⟩
  have rc : KReg (conv μ E k k') := kReg_conv hLg n μ E k k' rk rk'
  have hk'eq : ∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k' (y * k₂.1) = k' y * E.ρ k₂ := by
    intro y hy k₂
    have := hk'.2.2.1 y hy 1 k₂
    simpa using this
  have hKeq : ∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, K (y * k₂.1) = K y * E.ρ k₂ := by
    intro y hy k₂
    have := hK.2.2.1 y hy 1 k₂
    simpa using this
  have hceq := conv_right_equivariant hLg n μ E k k' rk rk' hk'eq
  have key := hKU n μ E (fun y => conv μ E k k' y - K y) (GLs n) (isOpen_GLs_kerconv n) subset_rfl
    (fun y hy k₂ => mul_unitary_mem_GLs_kerconv hy k₂) (rc.1.sub rK.1)
    (fun y hy k₂ => by
      simp only [hceq y hy k₂, hKeq y hy k₂]
      exact (sub_mul _ _ _).symm)
    (fun f hf hc _ => by
      obtain ⟨u, hu, hu0⟩ := hWE n E f hf
      obtain ⟨v, hv, hv0, hvc⟩ := GlobalTheory.T.wave_kernel_composition hRC hWS n E u w w' g g' T T' hu hg hg'
      have h1 := one_mem_GLs_kerconv n
      have hfc : ContinuousOn f (GLs n) := hf.1.continuousOn
      have hlin := act_eq_sum_of_kernel hLg n μ E (ι := Bool) (fun b => if b then 1 else -1)
        (fun b => if b then conv μ E k k' else K) (fun y => conv μ E k k' y - K y) f
        (fun b => by cases b <;> simp [rc, rK])
        (fun y _ => by simp [Fintype.sum_bool, sub_eq_add_neg]) hfc 1 h1
      have hc1 : act μ E (conv μ E k k') f 1 = act μ E k (act μ E k' f) 1 :=
        act_conv hLg n μ E k k' f rk rk' hfc 1 h1
      have hact' : ∀ x ∈ GLs n, act μ E k' f x = v 0 x := by
        intro x hx
        rw [act_congr_kerconv μ E k' (fun z hz => (hu0 z hz).symm) hx, hk'.2.2.2 u hu x hx, hv0 x hx]
      have hc2 : act μ E k (act μ E k' f) 1 = act μ E K f 1 := by
        rw [act_congr_kerconv μ E k hact' h1, hk.2.2.2 v hv 1 h1, hvc 1 h1,
          ← hK.2.2.2 u hu 1 h1]
        exact act_congr_kerconv μ E K hu0 h1
      rw [hlin]
      simp [Fintype.sum_bool, hc1, hc2]) y hy
  exact sub_eq_zero.1 key

end GlobalTheory.CompanionTheory.WaveMult
