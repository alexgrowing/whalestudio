import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KFiniteSmoothVectors.UnitaryModelOfMultiplicityGardingDensity

open MeasureTheory Matrix Topology Set Metric
open scoped InnerProductSpace ContDiff

noncomputable section

namespace PI.KFinSmoothW

open PI.UpqRep

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Gard

def mMeas (n : ℕ) : MeasurableSpace (Matrix (Fin n) (Fin n) ℂ) := borel _

attribute [local instance] mMeas

lemma mBorel (n : ℕ) : BorelSpace (Matrix (Fin n) (Fin n) ℂ) := by
  exact ⟨rfl⟩

attribute [local instance] mBorel

lemma mBorelN (n : ℕ) : @BorelSpace (Matrix (Fin n) (Fin n) ℂ)
    (@UniformSpace.toTopologicalSpace _ (@PseudoMetricSpace.toUniformSpace _
      (@SeminormedAddCommGroup.toPseudoMetricSpace _
        (@NormedAddCommGroup.toSeminormedAddCommGroup _ Matrix.normedAddCommGroup)))) (mMeas n) := by
  exact ⟨rfl⟩

attribute [local instance] mBorelN

lemma mLocCpt (n : ℕ) : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) := by
  exact inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))

attribute [local instance] mLocCpt

section Calc

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} {N : WithTop ℕ∞}

lemma contDiff_mat_iff {f : E → Matrix (Fin n) (Fin n) ℂ} :
    ContDiff ℝ N f ↔ ∀ i j, ContDiff ℝ N (fun x => f x i j) := by
  exact contDiff_pi.trans (forall_congr' fun i => contDiff_pi)

lemma contDiff_mat_mul {f g : E → Matrix (Fin n) (Fin n) ℂ} (hf : ContDiff ℝ N f)
    (hg : ContDiff ℝ N g) : ContDiff ℝ N (fun x => f x * g x) := by
  rw [contDiff_mat_iff] at hf hg ⊢
  intro i j
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun k _ => (hf i k).mul (hg k j)

lemma contDiff_mat_conjT {f : E → Matrix (Fin n) (Fin n) ℂ} (hf : ContDiff ℝ N f) :
    ContDiff ℝ N (fun x => (f x)ᴴ) := by
  rw [contDiff_mat_iff] at hf ⊢
  intro i j
  simp only [Matrix.conjTranspose_apply]
  exact Complex.conjCLE.contDiff.comp (hf j i)

end Calc

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

lemma umat_closedEmb (ε : Fin n → Bool) :
    IsClosedEmbedding (umat : UJ ε → Matrix (Fin n) (Fin n) ℂ) := by
  exact ⟨⟨isInducing_coeMatrix ε, injective_coeMatrix ε⟩, (range_coeMatrix ε) ▸ isClosed_pseudoUnitary ε⟩

lemma umat_measEmb (ε : Fin n → Bool) :
    MeasurableEmbedding (umat : UJ ε → Matrix (Fin n) (Fin n) ℂ) := by
  exact (umat_closedEmb ε).measurableEmbedding

lemma umat_mem (h : UJ ε) : umat h ∈ UJset ε := by
  exact h.2

lemma umat_inv (γ : UJ ε) : umat γ⁻¹ = Jm ε * (umat γ)ᴴ * Jm ε := by
  exact coeMatrix_inv_eq ε γ

lemma umat_mul_inv (γ : UJ ε) : umat γ * umat γ⁻¹ = 1 := by
  exact Units.mul_inv (γ : (Matrix (Fin n) (Fin n) ℂ)ˣ)

lemma cont_orbit {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hτ : IsURepOn (UJset ε) τ) (x : H) :
    Continuous (fun h : UJ ε => τ (umat h) x) := by
  exact (hτ.2.2 x).comp_continuous (continuous_coeMatrix ε) (fun h => umat_mem h)

lemma integrable_orbit {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hτ : IsURepOn (UJset ε) τ)
    (Ψ : UJ ε → ℂ) (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ) (x : H) :
    Integrable (fun h => Ψ h • τ (umat h) x) (muG ε) := by
  exact (hΨ.smul (cont_orbit hτ x)).integrable_of_hasCompactSupport hΨc.smul_right

lemma tau_gv {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hτ : IsURepOn (UJset ε) τ)
    (Φ : Matrix (Fin n) (Fin n) ℂ → ℂ) (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) (x : H)
    (γ : UJ ε) :
    τ (umat γ) (gv ε τ Φ x) =
      ∫ h, Φ (Jm ε * (umat γ)ᴴ * Jm ε * umat h) • τ (umat h) x ∂(muG ε) := by
  have hint := integrable_orbit hτ (fun h => Φ (umat h)) (hΦ.comp (continuous_coeMatrix ε))
    (hΦc.comp_isClosedEmbedding (umat_closedEmb ε)) x
  rw [gv, ← (τ (umat γ)).integral_comp_comm hint]
  have key := integral_mul_left_eq_self (μ := muG ε)
    (fun h' => Φ (Jm ε * (umat γ)ᴴ * Jm ε * umat h') • τ (umat h') x) γ
  beta_reduce at key
  rw [← key]
  congr 1
  funext h
  rw [show umat (γ * h) = umat γ * umat h from rfl, ← Matrix.mul_assoc,
    coeMatrix_left_inv ε _ (umat_mem γ), Matrix.one_mul, hτ.1.2 _ (umat_mem γ) _ (umat_mem h), map_smul]
  rfl

def Lsm (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] : H →L[ℝ] ℂ →L[ℝ] H :=
  (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] H →L[ℝ] H).flip

lemma Lsm_apply (v : H) (c : ℂ) : Lsm H v c = c • v := rfl

lemma locInt {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hτ : IsURepOn (UJset ε) τ) (x : H) :
    LocallyIntegrable (fun t => τ t x) (Measure.map umat (muG ε)) := by
  rw [MeasureTheory.locallyIntegrable_iff]
  intro K hK
  rw [(umat_measEmb ε).integrableOn_map_iff]
  exact (cont_orbit hτ x).continuousOn.integrableOn_compact ((umat_closedEmb ε).isCompact_preimage hK)

private theorem matrix_norm_mul_le_card_mul {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) :
    ‖A * B‖ ≤ m * ‖A‖ * ‖B‖ := by
  have h0 : 0 ≤ (m : ℝ) * ‖A‖ * ‖B‖ := by positivity
  rw [Matrix.norm_le_iff h0]
  intro i j
  rw [Matrix.mul_apply]
  calc ‖∑ k, A i k * B k j‖ ≤ ∑ k, ‖A i k * B k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin m, ‖A‖ * ‖B‖ := Finset.sum_le_sum fun k _ => by
        rw [norm_mul]
        exact mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm A)
          (Matrix.norm_entry_le_entrywise_sup_norm B) (norm_nonneg _) (norm_nonneg _)
    _ = m * ‖A‖ * ‖B‖ := by simp [mul_assoc]

theorem stepGarding_main : StepGarding := by
  intro n ε H _ _ _ τ hτ Φ hΦ hΦc x
  unfold SmoothJ SmoothOnH
  intro g₀ hg₀
  have hl : (Jm ε * g₀ᴴ * Jm ε) * g₀ = 1 := coeMatrix_left_inv ε g₀ hg₀
  have hr : g₀ * (Jm ε * g₀ᴴ * Jm ε) = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp hl
  set A : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ := fun p => Jm ε * pᴴ * Jm ε with hA
  have hAc : ContDiff ℝ ∞ A :=
    contDiff_mat_mul (contDiff_mat_mul contDiff_const (contDiff_mat_conjT contDiff_id)) contDiff_const

  obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 < R ∧ tsupport Φ ⊆ Metric.closedBall 0 R := by
    obtain ⟨R, hR⟩ := hΦc.isCompact.isBounded.subset_closedBall 0
    exact ⟨max R 1, by positivity,
      hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))⟩
  set c : ℝ := (n : ℝ) * ‖g₀‖ with hc
  have hc0 : 0 ≤ c := by positivity
  set U : Set (Matrix (Fin n) (Fin n) ℂ) := {p | (n : ℝ) * c * ‖A p - A g₀‖ < 1 / 2} with hU
  have hUo : IsOpen U :=
    isOpen_lt (continuous_const.mul ((hAc.continuous.sub continuous_const).norm)) continuous_const
  have hg₀U : g₀ ∈ U := by
    show (n : ℝ) * c * ‖A g₀ - A g₀‖ < 1 / 2
    simp

  have hk : ∀ p ∈ U, ∀ y, Φ (A p * (-y)) ≠ 0 → ‖y‖ ≤ 2 * c * R := by
    intro p hp y hy
    have hp' : (n : ℝ) * c * ‖A p - A g₀‖ < 1 / 2 := hp
    have hz : ‖A p * (-y)‖ ≤ R := by
      have h0 := hR (subset_tsupport _ hy)
      simpa using h0
    have h1 : -y = g₀ * (A g₀ * (-y)) := by
      rw [← Matrix.mul_assoc, hr, Matrix.one_mul]
    have h2 : A g₀ * (-y) = A p * (-y) - (A p - A g₀) * (-y) := by
      rw [Matrix.sub_mul]
      abel
    have e1 := matrix_norm_mul_le_card_mul g₀ (A g₀ * (-y))
    have e2 := matrix_norm_mul_le_card_mul (A p - A g₀) (-y)
    rw [← h1, norm_neg] at e1
    rw [norm_neg] at e2
    have e3 : ‖A g₀ * (-y)‖ ≤ ‖A p * (-y)‖ + ‖(A p - A g₀) * (-y)‖ := by
      rw [h2]
      exact norm_sub_le _ _
    have e4 : ‖A g₀ * (-y)‖ ≤ R + n * ‖A p - A g₀‖ * ‖y‖ := by linarith
    have e5 : ‖y‖ ≤ c * (R + n * ‖A p - A g₀‖ * ‖y‖) := by
      calc ‖y‖ ≤ n * ‖g₀‖ * ‖A g₀ * (-y)‖ := e1
        _ ≤ c * (R + n * ‖A p - A g₀‖ * ‖y‖) := by
          rw [hc]
          exact mul_le_mul_of_nonneg_left e4 (by positivity)
    have e6 : c * (n * ‖A p - A g₀‖ * ‖y‖) ≤ 1 / 2 * ‖y‖ := by
      have h3 := mul_le_mul_of_nonneg_right hp'.le (norm_nonneg y)
      linarith
    linarith
  have hgs : ∀ (p y : Matrix (Fin n) (Fin n) ℂ), p ∈ U → y ∉ Metric.closedBall 0 (2 * c * R) →
      Φ (A p * (-y)) = 0 := by
    intro p y hp hy
    by_contra h
    exact hy (mem_closedBall_zero_iff.mpr (hk p hp y h))
  have hGs : ContDiff ℝ ∞ (fun q : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ =>
      Φ (A q.1 * (-q.2))) :=
    hΦ.comp (contDiff_mat_mul (hAc.comp contDiff_fst) contDiff_snd.neg)
  have hconv := MeasureTheory.contDiffOn_convolution_right_with_param (𝕜 := ℝ)
    (μ := Measure.map umat (muG ε)) (f := fun t => τ t x) (n := ⊤) (Lsm H)
    (g := fun p y => Φ (A p * (-y))) hUo (isCompact_closedBall 0 (2 * c * R)) hgs (locInt hτ x)
    hGs.contDiffOn
  refine ⟨U, fun p => MeasureTheory.convolution (fun t => τ t x) (fun y => Φ (A p * (-y))) (Lsm H)
    (Measure.map umat (muG ε)) 0, hUo, hg₀U, ?_, ?_⟩
  · have h2 : ContDiffOn ℝ ∞ (fun p : Matrix (Fin n) (Fin n) ℂ => (p, (0 : Matrix (Fin n) (Fin n) ℂ))) U :=
      contDiffOn_id.prodMk contDiffOn_const
    have h4 : Set.MapsTo (fun p : Matrix (Fin n) (Fin n) ℂ => (p, (0 : Matrix (Fin n) (Fin n) ℂ))) U
        (U ×ˢ Set.univ) := fun p hp => ⟨hp, Set.mem_univ _⟩
    have h5 := ContDiffOn.comp hconv h2 h4
    exact h5
  · intro g _ hg
    have hgl : (Jm ε * gᴴ * Jm ε) * g = 1 := coeMatrix_left_inv ε g hg
    have hgr : g * (Jm ε * gᴴ * Jm ε) = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp hgl
    let u : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨g, Jm ε * gᴴ * Jm ε, hgr, hgl⟩
    let γ : UJ ε := ⟨u, hg⟩
    have hγ : umat γ = g := rfl
    beta_reduce
    rw [← hγ, tau_gv hτ Φ hΦ.continuous hΦc x γ, hγ, MeasureTheory.convolution_def,
      (umat_measEmb ε).integral_map]
    congr 1
    funext h
    rw [Lsm_apply, zero_sub, neg_neg]

end Gard

theorem garding_vectors_smooth : StepGarding := by
  exact Gard.stepGarding_main

end PI.KFinSmoothW
