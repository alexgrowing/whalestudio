import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemContraIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddPowLe

set_option synthInstance.maxSize 1000

noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GroundTheory.Automorphic.GJMatrix GlobalTheory.ThetaPoisson

open scoped Classical

namespace GlobalTheory.SchwartzBruhatMoments

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {m : ℕ}

theorem pInfPi_eq (x : Fin m → Ad E) :
    (fun i => pInf E (x i)) = (toMixedPi E m).symm (infPartPi x) := by
  rw [← toMixedPi_pInf, ContinuousLinearEquiv.symm_apply_apply]

theorem one_add_pow_le {t : ℝ} (ht : 0 ≤ t) (k : ℕ) : (1 + t) ^ k ≤ 2 ^ k * (1 + t ^ k) := by
  first
  | exact @_root_.GlobalTheory.OneAddPowBound.one_add_pow_le
  | exact _root_.GlobalTheory.OneAddPowBound.one_add_pow_le
  | (apply _root_.GlobalTheory.OneAddPowBound.one_add_pow_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.OneAddPowBound.one_add_pow_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OneAddPowBound.one_add_pow_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OneAddPowBound.one_add_pow_le ..)

theorem integrable_arch (φ : SchwartzMap (Fin m → mixedEmbedding.mixedSpace E) ℂ) (k : ℕ) :
    Integrable (fun u => ‖φ u‖ * (1 + ‖(toMixedPi E m).symm u‖) ^ k) (mixedMeasurePi E) := by
  set S := (toMixedPi E m).symm
  set C := ‖(S : (Fin m → mixedEmbedding.mixedSpace E) →L[ℝ] (Fin m → Cinf E))‖
  have hC : 0 ≤ C := norm_nonneg _
  have hint : Integrable (fun u => ((1 + C) ^ k * 2 ^ k) * (‖φ u‖ + ‖u‖ ^ k * ‖φ u‖))
      (mixedMeasurePi E) :=
    ((φ.integrable (μ := mixedMeasurePi E)).norm.add
      (φ.integrable_pow_mul (mixedMeasurePi E) k)).const_mul _
  refine hint.mono' ?_ (Filter.Eventually.of_forall fun u => ?_)
  · exact (φ.continuous.norm.mul ((continuous_const.add S.continuous.norm).pow k)).aestronglyMeasurable
  · have h1 : ‖S u‖ ≤ C * ‖u‖ := (S : (Fin m → mixedEmbedding.mixedSpace E) →L[ℝ] (Fin m → Cinf E)).le_opNorm u
    have h2 : 1 + ‖S u‖ ≤ (1 + C) * (1 + ‖u‖) := by nlinarith [norm_nonneg u, norm_nonneg (S u)]
    have h3 : (1 + ‖S u‖) ^ k ≤ (1 + C) ^ k * (2 ^ k * (1 + ‖u‖ ^ k)) := by
      calc (1 + ‖S u‖) ^ k ≤ ((1 + C) * (1 + ‖u‖)) ^ k := pow_le_pow_left₀ (by positivity) h2 k
        _ = (1 + C) ^ k * (1 + ‖u‖) ^ k := mul_pow _ _ _
        _ ≤ (1 + C) ^ k * (2 ^ k * (1 + ‖u‖ ^ k)) :=
          mul_le_mul_of_nonneg_left (one_add_pow_le (norm_nonneg u) k) (by positivity)
    rw [Real.norm_of_nonneg (by positivity)]
    calc ‖φ u‖ * (1 + ‖S u‖) ^ k ≤ ‖φ u‖ * ((1 + C) ^ k * (2 ^ k * (1 + ‖u‖ ^ k))) :=
          mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      _ = ((1 + C) ^ k * 2 ^ k) * (‖φ u‖ + ‖u‖ ^ k * ‖φ u‖) := by ring

theorem aestronglyMeasurable_weight (k : ℕ) :
    AEStronglyMeasurable (fun x : Fin m → Ad E => (1 + ‖fun i => pInf E (x i)‖) ^ k)
      (adeleMeasurePi E) := by
  have h : (fun x : Fin m → Ad E => (1 + ‖fun i => pInf E (x i)‖) ^ k) =
      (fun p : (Fin m → mixedEmbedding.mixedSpace E) × (Fin m → Af E) =>
        (1 + ‖(toMixedPi E m).symm p.1‖) ^ k) ∘ splitEquivPi E (Fin m) := by
    funext x
    simp only [Function.comp_apply, splitEquivPi_apply]
    rw [pInfPi_eq]
  rw [h]
  exact ((((continuous_const.add (toMixedPi E m).symm.continuous.norm).pow k).measurable.comp
    measurable_fst).comp (splitEquivPi E (Fin m)).measurable).aestronglyMeasurable

theorem integrable_tensor (φ : SchwartzMap (Fin m → mixedEmbedding.mixedSpace E) ℂ)
    {g : (Fin m → Af E) → ℂ} (hg : g ∈ finiteSchwartzBruhatPi E) (k : ℕ) :
    Integrable (fun x => ‖schwartzBruhatTensorPi φ g x‖ * (1 + ‖fun i => pInf E (x i)‖) ^ k)
      (adeleMeasurePi E) := by
  have h : (fun x : Fin m → Ad E => ‖schwartzBruhatTensorPi φ g x‖ * (1 + ‖fun i => pInf E (x i)‖) ^ k) =
      (fun p : (Fin m → mixedEmbedding.mixedSpace E) × (Fin m → Af E) =>
        (‖φ p.1‖ * (1 + ‖(toMixedPi E m).symm p.1‖) ^ k) * ‖g p.2‖) ∘ splitEquivPi E (Fin m) := by
    funext x
    simp only [Function.comp_apply, splitEquivPi_apply, schwartzBruhatTensorPi, norm_mul]
    rw [pInfPi_eq]
    ring
  rw [h, measurePreserving_splitEquivPi.integrable_comp_emb (splitEquivPi E (Fin m)).measurableEmbedding]
  exact (integrable_arch φ k).mul_prod (integrable_of_mem_finiteSchwartzBruhatPi hg).norm

theorem compactSupport_and_integrable_moments :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (F : (Fin m → Ad E) → ℂ),
    F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi E (Fin m) →
    (∃ L : Set (Fin m → Af E), IsCompact L ∧ ∀ x, F x ≠ 0 → (fun i => pFin E (x i)) ∈ L) ∧
    ∀ k : ℕ, Integrable (fun x => ‖F x‖ * (1 + ‖fun i => pInf E (x i)‖) ^ k)
      (GroundTheory.Automorphic.GJMatrix.adeleMeasurePi E) := by
  intro E _ _ _ m F hF
  refine ⟨?_, fun k => ?_⟩
  · induction hF using Submodule.span_induction with
    | mem G hG =>
      obtain ⟨φ, g, hg, rfl⟩ := hG
      refine ⟨tsupport g, hg.2, fun x hx => ?_⟩
      have e : (fun i => pFin E (x i)) = finPartPi x := rfl
      rw [e]
      apply subset_tsupport
      intro h0
      apply hx
      simp only [schwartzBruhatTensorPi, h0, mul_zero]
    | zero => exact ⟨∅, isCompact_empty, fun x hx => absurd rfl hx⟩
    | add G H _ _ hG hH =>
      obtain ⟨L1, h1, hL1⟩ := hG
      obtain ⟨L2, h2, hL2⟩ := hH
      refine ⟨L1 ∪ L2, h1.union h2, fun x hx => ?_⟩
      by_cases hGx : G x = 0
      · right
        apply hL2
        intro hH0
        apply hx
        simp [hGx, hH0]
      · left
        exact hL1 x hGx
    | smul c G _ hG =>
      obtain ⟨L, hL, hLx⟩ := hG
      exact ⟨L, hL, fun x hx => hLx x fun h0 => hx (by simp [h0])⟩
  · induction hF using Submodule.span_induction with
    | mem G hG =>
      obtain ⟨φ, g, hg, rfl⟩ := hG
      exact integrable_tensor φ hg k
    | zero => simp
    | add G H hGm hHm hG hH =>
      refine (hG.add hH).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
      · exact (integrable_of_mem_schwartzBruhatPi (K := E) (ι := Fin m)
          (Submodule.add_mem _ hGm hHm)).aestronglyMeasurable.norm.mul (aestronglyMeasurable_weight k)
      · have hw : 0 ≤ (1 + ‖fun i => pInf E (x i)‖) ^ k := by positivity
        simp only [Pi.add_apply]
        rw [Real.norm_of_nonneg (by positivity), ← add_mul]
        exact mul_le_mul_of_nonneg_right (norm_add_le _ _) hw
    | smul c G _ hG =>
      refine (hG.const_mul ‖c‖).congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
      ring

end GlobalTheory.SchwartzBruhatMoments
