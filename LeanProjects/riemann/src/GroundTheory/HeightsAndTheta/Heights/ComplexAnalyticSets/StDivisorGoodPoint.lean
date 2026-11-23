import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology ComplexSets

noncomputable section

variable {n : ℕ}

def DivisorRegularAt (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (d : ℕ) (q : Fin n → ℂ) : Prop :=
  ∃ (A : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)) (O : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ))
    (g : (Fin d → ℂ) → Fin n → ℂ), IsOpen O ∧ IsOpen V ∧ q ∈ V ∧ AnalyticOnNhd ℂ g O ∧
      (∀ y ∈ O, A (g y) = y) ∧ zeroSet J ∩ {x | linEval u x = 0} ∩ V = g '' O

def NormalDivisorChartAt {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (u : Fin n → ℂ) (d : ℕ) (q : Fin n → ℂ) : Prop :=
  ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q →
    ∃ (r : ℝ) (φ : (Fin (d + 1) → ℂ) → Fin n ⊕ Fin M.m → ℂ) (k : ℕ), 0 < r ∧
      DifferentiableOn ℂ φ (Metric.ball 0 r) ∧ Set.InjOn φ (Metric.ball 0 r) ∧ φ 0 = w ∧
      Set.MapsTo φ (Metric.ball 0 r) (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal) ∧
      (∀ s : ℝ, 0 < s → ∃ U ∈ 𝓝 w, IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ U ⊆ φ '' Metric.ball 0 s) ∧
      VanishesToOrder (fun t => linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords (φ t))) r k ∧
      ∀ v : Fin (d + 1) → ℂ, v 0 = 0 →
        fderiv ℂ (fun t => IndefiniteRowSideFullHecke.ComplexSets.firstCoords (φ t)) 0 v = 0 → v = 0

def NormalDoublePointsOnDivisor {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (u : Fin n → ℂ) (q : Fin n → ℂ) : Prop :=
  ∃ N ∈ 𝓝 q, ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, ∀ w' ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal,
    IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = IndefiniteRowSideFullHecke.ComplexSets.firstCoords w' →
      IndefiniteRowSideFullHecke.ComplexSets.firstCoords w ∈ N → w ≠ w' → linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords w) = 0

theorem eq_const_of_mem_zeroSetIn_lineDiagonal {z : Fin 1 ⊕ Fin 1 → ℂ}
    (hz : z ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn IndefiniteRowSideFullHecke.ComplexSets.lineDiagonalIdeal) :
    z = fun _ => z (Sum.inl 0) := by
  have hzd : z (Sum.inr 0) = z (Sum.inl 0) := by
    have h1 := hz (X (Sum.inr 0) - X (Sum.inl 0)) (by
      show IndefiniteRowSideFullHecke.ComplexSets.lineDiagonalMap (X (Sum.inr 0) - X (Sum.inl 0)) = 0
      rw [IndefiniteRowSideFullHecke.ComplexSets.lineDiagonalMap, map_sub, aeval_X, aeval_X]
      simp)
    simp only [map_sub, eval_X] at h1
    exact sub_eq_zero.mp h1
  funext s
  rcases s with i | i
  · rw [Subsingleton.elim i 0]
  · rw [Subsingleton.elim i 0, hzd]

theorem lineNormalDivisorChartAt :
    NormalDivisorChartAt IndefiniteRowSideFullHecke.ComplexSets.lineDiagonalModel (fun _ => (1 : ℂ)) 0 0 := by
  intro w hw hw0
  have hw' : w = 0 := by
    rw [eq_const_of_mem_zeroSetIn_lineDiagonal hw]
    have h0 : w (Sum.inl 0) = 0 := congrFun hw0 0
    funext _
    exact h0
  subst hw'
  refine ⟨1, fun t _ => t 0, 1, one_pos, Differentiable.differentiableOn (by fun_prop), ?_, rfl,
    fun t _ => IndefiniteRowSideFullHecke.ComplexSets.const_mem_zeroSetIn_lineDiagonal (t 0), ?_, ?_, ?_⟩
  · intro s _ t _ hst
    funext i
    rw [show i = 0 from Fin.ext (by omega)]
    exact congrFun hst (Sum.inl 0)
  · intro s hs
    refine ⟨Metric.ball 0 s, Metric.ball_mem_nhds 0 hs, ?_⟩
    rintro z ⟨hz, hzB⟩
    refine ⟨fun _ => z (Sum.inl 0), ?_, (eq_const_of_mem_zeroSetIn_lineDiagonal hz).symm⟩
    rw [mem_ball_zero_iff] at hzB ⊢
    refine lt_of_le_of_lt ?_ hzB
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro _
    exact norm_le_pi_norm z (Sum.inl 0)
  · refine ⟨fun _ => 1, differentiableOn_const _, fun _ _ => one_ne_zero, fun t _ => ?_⟩
    simp [linEval, IndefiniteRowSideFullHecke.ComplexSets.firstCoords]
  · intro v hv _
    funext i
    rw [show i = 0 from Fin.ext (by omega)]
    exact hv

end

end GroundTheory.Heights₂.Heights
