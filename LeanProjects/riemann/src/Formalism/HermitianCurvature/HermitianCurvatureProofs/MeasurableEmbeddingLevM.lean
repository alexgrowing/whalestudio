import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousZetaL

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k ρ : ℕ}

def projM (y : Mt k (1 + ρ)) : Mt k ρ := fun a b => y ⟨a.val + 1, by omega⟩ ⟨b.val + 1, by omega⟩

theorem projM_levM (x : Mt k ρ) : projM (B2.levM k ρ x) = x := by
  funext a b
  simp only [projM, B2.levM, ιLev, Matrix.of_apply]
  rw [dif_pos ⟨by omega, by omega⟩, dif_pos ⟨by omega, by omega⟩]
  rfl

theorem continuous_levM : Continuous (B2.levM k ρ) := by
  exact Formalism.FourierDecayAlt.P.LongWeylElement.levM_cont k ρ

theorem continuous_projM : Continuous (projM (k := k) (ρ := ρ)) := by
  unfold projM
  fun_prop

theorem measurableEmbedding_levM : MeasurableEmbedding (B2.levM k ρ) := by
  refine MeasurableEmbedding.of_measurable_inverse continuous_levM.measurable ?_
    continuous_projM.measurable (fun x => projM_levM x)
  have hr : Set.range (B2.levM k ρ) = {y | B2.levM k ρ (projM y) = y} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      simp only [Set.mem_setOf_eq, projM_levM]
    · intro hy
      exact ⟨projM y, hy⟩
  rw [hr]
  exact (isClosed_eq (continuous_levM.comp continuous_projM) continuous_id).measurableSet

theorem zWeight_fin (T T' R : ℝ) :
    ∫⁻ ζ in Metric.closedBall (0 : ℂ) R, ENNReal.ofReal (B2.zWeight k T T' ζ) < ⊤ := by
  have hC : ∀ ζ ∈ Metric.closedBall (0 : ℂ) R,
      ENNReal.ofReal (B2.zWeight k T T' ζ) ≤ ENNReal.ofReal ((R ^ 2 + |T * T'|) ^ (k - 1)) := by
    intro ζ hζ
    apply ENNReal.ofReal_le_ofReal
    have hn : ‖ζ‖ ≤ R := by simpa using hζ
    have hns : Complex.normSq ζ ≤ R ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) hn 2
    simp only [B2.zWeight]
    split_ifs with h
    · apply pow_le_pow_left₀ (by linarith)
      linarith [neg_abs_le (T * T')]
    · positivity
  calc ∫⁻ ζ in Metric.closedBall (0 : ℂ) R, ENNReal.ofReal (B2.zWeight k T T' ζ)
      ≤ ∫⁻ _ in Metric.closedBall (0 : ℂ) R, ENNReal.ofReal ((R ^ 2 + |T * T'|) ^ (k - 1)) :=
        setLIntegral_mono' measurableSet_closedBall hC
    _ = ENNReal.ofReal ((R ^ 2 + |T * T'|) ^ (k - 1)) * MeasureTheory.volume (Metric.closedBall (0 : ℂ) R) :=
        setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top

section pair

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {z z' : Fin (2 * ρ + k + 1) → ℂ} {π : Mx k (1 + ρ) → (Wp →L[ℂ] Wp)} {π' : Mx k (1 + ρ) → (Wq →L[ℂ] Wq)}

theorem pairAt_tr {t : ℂ} (ht : t ≠ 0) {μ : Measure (Mt k (1 + ρ))} {μs : Measure (Mt k ρ)}
    (hmap : μs.map (B2.levM k ρ) = μ) (Φ Ψ : RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')
    (c : Fin ρ → ℂ) :
    P5.pairAt μs (trL ht z z' π π' Φ) (trL ht z z' π π' Ψ) c = P5.pairAt μ Φ Ψ (consC t c) := by
  subst hmap
  simp only [P5.pairAt]
  rw [measurableEmbedding_levM.integral_map]
  rfl

end pair

def RadTransport : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (k ρ : ℕ)
    (z z' : Fin (2 * ρ + k + 1) → ℂ) (π : Mx k (1 + ρ) → (Wp →L[ℂ] Wp)) (π' : Mx k (1 + ρ) → (Wq →L[ℂ] Wq))
    (X : ActualOps k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')
    (Xs : ActualOps k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)))
    (L : R.LevelData (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')) (1 + ρ))
    (st : Fr.Start (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')))
    (Ls : R.LevelData (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)))) ρ)
    (sts : Fr.Start (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)))))
    (s : ℂ) (μ : Measure (Mt k (1 + ρ))) (μs : Measure (Mt k ρ)),
    inWb k ρ z → inWb k ρ z' → IsActualLevel X L → IsActualLevel Xs Ls →
    (∀ Y, st.QQ Y = s • X.QQ Y) → (∀ Y, sts.QQ Y = s • Xs.QQ Y) →
    B.IsHaarOn (Glev k (1 + ρ) (Fin.last (1 + ρ))) μ → B.IsHaarOn (Glev k ρ (Fin.last ρ)) μs →
    (∀ ψ : ℂ → ℝ≥0∞, Measurable ψ →
      ∫⁻ x, ψ (zetaL k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') (Fin.last (1 + ρ)) (Matrix.of x)) ∂μ =
        ∫⁻ ζ, ENNReal.ofReal (B2.zWeight k (Tz k ρ z) (Tz k ρ z') ζ) * ψ ζ) →
    (∀ ψ : ℂ → ℝ≥0∞, Measurable ψ →
      ∫⁻ x, ψ (zetaL k ρ z z' (Fin.last ρ) (Matrix.of x)) ∂μs =
        ∫⁻ ζ, ENNReal.ofReal (B2.zWeight k (Tz k ρ z) (Tz k ρ z') ζ) * ψ ζ) →
    ∀ t : ℂ, t ≠ 0 →
      ∃ T : RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π' →ₗ[ℂ]
          RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)),
        (∀ Φ c g, (T Φ : Fn k ρ (Wq →L[ℂ] Wp)) c g =
          (Φ : Fn k (1 + ρ) (Wq →L[ℂ] Wp)) (consC t c) (ιLev k 1 ρ g)) ∧
        (∀ (Y : ℂ) (a b : Fin 2) Φ,
          ((P5.QQi Ls sts 0 Y) a b).1 (T Φ) = T (((P5.QQi L st 1 Y) a b).1 Φ) ∧
          ((P5.QQi Ls sts 0 Y) a b).2.unop (T Φ) = T (((P5.QQi L st 1 Y) a b).2.unop Φ)) ∧
        ∀ Φ Ψ c, P5.pairAt μs (T Φ) (T Ψ) c = P5.pairAt μ Φ Ψ (consC t c)

end Formalism.FourierDecayAlt.P.PBH

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH

end Formalism.FourierDecayAlt.P
