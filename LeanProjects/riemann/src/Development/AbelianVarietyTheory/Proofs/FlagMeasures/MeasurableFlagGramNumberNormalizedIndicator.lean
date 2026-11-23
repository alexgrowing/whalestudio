import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoSidedSizeFunctionPosInvariantContinuous
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableStarProjectionKerMatrix

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.YMeas

theorem exists_matrix_ker {n : ℕ} (Q : Submodule ℂ (Fin n → ℂ)) :
    ∃ M : Matrix (Fin n) (Fin n) ℂ, ∀ v, M *ᵥ v = 0 ↔ v ∈ Q := by
  obtain ⟨P, hP⟩ := Q.exists_isCompl
  refine ⟨LinearMap.toMatrix' (P.subtype ∘ₗ P.projectionOnto Q hP.symm), fun v => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  simp

theorem measurable_proj {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (Q : Submodule ℂ (Fin n → ℂ)) (g : X → Matrix (Fin n) (Fin n) ℂ)
    (v : X → EuclideanSpace ℂ (Fin n)) (hg : Continuous g) (hv : Continuous v) :
    Measurable fun x => ((LinearMap.ker (Matrix.toLin' A) ⊓ Q.comap (Matrix.toLin' (g x))).comap
      (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).toLinearMap).starProjection (v x) := by
  obtain ⟨M, hM⟩ := exists_matrix_ker Q
  let Φ : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ →ₗ[ℂ]
      (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n ⊕ Fin n)) :=
    (LinearMap.toContinuousLinearMap.toLinearMap).comp Matrix.toEuclideanLin.toLinearMap
  have hΦ : Continuous Φ := Φ.continuous_of_finiteDimensional
  have hMg : Continuous fun x => M * g x := continuous_const.matrix_mul hg
  have hL : Continuous fun x => Matrix.fromRows A (M * g x) := by
    refine continuous_matrix fun i j => ?_
    rcases i with i | i
    · simpa using continuous_const
    · simpa using hMg.matrix_elem i j
  have h := GlobalTheory.measurable_starProjection_ker_clm (fun x => Φ (Matrix.fromRows A (M * g x))) v (hΦ.comp hL) hv
  have e : ∀ x, ((LinearMap.ker (Matrix.toLin' A) ⊓ Q.comap (Matrix.toLin' (g x))).comap
      (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).toLinearMap) =
      LinearMap.ker (Φ (Matrix.fromRows A (M * g x)) :
        EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n ⊕ Fin n)) := by
    intro x
    ext p
    have h1 : Φ (Matrix.fromRows A (M * g x)) p =
        WithLp.toLp 2 (Matrix.fromRows A (M * g x) *ᵥ p.ofLp) := rfl
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, h1, WithLp.toLp_eq_zero, Matrix.fromRows_mulVec,
      ← Matrix.mulVec_mulVec]
    simp only [Submodule.mem_comap, Submodule.mem_inf, LinearMap.mem_ker, Matrix.toLin'_apply, ← hM]
    constructor
    · rintro ⟨h2, h3⟩
      funext i
      rcases i with i | i
      · exact congrFun h2 i
      · exact congrFun h3 i
    · intro h2
      exact ⟨funext fun i => congrFun h2 (Sum.inl i), funext fun i => congrFun h2 (Sum.inr i)⟩
  simp only [e]
  exact h

theorem measurableSet_GG (k r : ℕ) : MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r} := by
  refine IsClosed.measurableSet ?_
  have hc : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) := continuous_id
  exact isClosed_eq ((hc.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hc) continuous_const

theorem measurable_gramProj (k r j : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r)
    (w : Fin j → Fin (2 * r + k + 1) → ℂ) :
    Measurable fun x : {x : Mt k r | Matrix.of x ∈ GG k r} =>
      gramProj (Ppos k r z z' γ (Matrix.of x.1)) (fun a : Fin j => (Matrix.of x.1 : Mat k r)⁻¹ *ᵥ w a) := by
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  have hc : Continuous fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => (Matrix.of x.1 : Mat k r) :=
    continuous_subtype_val
  have hinv : Continuous fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => (Matrix.of x.1 : Mat k r)⁻¹ := by
    rw [continuous_iff_continuousAt]
    intro x
    have hx : IsUnit (Matrix.of x.1 : Mat k r).det := ((uHGroup _ _ hH).2.2 _ x.2).1
    have h1 : ContinuousAt (Inv.inv : Mat k r → _) (Matrix.of x.1) := by
      refine continuousAt_matrix_inv _ ?_
      obtain ⟨u, hu⟩ := hx
      rw [← hu]
      exact NormedRing.inverse_continuousAt u
    exact ContinuousAt.comp (f := fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => (Matrix.of x.1 : Mat k r))
      h1 hc.continuousAt
  have hp : ∀ a : Fin j, Measurable fun x : {x : Mt k r | Matrix.of x ∈ GG k r} =>
      (Ppos k r z z' γ (Matrix.of x.1)).starProjection
        (WithLp.toLp 2 ((Matrix.of x.1 : Mat k r)⁻¹ *ᵥ w a)) := fun a =>
    measurable_proj (Hpk k r - 1) (Hcom k r z z' γ ⊔ Xsp k r) _ _ hc
      ((PiLp.continuous_toLp 2 _).comp (hinv.matrix_mulVec continuous_const))
  have hG : Continuous fun u : Fin j → EuclideanSpace ℂ (Fin (2 * r + k + 1)) =>
      Real.sqrt ‖(Matrix.gram ℂ u).det‖ := by
    refine Real.continuous_sqrt.comp (continuous_norm.comp (Continuous.matrix_det ?_))
    refine continuous_matrix fun a b => ?_
    simp only [Matrix.gram_apply]
    exact (continuous_apply a).inner (continuous_apply b)
  exact hG.measurable.comp (measurable_pi_lambda _ hp)

theorem yj_measurable : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ γ : Mat k r, inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → γ ∈ GG k r → Measurable (Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r} fun x => Yj k r hj z z' γ (Matrix.of x)) ∧ ∀ R₀ y : ℝ, MeasurableSet (Eset0 k r hj z z' γ R₀ y) := by
  intro k r j hj z z' γ hz hz' hT hT' hγ
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  have hS := measurableSet_GG k r
  have hY : Measurable fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => Yj k r hj z z' γ (Matrix.of x.1) :=
    (measurable_gramProj k r j z z' γ _).div_const _
  have hc : Continuous fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => (Matrix.of x.1 : Mat k r) :=
    continuous_subtype_val
  have h1 : Continuous fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => Sg2 k r z' (Matrix.of x.1) :=
    (TwoSided.Sg2_invariant_continuousOn_one_le_bounds k r z' hz' hT').2.2.1.comp_continuous hc fun x => x.2
  have h2 : Continuous fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => Sg2 k r z (γ * Matrix.of x.1) :=
    (TwoSided.Sg2_invariant_continuousOn_one_le_bounds k r z hz hT).2.2.1.comp_continuous (continuous_const.matrix_mul hc)
      fun x => (uHGroup _ _ hH).2.1 _ hγ _ x.2
  refine ⟨?_, fun R₀ y => ?_⟩
  · refine measurable_of_restrict_of_restrict_compl hS ?_ ?_
    · convert hY using 1
      funext x
      exact Set.indicator_of_mem x.2 _
    · convert (measurable_const (a := (0 : ℝ))) using 1
      funext x
      exact Set.indicator_of_notMem x.2 _
  have e : Eset0 k r hj z z' γ R₀ y = Subtype.val '' {x : {x : Mt k r | Matrix.of x ∈ GG k r} |
      Sg2 k r z' (Matrix.of x.1) ≤ R₀ ∧ Sg2 k r z (γ * Matrix.of x.1) ≤ R₀ ∧
        y < Yj k r hj z z' γ (Matrix.of x.1) ∧ Yj k r hj z z' γ (Matrix.of x.1) ≤ 2 * y} := by
    ext x
    constructor
    · rintro ⟨hx, h⟩
      exact ⟨⟨x, hx⟩, h, rfl⟩
    · rintro ⟨⟨x, hx⟩, h, rfl⟩
      exact ⟨hx, h⟩
  rw [e]
  refine hS.subtype_image ?_
  exact (measurableSet_le h1.measurable measurable_const).inter
    ((measurableSet_le h2.measurable measurable_const).inter
      ((measurableSet_lt measurable_const hY).inter (measurableSet_le hY measurable_const)))

end GlobalTheory.Amp.YMeas
