import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLimitOfChart
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
open Filter Topology Metric Formalism.REAL

noncomputable section

namespace GlobalTheory.GaugeSubExists

open GlobalTheory.GaugeConst

variable {n : ℕ}

theorem exp_sub_one_mem (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ A) :
    NormedSpace.exp X - 1 ∈ A := by
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (n := Fin n) (R := ℝ) (α := ℂ)
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) X
  have h1 := (hasSum_nat_add_iff' 1).2 h
  simp only [Finset.range_one, Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one,
    pow_zero, one_smul] at h1
  have hp : ∀ k : ℕ, X ^ (k + 1) ∈ A := by
    intro k
    induction k with
    | zero => simpa using hX
    | succ k ih => rw [pow_succ]; exact hA _ ih _ hX
  exact A.closed_of_finiteDimensional.mem_of_tendsto h1.tendsto_sum_nat
    (Eventually.of_forall fun m => A.sum_mem fun k _ => A.smul_mem _ (hp k))

def algSub (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) : Subgroup (UJ ε) where
  carrier := {g | uMat g - 1 ∈ A}
  one_mem' := by
    change (1 : Matrix (Fin n) (Fin n) ℂ) - 1 ∈ A
    simp
  mul_mem' := by
    intro g h hg hh
    change uMat g * uMat h - 1 ∈ A
    have : uMat g * uMat h - 1 = (uMat g - 1) * (uMat h - 1) + (uMat g - 1) + (uMat h - 1) := by
      noncomm_ring
    rw [this]
    exact A.add_mem (A.add_mem (hA _ hg _ hh) hg) hh
  inv_mem' := by
    intro g hg
    have hgi : uMat g⁻¹ * uMat g = 1 := g.1.inv_mul
    have hst : ∀ x ∈ A, LinearMap.mulLeft ℝ (uMat g) x ∈ A := by
      intro x hx
      have : LinearMap.mulLeft ℝ (uMat g) x = (uMat g - 1) * x + x := by
        rw [LinearMap.mulLeft_apply]; noncomm_ring
      rw [this]
      exact A.add_mem (hA _ hg _ hx) hx
    have hinj : Function.Injective ((LinearMap.mulLeft ℝ (uMat g)).restrict hst) := by
      intro x y hxy
      have h1 : uMat g * x.1 = uMat g * y.1 := congrArg Subtype.val hxy
      have h2 := congrArg (uMat g⁻¹ * ·) h1
      simp only [← Matrix.mul_assoc, hgi, Matrix.one_mul] at h2
      exact Subtype.ext h2
    obtain ⟨x, hx⟩ := LinearMap.surjective_of_injective hinj ⟨_, hg⟩
    have h1 : uMat g * x.1 = uMat g - 1 := congrArg Subtype.val hx
    have h2 := congrArg (uMat g⁻¹ * ·) h1
    simp only [← Matrix.mul_assoc, hgi, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one] at h2
    change uMat g⁻¹ - 1 ∈ A
    rw [← neg_sub, ← h2]
    exact A.neg_mem x.2

theorem isClosed_algSub (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) : IsClosed (algSub ε A hA : Set (UJ ε)) :=
  A.closed_of_finiteDimensional.preimage ((continuous_uMat ε).sub continuous_const)

theorem exists_preimage {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
    (A : Submodule ℝ M) {f : M → M} (hf : HasStrictFDerivAt f (ContinuousLinearMap.id ℝ M) 0)
    (h0 : f 0 = 0) (hA : ∀ X ∈ A, f X ∈ A) {W : Set M} (hW : W ∈ 𝓝 (0 : M)) :
    ∀ᶠ a : A in 𝓝 0, ∃ Y ∈ A, Y ∈ W ∧ f Y = a.1 := by
  obtain ⟨p, hp⟩ := A.subtype.exists_leftInverse_of_injective A.ker_subtype
  have hp' : ∀ x : A, p x.1 = x := fun x => LinearMap.congr_fun hp x
  haveI : CompleteSpace A := FiniteDimensional.complete ℝ _
  have h1 : HasStrictFDerivAt (fun x : A => f x.1) A.subtypeL 0 :=
    HasStrictFDerivAt.comp (0 : A) (g := f) (f := Subtype.val) hf A.subtypeL.hasStrictFDerivAt
  have h2 := (LinearMap.toContinuousLinearMap p).hasStrictFDerivAt.comp (0 : A) h1
  have h3 : (LinearMap.toContinuousLinearMap p).comp A.subtypeL =
      (ContinuousLinearEquiv.refl ℝ A : A →L[ℝ] A) := by
    ext1 x; exact hp' x
  rw [h3] at h2
  have h4 := h2.map_nhds_eq_of_equiv
  simp only [Submodule.coe_zero, h0, map_zero] at h4
  rw [← h4]
  have h6 : Subtype.val ⁻¹' W ∈ 𝓝 (0 : A) := continuous_subtype_val.continuousAt.preimage_mem_nhds hW
  refine mem_of_superset (image_mem_map h6) ?_
  rintro _ ⟨Y, hY, rfl⟩
  exact ⟨Y.1, Y.2, hY, (congrArg Subtype.val (hp' ⟨_, hA _ Y.2⟩)).symm⟩

open scoped Matrix.Norms.Frobenius in

theorem exists_log (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) {W : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hW : W ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ)) :
    ∀ᶠ a : A in 𝓝 0, ∃ Y ∈ A, Y ∈ W ∧ NormedSpace.exp Y - 1 = a.1 :=
  exists_preimage A (f := fun Y => NormedSpace.exp Y - 1)
    (HasStrictFDerivAt.sub_const (f := NormedSpace.exp) 1 CompactDualExists.exp_strict)
    (sub_eq_zero.2 (NormedSpace.exp_zero (𝔸 := Matrix (Fin n) (Fin n) ℂ)))
    (fun _ hX => exp_sub_one_mem A hA hX) hW

def expSub (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) (X : ↥(A ⊓ lieJ ε)) : algSub ε A hA :=
  ⟨expJ ε ⟨X.1, X.2.2⟩, exp_sub_one_mem A hA X.2.1⟩

theorem continuous_expSub (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) : Continuous (expSub ε A hA) :=
  ((continuous_expJ ε).comp (continuous_subtype_val.subtype_mk _)).subtype_mk _

theorem expSub_image_mem_nhds (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) {U : Set ↥(A ⊓ lieJ ε)} (hU : U ∈ 𝓝 (0 : ↥(A ⊓ lieJ ε))) :
    expSub ε A hA '' U ∈ 𝓝 (1 : algSub ε A hA) := by
  obtain ⟨e, he, h0⟩ := UpqExpChart.exists_chart (n := Fin n)
  have hinj : Set.InjOn NormedSpace.exp e.source := he ▸ e.injOn
  have hs := e.open_source.mem_nhds h0
  obtain ⟨T, hT, hTU⟩ := (mem_nhds_subtype _ _ _).1 hU
  have h1 : expJ ε '' (Subtype.val ⁻¹' (T ∩ e.source)) ∈ 𝓝 (1 : UJ ε) :=
    expJ_image_mem_nhds ε (continuous_subtype_val.continuousAt.preimage_mem_nhds (inter_mem hT hs))
  have h2 : Subtype.val ⁻¹' (expJ ε '' (Subtype.val ⁻¹' (T ∩ e.source))) ∈ 𝓝 (1 : algSub ε A hA) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds h1
  have hc : Continuous fun g : algSub ε A hA => (⟨uMat g.1 - 1, g.2⟩ : A) :=
    (((continuous_uMat ε).comp continuous_subtype_val).sub continuous_const).subtype_mk _
  have h3 : Tendsto (fun g : algSub ε A hA => (⟨uMat g.1 - 1, g.2⟩ : A)) (𝓝 1) (𝓝 0) :=
    hc.tendsto' 1 0 (Subtype.ext (sub_self (1 : Matrix (Fin n) (Fin n) ℂ)))
  filter_upwards [h2, h3.eventually (exists_log A hA hs)] with g hg1 hg2
  obtain ⟨X, hX, hXg⟩ := hg1
  obtain ⟨Y, hYA, hY, hYg⟩ := hg2
  have h4 : NormedSpace.exp X.1 = uMat g.1 := congrArg uMat hXg
  have h5 : NormedSpace.exp Y = uMat g.1 := sub_left_injective hYg
  have h6 : X.1 = Y := hinj hX.2 hY (h4.trans h5.symm)
  exact ⟨⟨X.1, h6 ▸ hYA, X.2⟩, hTU hX.1, Subtype.ext hXg⟩

theorem finrank_eq (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) {d : ℕ}
    (E : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0)
    (hs : ∀ X, (X ∈ A ∧ inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) :
    Module.finrank ℝ ↥(A ⊓ lieJ ε) = d := by
  have h1 : A ⊓ lieJ ε = Submodule.span ℝ (Set.range E) := Submodule.ext hs
  have h2 : LinearIndependent ℝ E := by
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    have h := congrArg (fun Z => ((Z * (E k)ᴴ).trace).re) hc
    simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum,
      Complex.smul_re, hE] at h
    simpa using h
  rw [h1, finrank_span_eq_card h2, Fintype.card_fin]

open scoped Matrix.Norms.Frobenius in

theorem exists_limit (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) (μ : Measure (algSub ε A hA)) [μ.IsHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧ Tendsto
      (fun r : ℝ => (μ {g | Real.sqrt (Formalism.REAL.hs (uMat g.1 - 1)) ≤ r}).toReal /
        r ^ Module.finrank ℝ ↥(A ⊓ lieJ ε)) (𝓝[>] 0) (𝓝 c) := by
  let L₀ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :=
    LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ LinearMap.mul ℝ _
  have hL₀ : Continuous L₀ := L₀.continuous_of_finiteDimensional
  have h := exists_limit_of_chart ↥(A ⊓ lieJ ε) (Matrix (Fin n) (Fin n) ℂ) (algSub ε A hA) μ
    (expSub ε A hA) (fun g => uMat g.1)
    (A ⊓ lieJ ε).subtypeₗᵢ (fun g => L₀ (uMat g.1)) (continuous_expSub ε A hA)
    (Subtype.ext (uMat_injective ε (NormedSpace.exp_zero (𝔸 := Matrix (Fin n) (Fin n) ℂ))))
    (HasStrictFDerivAt.comp (0 : ↥(A ⊓ lieJ ε)) (g := NormedSpace.exp) (f := Subtype.val)
      CompactDualExists.exp_strict (A ⊓ lieJ ε).subtypeL.hasStrictFDerivAt)
    (hL₀.comp ((continuous_uMat ε).comp continuous_subtype_val)).continuousAt
    (by ext1 A; exact Matrix.one_mul A) (fun g h => rfl)
    (fun r hr => expSub_image_mem_nhds ε A hA (ball_mem_nhds 0 hr))
    ((uJEmb n ε).1.isInducing.comp IsInducing.subtypeVal)
  simp only [sqrt_hs]
  exact h

theorem exists_isGaugeSub : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) → (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → ∃ μ : Measure (Formalism.REAL.UJ ε), SigmaFinite μ ∧ IsGaugeSub {g | uMat g - 1 ∈ A} d μ := by
  intro n ε A d E hA hE hs
  have hcl := isClosed_algSub ε A hA
  haveI : LocallyCompactSpace (algSub ε A hA) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hemb : MeasurableEmbedding (Subtype.val : algSub ε A hA → UJ ε) :=
    MeasurableEmbedding.subtype_coe hcl.measurableSet
  obtain ⟨c, hc, h⟩ := exists_limit ε A hA Measure.haar
  rw [finrank_eq ε A E hE hs] at h
  set B := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) with hBdef
  have hBt : B ≠ ⊤ := measure_ball_lt_top.ne
  have hB : 0 < B.toReal := ENNReal.toReal_pos (measure_ball_pos _ 0 one_pos).ne' hBt
  have hq : 0 < B.toReal / c := div_pos hB hc
  set ν : Measure (algSub ε A hA) := (B.toReal / c).toNNReal • Measure.haar with hν
  haveI : ν.IsHaarMeasure := Measure.IsHaarMeasure.nnreal_smul _ (Real.toNNReal_pos.2 hq).ne'
  haveI : SecondCountableTopology (algSub ε A hA) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  refine ⟨ν.map Subtype.val, hemb.sigmaFinite_map, ?_, fun s hs => ?_, ?_⟩
  · rw [hemb.map_apply]
    convert measure_empty (μ := ν)
    ext g
    exact ⟨fun hg => hg g.2, False.elim⟩
  · rw [Measure.map_map (measurable_const_mul s) hemb.measurable]
    conv_rhs => rw [← map_mul_left_eq_self ν (⟨s, hs⟩ : algSub ε A hA)]
    rw [Measure.map_map hemb.measurable (measurable_const_mul _)]
    rfl
  · have h1 := ENNReal.tendsto_ofReal (h.const_mul (B.toReal / c))
    rw [div_mul_cancel₀ _ hc.ne', ENNReal.ofReal_toReal hBt] at h1
    refine h1.congr' ?_
    filter_upwards [h.eventually (lt_mem_nhds hc), self_mem_nhdsWithin] with r h2 hr
    have hr' : (0 : ℝ) < r := hr
    have h3 := (ENNReal.toReal_pos_iff.1 ((div_pos_iff_of_pos_right (pow_pos hr' d)).1 h2)).2.ne
    rw [hemb.map_apply, hν, Measure.coe_nnreal_smul_apply, ENNReal.ofReal_mul hq.le,
      ENNReal.ofReal_div_of_pos (pow_pos hr' d), ENNReal.ofReal_toReal h3, mul_div_assoc]
    rfl

end GlobalTheory.GaugeSubExists
