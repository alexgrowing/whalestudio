import Mathlib
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace ContDiff Topology Manifold

noncomputable section

namespace GlobalTheory.GardingSmooth

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem contDiff_matrix_mul {n : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {f g : P → Matrix (Fin n) (Fin n) ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ fun p => f p * g p := by
  let B : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
          (Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) ≃ₗ[ℝ]
            (Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ)).toLinearMap ∘ₗ
        LinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℂ))
  exact (B.contDiff.comp hf).clm_apply hg

theorem contDiff_adjoint {n : ℕ} : ContDiff ℝ ∞ fun x : Matrix (Fin n) (Fin n) ℂ => xᴴ := by
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    AddMonoidHom.toRealLinearMap (Matrix.conjTransposeAddEquiv (Fin n) (Fin n) ℂ).toAddMonoidHom
      continuous_id.matrix_conjTranspose
  exact L.contDiff

private theorem exists_contDiff_eq_on_closed_of_local {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {S : Set E} (hS : IsClosed S) (β : E → ℂ)
    (hβ : ∀ x ∈ S, ∃ (U : Set E) (F : E → ℂ), IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ ∞ F U ∧
      ∀ g ∈ U, g ∈ S → β g = F g) :
    ∃ φ : E → ℂ, ContDiff ℝ ∞ φ ∧ ∀ g ∈ S, φ g = β g := by
  classical
  have hloc : ∀ x : E, ∃ (U : Set E) (F : E → ℂ), IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ ∞ F U ∧
      ∀ g ∈ U, g ∈ S → β g = F g := by
    intro x
    by_cases hx : x ∈ S
    · exact hβ x hx
    · exact ⟨Sᶜ, fun _ => 0, hS.isOpen_compl, hx, contDiffOn_const, fun g hg hg' => (hg hg').elim⟩
  choose U F hUo hxU hFU hβF using hloc
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E) isClosed_univ U hUo
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxU x⟩)
  refine ⟨fun g => ∑ᶠ i, ρ i g • F i g, ?_, ?_⟩
  · rw [← contMDiff_iff_contDiff]
    refine ρ.contMDiff_finsum_smul fun i x hx => ?_
    exact ((hFU i).contDiffAt ((hUo i).mem_nhds (hρ i hx))).contMDiffAt
  · intro g hg
    have hterm : ∀ i, ρ i g • F i g = ρ i g • β g := by
      intro i
      by_cases h : ρ i g = 0
      · simp [h]
      · rw [hβF i g (hρ i (subset_tsupport _ h)) hg]
    simp_rw [hterm]
    rw [← finsum_smul, ρ.sum_eq_one (Set.mem_univ g), one_smul]

theorem exists_contDiff_extension {n : ℕ} {ε : Fin n → Bool} {β : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hβ : SmoothOnG ε β) :
    ∃ φ : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ∞ φ ∧ ∀ g, inUJ ε g → φ g = β g := by
  have hclosed : IsClosed {g : Matrix (Fin n) (Fin n) ℂ | inUJ ε g} := by
    have hc : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => gᴴ * Jm ε * g :=
      (contDiff_matrix_mul (contDiff_matrix_mul contDiff_adjoint contDiff_const) contDiff_id).continuous
    exact isClosed_eq hc continuous_const
  exact exists_contDiff_eq_on_closed_of_local hclosed β (fun x hx => hβ x hx)

private theorem hasFDerivAt_integral_lemma {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [SecondCountableTopology X] [T2Space X] (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] {P Z V E W : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [ProperSpace P] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (e : X → Z) (he : Continuous e) {K : Set X} (hK : IsCompact K) {s : Set P} (hs : IsOpen s)
    (B : V →L[ℝ] E →L[ℝ] W) (Ψ : P → Z → V) (w : X → E)
    (hΨ : ContDiff ℝ ∞ (Function.uncurry Ψ)) (hw : Continuous w)
    (hsupp : ∀ p ∈ s, ∀ y ∉ K, Ψ p (e y) = 0) {p₀ : P} (hp₀ : p₀ ∈ s) :
    HasFDerivAt (fun p => ∫ y, B (Ψ p (e y)) (w y) ∂μ)
      (∫ y, ((ContinuousLinearMap.compL ℝ P V W).comp B.flip).flip
        (fderiv ℝ (fun q => Ψ q (e y)) p₀) (w y) ∂μ) p₀ := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hs p₀ hp₀
  set B' := ((ContinuousLinearMap.compL ℝ P V W).comp B.flip).flip
  have hB' : ∀ L h, B' L h = (B.flip h).comp L := fun _ _ => rfl

  have hDs : ContDiff ℝ ∞ (fun x : P × Z => fderiv ℝ (fun q => Ψ q x.2) x.1) := by
    have hf' := hΨ.comp ((contDiff_snd (E := P × Z) (F := P)).prodMk
      ((contDiff_snd (E := P) (F := Z)).comp (contDiff_fst (E := P × Z) (F := P))))
    exact ContDiff.fderiv (f := fun (x : P × Z) (q : P) => Ψ q x.2) (g := Prod.fst) hf' contDiff_fst
      (le_of_eq ENat.coe_top_add_one)
  have hDc : Continuous (fun x : P × Z => fderiv ℝ (fun q => Ψ q x.2) x.1) := hDs.continuous
  have hpart : ∀ z, ContDiff ℝ ∞ (fun q => Ψ q z) := fun z =>
    hΨ.comp (contDiff_id.prodMk (contDiff_const (c := z)))
  have hderiv : ∀ y p, HasFDerivAt (fun q => B (Ψ q (e y)) (w y))
      (B' (fderiv ℝ (fun q => Ψ q (e y)) p) (w y)) p := by
    intro y p
    have h1 : HasFDerivAt (fun q => Ψ q (e y)) (fderiv ℝ (fun q => Ψ q (e y)) p) p :=
      ((hpart (e y)).differentiable (by simp) p).hasFDerivAt
    rw [hB']
    exact (B.flip (w y)).hasFDerivAt.comp p h1
  have hzero : ∀ p ∈ s, ∀ y ∉ K, fderiv ℝ (fun q => Ψ q (e y)) p = 0 := by
    intro p hp y hy
    have hev : (fun q => Ψ q (e y)) =ᶠ[nhds p] fun _ => 0 :=
      Filter.eventually_of_mem (hs.mem_nhds hp) fun q hq => hsupp q hq y hy
    rw [hev.fderiv_eq]
    simp
  have hΨc : ∀ p, Continuous fun y => Ψ p (e y) := fun p =>
    hΨ.continuous.comp (continuous_const.prodMk he)
  have hFc : ∀ p, Continuous fun y => B (Ψ p (e y)) (w y) := fun p =>
    (B.continuous.comp (hΨc p)).clm_apply hw
  have hF'c : Continuous fun y => B' (fderiv ℝ (fun q => Ψ q (e y)) p₀) (w y) :=
    (B'.continuous.comp (hDc.comp (continuous_const.prodMk he))).clm_apply hw

  have hcpt : IsCompact (Metric.closedBall p₀ (δ / 2) ×ˢ (e '' K)) :=
    (isCompact_closedBall _ _).prod (hK.image he)
  obtain ⟨C₁, hC₁⟩ := hcpt.exists_bound_of_continuousOn hDc.continuousOn
  obtain ⟨C₂, hC₂⟩ := hK.exists_bound_of_continuousOn hw.continuousOn
  have hsub : Metric.ball p₀ (δ / 2) ⊆ s := fun p hp =>
    hball (Metric.ball_subset_ball (by linarith) hp)
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hint : Integrable (fun y => B (Ψ p₀ (e y)) (w y)) μ := by
    rw [← integrableOn_iff_integrable_of_support_subset (s := K)]
    · exact (hFc p₀).continuousOn.integrableOn_compact hK
    · intro y hy
      by_contra hyK
      apply hy
      simp [hsupp p₀ hp₀ y hyK]
  have hbint : Integrable (K.indicator fun _ => ‖B'‖ * C₁ * C₂) μ :=
    (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hKm
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds p₀ (half_pos hδ))
    (Filter.Eventually.of_forall fun p => (hFc p).aestronglyMeasurable) hint
    hF'c.aestronglyMeasurable ?_ hbint (Filter.Eventually.of_forall fun y p _ => hderiv y p)
  refine Filter.Eventually.of_forall fun y p hp => ?_
  by_cases hy : y ∈ K
  · rw [Set.indicator_of_mem hy]
    have hL : ‖fderiv ℝ (fun q => Ψ q (e y)) p‖ ≤ C₁ :=
      hC₁ (p, e y) ⟨Metric.ball_subset_closedBall hp, Set.mem_image_of_mem e hy⟩
    have hh : ‖w y‖ ≤ C₂ := hC₂ y hy
    calc ‖B' (fderiv ℝ (fun q => Ψ q (e y)) p) (w y)‖
        ≤ ‖B'‖ * ‖fderiv ℝ (fun q => Ψ q (e y)) p‖ * ‖w y‖ := B'.le_opNorm₂ _ _
      _ ≤ ‖B'‖ * C₁ * C₂ :=
        mul_le_mul (mul_le_mul_of_nonneg_left hL (norm_nonneg _)) hh (norm_nonneg _)
          (mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans hL))
  · rw [hzero p (hsub hp) y hy]
    simp [hy]

private theorem contDiffOn_integral_lemma_2 {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [SecondCountableTopology X] [T2Space X] (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] {P Z : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [ProperSpace P] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (e : X → Z) (he : Continuous e) {K : Set X} (hK : IsCompact K) {s : Set P} (hs : IsOpen s)
    (m : ℕ) :
    ∀ (V E W : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E]
      [NormedSpace ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      (B : V →L[ℝ] E →L[ℝ] W) (Ψ : P → Z → V) (w : X → E),
      ContDiff ℝ ∞ (Function.uncurry Ψ) → Continuous w → (∀ p ∈ s, ∀ y ∉ K, Ψ p (e y) = 0) →
      ContDiffOn ℝ m (fun p => ∫ y, B (Ψ p (e y)) (w y) ∂μ) s := by
  induction m with
  | zero =>
    intro V E W _ _ _ _ _ _ _ B Ψ w hΨ hw hsupp
    simp only [Nat.cast_zero, contDiffOn_zero]
    intro p hp
    exact (hasFDerivAt_integral_lemma μ e he hK hs B Ψ w hΨ hw hsupp hp).continuousAt.continuousWithinAt
  | succ m ih =>
    intro V E W _ _ _ _ _ _ _ B Ψ w hΨ hw hsupp
    have hcast : ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 := by norm_cast
    rw [hcast, contDiffOn_succ_iff_fderiv_of_isOpen hs]
    refine ⟨fun p hp =>
      (hasFDerivAt_integral_lemma μ e he hK hs B Ψ w hΨ hw hsupp hp).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    have hD : ContDiff ℝ ∞ (Function.uncurry fun (p : P) (z : Z) => fderiv ℝ (fun q => Ψ q z) p) := by
      have hf' := hΨ.comp ((contDiff_snd (E := P × Z) (F := P)).prodMk
        ((contDiff_snd (E := P) (F := Z)).comp (contDiff_fst (E := P × Z) (F := P))))
      exact ContDiff.fderiv (f := fun (x : P × Z) (q : P) => Ψ q x.2) (g := Prod.fst) hf' contDiff_fst
        (le_of_eq ENat.coe_top_add_one)
    have hDz : ∀ p ∈ s, ∀ y ∉ K, fderiv ℝ (fun q => Ψ q (e y)) p = 0 := by
      intro p hp y hy
      have hev : (fun q => Ψ q (e y)) =ᶠ[nhds p] fun _ => 0 :=
        Filter.eventually_of_mem (hs.mem_nhds hp) fun q hq => hsupp q hq y hy
      rw [hev.fderiv_eq]
      simp
    refine (ih (P →L[ℝ] V) E (P →L[ℝ] W) (((ContinuousLinearMap.compL ℝ P V W).comp B.flip).flip)
      (fun p z => fderiv ℝ (fun q => Ψ q z) p) w hD hw hDz).congr fun p hp => ?_
    exact (hasFDerivAt_integral_lemma μ e he hK hs B Ψ w hΨ hw hsupp hp).fderiv

theorem garding_smooth : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ →
    ∀ β : Matrix (Fin n) (Fin n) ℂ → ℂ, SmoothOnG ε β → HasCompactSupport (fun g : UJ ε => β (umat g)) →
    ∀ u : H, SmoothOnGV ε (fun g => σ g (∫ y : UJ ε, β (umat y) • σ (umat y) u ∂(muG ε))) := by
  intro n ε H _ _ _ σ hσ β hβ hβc u g₀ _
  obtain ⟨⟨_, hσmul⟩, _, hσcont⟩ := hσ
  obtain ⟨φ, hφ, hφβ⟩ := exists_contDiff_extension hβ
  have hemb := (isClosedEmbeddingMatrix n ε).1
  have hum : Continuous (fun y : UJ ε => umat y) := hemb.continuous

  set T := tsupport (fun g : UJ ε => β (umat g)) with hT
  have hmulc : Continuous fun q : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => q.1 * q.2 :=
    (contDiff_matrix_mul contDiff_fst contDiff_snd).continuous
  have hcpt : IsCompact (Metric.closedBall g₀ 1 ×ˢ T) := (isCompact_closedBall _ _).prod hβc
  obtain ⟨R, hR⟩ := hcpt.exists_bound_of_continuousOn
    (f := fun q : Matrix (Fin n) (Fin n) ℂ × UJ ε => q.1 * umat q.2)
    (hmulc.comp (continuous_fst.prodMk (hum.comp continuous_snd))).continuousOn
  set R' := max R 0 with hR'
  have hR'0 : 0 ≤ R' := le_max_right _ _
  have hRR : R ≤ R' := le_max_left _ _
  let χ : ContDiffBump (0 : Matrix (Fin n) (Fin n) ℂ) := ⟨R' + 1, R' + 2, by linarith, by linarith⟩
  have hχsupp : Function.support χ = Metric.ball 0 (R' + 2) := χ.support_eq
  have hχone : ∀ Y : Matrix (Fin n) (Fin n) ℂ, ‖Y‖ ≤ R' + 1 → χ Y = 1 := fun Y hY =>
    χ.one_of_mem_closedBall (mem_closedBall_zero_iff.2 hY)

  let Ψ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ → ℂ := fun p Y =>
    ((χ Y : ℝ) : ℂ) * φ (Jm ε * pᴴ * Jm ε * Y)
  have hΨ : ContDiff ℝ ∞ (Function.uncurry Ψ) := by
    have h1 : ContDiff ℝ ∞ fun x : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ =>
        ((χ x.2 : ℝ) : ℂ) :=
      Complex.ofRealCLM.contDiff.comp (χ.contDiff.comp contDiff_snd)
    have h2 : ContDiff ℝ ∞ fun x : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ =>
        φ (Jm ε * x.1ᴴ * Jm ε * x.2) :=
      hφ.comp (contDiff_matrix_mul (contDiff_matrix_mul (contDiff_matrix_mul (contDiff_const (c := Jm ε))
        (contDiff_adjoint.comp contDiff_fst)) (contDiff_const (c := Jm ε))) contDiff_snd)
    exact h1.mul h2
  set K := (fun y : UJ ε => umat y) ⁻¹' Metric.closedBall 0 (R' + 2) with hKeq
  have hK : IsCompact K := hemb.isCompact_preimage (isCompact_closedBall _ _)
  have hsupp : ∀ p ∈ Metric.ball g₀ 1, ∀ y ∉ K, Ψ p (umat y) = 0 := by
    intro p _ y hy
    have h0 : χ (umat y) = 0 := by
      by_contra h
      have h' : umat y ∈ Function.support χ := h
      rw [hχsupp] at h'
      exact hy (Metric.ball_subset_closedBall h')
    simp [Ψ, h0]
  have hw : Continuous fun y : UJ ε => σ (umat y) u :=
    (hσcont u).comp_continuous hum (fun y => y.2)
  have hsmooth := contDiffOn_infty.2 fun m => contDiffOn_integral_lemma_2 (muG ε)
    (fun y : UJ ε => umat y) hum hK Metric.isOpen_ball m ℂ H H
    (ContinuousLinearMap.lsmul ℝ ℂ) Ψ (fun y => σ (umat y) u) hΨ hw hsupp
  refine ⟨Metric.ball g₀ 1, _, Metric.isOpen_ball, Metric.mem_ball_self one_pos, hsmooth, ?_⟩
  intro g hg hgG

  have hgG' : gᴴ * Jm ε * g = Jm ε := hgG
  have hinv : Jm ε * gᴴ * Jm ε * g = 1 := by
    calc Jm ε * gᴴ * Jm ε * g = Jm ε * (gᴴ * Jm ε * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hgG', Jm_mul_self]
  let gu : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨g, Jm ε * gᴴ * Jm ε, mul_eq_one_comm.1 hinv, hinv⟩
  let g' : UJ ε := ⟨gu, hgG⟩
  have hg'm : umat g' = g := rfl
  have hg'inv : umat g'⁻¹ = Jm ε * gᴴ * Jm ε := rfl
  have hφcomp : ∀ y : UJ ε, β (umat y) = φ (umat y) := fun y => (hφβ _ y.2).symm
  have hint : Integrable (fun y : UJ ε => β (umat y) • σ (umat y) u) (muG ε) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ (hβc.smul_right (f' := fun y => σ (umat y) u))
    have hβu : Continuous fun y : UJ ε => β (umat y) := by
      simp_rw [hφcomp]
      exact hφ.continuous.comp hum
    exact hβu.smul hw
  have hgl : g ∈ Metric.closedBall g₀ 1 := Metric.ball_subset_closedBall hg
  calc σ g (∫ y, β (umat y) • σ (umat y) u ∂muG ε)
      = ∫ y, σ g (β (umat y) • σ (umat y) u) ∂muG ε := ((σ g).integral_comp_comm hint).symm
    _ = ∫ y, β (umat (g'⁻¹ * (g' * y))) • σ (umat (g' * y)) u ∂muG ε := by
        congr 1
        funext y
        rw [inv_mul_cancel_left, map_smul]
        congr 1
        change σ g (σ (umat y) u) = σ (g * umat y) u
        rw [hσmul g hgG (umat y) y.2]
        try rfl
    _ = ∫ y, β (umat (g'⁻¹ * y)) • σ (umat y) u ∂muG ε :=
        integral_mul_left_eq_self (fun y => β (umat (g'⁻¹ * y)) • σ (umat y) u) g'
    _ = ∫ y, ContinuousLinearMap.lsmul ℝ ℂ (Ψ g (umat y)) (σ (umat y) u) ∂muG ε := by
        congr 1
        funext y
        rw [ContinuousLinearMap.lsmul_apply]
        congr 1
        have hprod : umat (g'⁻¹ * y) = Jm ε * gᴴ * Jm ε * umat y := rfl
        have hφy : φ (Jm ε * gᴴ * Jm ε * umat y) = β (umat (g'⁻¹ * y)) := by
          rw [← hprod]; exact (hφcomp _).symm
        simp only [Ψ, hφy]
        by_cases h0 : β (umat (g'⁻¹ * y)) = 0
        · simp [h0]
        · have hyT : g'⁻¹ * y ∈ T := subset_tsupport _ h0
          have hbd : ‖g * umat (g'⁻¹ * y)‖ ≤ R := hR (g, g'⁻¹ * y) ⟨hgl, hyT⟩
          have hY : g * umat (g'⁻¹ * y) = umat y := by
            rw [← hg'm]
            change umat (g' * (g'⁻¹ * y)) = umat y
            rw [mul_inv_cancel_left]
          rw [hY] at hbd
          rw [hχone (umat y) (by linarith), Complex.ofReal_one, one_mul]

end GlobalTheory.GardingSmooth
