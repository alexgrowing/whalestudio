import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJFEInducedParabolic

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal Parabolic Iwasawa Measures MeasureTheory GJMatrix
open scoped NNReal ENNReal

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}

def cosetFamily (p : ℤ × (Fin n × Fin n → F)) : Fin n × Fin n → F → ℂ :=
  fun ij => cosetInd (LocalField.valBall F p.1) (p.2 ij)

omit [MeasurableSpace F] [BorelSpace F] in
theorem cosetFamily_mem (p : ℤ × (Fin n × Fin n → F)) (ij : Fin n × Fin n) :
    cosetFamily p ij ∈ LocalField.schwartzBruhat F :=
  cosetInd_valBall_mem p.1 (p.2 ij)

omit [MeasurableSpace F] [BorelSpace F] in

theorem isSchwartzBruhat_matrixTensor {g : Fin n × Fin n → F → ℂ}
    (hg : ∀ ij, g ij ∈ LocalField.schwartzBruhat F) : IsSchwartzBruhat (matrixTensor g) := by
  rw [isSchwartzBruhat_iff_comp_symm]
  have : matrixTensor g ∘ (matrixCoordHomeomorph (Fin n) F).symm = localTensor g := by
    funext x
    rfl
  rw [this]
  exact localTensor_mem hg

omit [MeasurableSpace F] [BorelSpace F] in

theorem exists_matrixTensor_decomp {Φ : Matrix (Fin n) (Fin n) F → ℂ} (hΦ : IsSchwartzBruhat Φ) :
    ∃ (S : Finset (ℤ × (Fin n × Fin n → F))) (c : ℤ × (Fin n × Fin n → F) → ℂ),
      ∀ X, Φ X = ∑ p ∈ S, c p * matrixTensor (cosetFamily p) X := by
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (mem_span_matrixTensor hΦ)
  refine ⟨c.support, c, fun X => ?_⟩
  rw [← hc, Finsupp.sum, Finset.sum_apply]
  rfl

instance isAddHaarMeasure_matrixMeasure (ψ : AddChar F Circle) :
    (matrixMeasure (LocalField.selfDualMeasure ψ) : Measure (Matrix (Fin n) (Fin n) F)).IsAddHaarMeasure := by
  have : (Measure.pi fun _ : Fin n => LocalField.selfDualMeasure ψ).IsAddHaarMeasure :=
    inferInstance
  have hH : (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n =>
      LocalField.selfDualMeasure ψ : Measure (Fin n → Fin n → F)).IsAddHaarMeasure := inferInstance
  exact hH

theorem localMatrixFourier_sum (ψ : AddChar F Circle) (hψ : Continuous ψ) {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) {T : ι → Matrix (Fin n) (Fin n) F → ℂ}
    (hT : ∀ p ∈ S, IsSchwartzBruhat (T p)) (Z : Matrix (Fin n) (Fin n) F) :
    localMatrixFourier ψ (fun X => ∑ p ∈ S, c p * T p X) Z =
      ∑ p ∈ S, c p * localMatrixFourier ψ (T p) Z := by
  simp only [localMatrixFourier, Finset.sum_mul]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [← integral_const_mul]
    congr 1
    funext X
    ring
  · intro p hp
    have hc : Continuous fun X : Matrix (Fin n) (Fin n) F => (ψ (trace (X * Z)) : ℂ) :=
      (continuous_subtype_val.comp hψ).comp (continuous_id.matrix_mul continuous_const).matrix_trace
    exact (((hT p hp).1.continuous.const_smul (c p)).mul hc).integrable_of_hasCompactSupport
      (((hT p hp).2.smul_left (f := fun _ => c p)).mul_right)

theorem lintegral_lt_top_of_le_sum {X ι : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ}
    {S : Finset ι} {g : ι → X → ℂ} {a : ι → ℝ} (ha : ∀ p, 0 ≤ a p)
    (hg : ∀ p ∈ S, Integrable (g p) μ) (hle : ∀ x, ‖f x‖ ≤ ∑ p ∈ S, a p * ‖g p x‖) :
    ∫⁻ x, ‖f x‖ₑ ∂μ < ⊤ := by
  calc ∫⁻ x, ‖f x‖ₑ ∂μ ≤ ∫⁻ x, ∑ p ∈ S, ENNReal.ofReal (a p) * ‖g p x‖ₑ ∂μ := by
        refine lintegral_mono fun x => ?_
        rw [← ofReal_norm]
        calc ENNReal.ofReal ‖f x‖ ≤ ENNReal.ofReal (∑ p ∈ S, a p * ‖g p x‖) :=
              ENNReal.ofReal_le_ofReal (hle x)
          _ = ∑ p ∈ S, ENNReal.ofReal (a p) * ‖g p x‖ₑ := by
              rw [ENNReal.ofReal_sum_of_nonneg fun p _ => mul_nonneg (ha p) (norm_nonneg _)]
              refine Finset.sum_congr rfl fun p _ => ?_
              rw [ENNReal.ofReal_mul (ha p), ofReal_norm]
    _ = ∑ p ∈ S, ENNReal.ofReal (a p) * ∫⁻ x, ‖g p x‖ₑ ∂μ := by
        rw [lintegral_finsetSum' _ fun p hp =>
          ((hg p hp).aestronglyMeasurable.enorm).const_mul _]
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ < ⊤ := ENNReal.sum_lt_top.2 fun p hp =>
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hg p hp).2

omit [MeasurableSpace F] [BorelSpace F] in
theorem norm_leviIntegrand (κ : levi F n β →* ℝ≥0) (Ψ : Matrix (Fin n) (Fin n) F → ℂ) (w : W)
    (ℓ : Module.Dual ℂ W) (s : ℂ) (m : levi F n β) :
    ‖leviIntegrand σ κ Ψ w ℓ s m‖ = ‖Ψ ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)‖ *
      ‖((κ m : ℝ≥0) : ℂ) * detPow (m : GL (Fin n) F) s * ℓ (σ m w)‖ := by
  simp only [leviIntegrand, norm_mul]
  ring

omit [MeasurableSpace F] [BorelSpace F] in
theorem norm_leviIntegrandB (κ : levi F n β →* ℝ≥0) (Ψ : Matrix (Fin n) (Fin n) F → ℂ) (w : W)
    (ℓ : Module.Dual ℂ W) (s : ℂ) (m : levi F n β) :
    ‖leviIntegrandB σ κ Ψ w ℓ s m‖ = ‖Ψ ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)‖ *
      ‖((((κ m)⁻¹ * leviModulus β m : ℝ≥0)) : ℂ) * detPow (m : GL (Fin n) F) (-s) * ℓ (σ m⁻¹ w)‖ := by
  simp only [leviIntegrandB, norm_mul]
  ring

omit [IsNonarchimedeanLocalField F] in

instance borelSpace_GL : BorelSpace (GL (Fin n) F) := by
  refine ⟨?_⟩
  have hM : (measurableSpace_matrix : MeasurableSpace (Matrix (Fin n) (Fin n) F)) =
      _root_.borel (Matrix (Fin n) (Fin n) F) := BorelSpace.measurable_eq
  show MeasurableSpace.comap Units.val _ = _
  rw [hM, ← borel_comap, ← (Measures.isOpenEmbedding_val F n).isEmbedding.eq_induced]

theorem levi_decomp {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {γ : RatFunc ℂ}
    (hL : LeviFE F σ (inducedChar β) (measureM β ψ) ψ γ) {Φ : Matrix (Fin n) (Fin n) F → ℂ}
    (hΦ : IsSchwartzBruhat Φ) (w : W) {ℓ : Module.Dual ℂ W}
    (hℓ : ℓ ∈ smoothVectors (Representation.dual σ)) :
    (∃ s₁ : ℝ, ∀ s : ℂ, s₁ < s.re → ∫⁻ m, ‖leviIntegrand σ (inducedChar β)
        (fun X => ∫ u, ((‖Φ (X + unipMatrix F u)‖ : ℝ) : ℂ) ∂unipMeasure β ψ) w ℓ s m‖ₑ
          ∂measureM β ψ < ⊤) ∧
    (∃ s₁ : ℝ, ∀ s : ℂ, s.re < s₁ → ∫⁻ m, ‖leviIntegrandB σ (inducedChar β)
        (fun X => ∫ u, ((‖localMatrixFourier ψ Φ (X + unipMatrix F u)‖ : ℝ) : ℂ) ∂unipMeasure β ψ)
          w ℓ s m‖ₑ ∂measureM β ψ < ⊤) ∧
    RatFE F γ
      (fun s => ∫ m, leviIntegrand σ (inducedChar β)
        (fun X => ∫ u, Φ (X + unipMatrix F u) ∂unipMeasure β ψ) w ℓ s m ∂measureM β ψ)
      (fun s => ∫ m, leviIntegrandB σ (inducedChar β)
        (fun X => ∫ u, localMatrixFourier ψ Φ (X + unipMatrix F u) ∂unipMeasure β ψ) w ℓ s m
          ∂measureM β ψ) := by
  classical
  obtain ⟨S, c, hc⟩ := exists_matrixTensor_decomp hΦ
  set T : ℤ × (Fin n × Fin n → F) → Matrix (Fin n) (Fin n) F → ℂ :=
    fun p => matrixTensor (cosetFamily p) with hTdef
  set L : ℤ × (Fin n × Fin n → F) → Matrix (Fin n) (Fin n) F → ℂ :=
    fun p => leviTensor β fun s => cosetFamily p s.1 with hLdef
  set Lh : ℤ × (Fin n × Fin n → F) → Matrix (Fin n) (Fin n) F → ℂ :=
    fun p => leviTensorHat β ψ fun s => cosetFamily p s.1 with hLhdef
  set K : ℤ × (Fin n × Fin n → F) → ℂ := fun p => tensorConst β ψ (cosetFamily p) with hKdef
  have hTsb : ∀ p, IsSchwartzBruhat (T p) := fun p =>
    isSchwartzBruhat_matrixTensor fun ij => cosetFamily_mem p ij
  have hLev := fun p => hL (fun s => cosetFamily p s.1) (fun s => cosetFamily_mem p s.1) w ℓ hℓ
  choose sA hA using fun p => (hLev p).1
  choose sB hB using fun p => (hLev p).2.1
  have hR := fun p => (hLev p).2.2
  have hΦeq : Φ = fun X => ∑ p ∈ S, c p * T p X := funext hc

  have hΨA : ∀ X : Matrix (Fin n) (Fin n) F, (∀ i j, β i ≠ β j → X i j = 0) →
      ∫ u, Φ (X + unipMatrix F u) ∂unipMeasure β ψ = ∑ p ∈ S, c p * (K p * L p X) := by
    intro X hX
    rw [hΦeq]
    simp only
    rw [integral_finsetSum _ fun p _ =>
      (integrable_add_unipMatrix (unipMeasure β ψ) (hTsb p) hX).const_mul (c p)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [integral_const_mul, integral_matrixTensor_add_unip ψ _ hX]
  have hΦh : ∀ Z, localMatrixFourier ψ Φ Z = ∑ p ∈ S, c p * localMatrixFourier ψ (T p) Z := by
    intro Z
    rw [hΦeq]
    exact localMatrixFourier_sum ψ hψ S c (fun p _ => hTsb p) Z
  have hΨB : ∀ X : Matrix (Fin n) (Fin n) F, (∀ i j, β i ≠ β j → X i j = 0) →
      ∫ u, localMatrixFourier ψ Φ (X + unipMatrix F u) ∂unipMeasure β ψ =
        ∑ p ∈ S, c p * (K p * Lh p X) := by
    intro X hX
    simp_rw [hΦh]
    rw [integral_finsetSum _ fun p _ =>
      (integrable_add_unipMatrix (unipMeasure β ψ) ((hTsb p).localMatrixFourier hψ hψ1) hX).const_mul
        (c p)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [integral_const_mul, integral_fourier_matrixTensor_add_unip hψ hψ1
      (fun ij => cosetFamily_mem p ij) hX]
  set s₁ : ℝ := ∑ p ∈ S, (|sA p| + |sB p|) with hs₁
  have hsA : ∀ p ∈ S, sA p ≤ s₁ := fun p hp =>
    (le_abs_self _).trans ((le_add_of_nonneg_right (abs_nonneg _)).trans
      (Finset.single_le_sum (f := fun p => |sA p| + |sB p|)
        (fun p _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hp))
  have hsB : ∀ p ∈ S, -s₁ ≤ sB p := fun p hp => by
    have h1 : |sB p| ≤ s₁ := (le_add_of_nonneg_left (abs_nonneg _)).trans
      (Finset.single_le_sum (f := fun p => |sA p| + |sB p|)
        (fun p _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hp)
    linarith [neg_abs_le (sB p)]

  have hRsum : RatFE F γ
      (fun s => ∑ p ∈ S, c p * K p *
        ∫ m, leviIntegrand σ (inducedChar β) (L p) w ℓ s m ∂measureM β ψ)
      (fun s => ∑ p ∈ S, c p * K p *
        ∫ m, leviIntegrandB σ (inducedChar β) (Lh p) w ℓ s m ∂measureM β ψ) :=
    RatFE.sum S fun p _ => RatFE.const_mul (c p * K p) (hR p)
  have hptA : ∀ s : ℂ, ∀ m : levi F n β, leviIntegrand σ (inducedChar β)
      (fun X => ∫ u, Φ (X + unipMatrix F u) ∂unipMeasure β ψ) w ℓ s m =
        ∑ p ∈ S, c p * K p * leviIntegrand σ (inducedChar β) (L p) w ℓ s m := by
    intro s m
    simp only [leviIntegrand]
    rw [hΨA _ (mem_levi.1 m.2), Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hptB : ∀ s : ℂ, ∀ m : levi F n β, leviIntegrandB σ (inducedChar β)
      (fun X => ∫ u, localMatrixFourier ψ Φ (X + unipMatrix F u) ∂unipMeasure β ψ) w ℓ s m =
        ∑ p ∈ S, c p * K p * leviIntegrandB σ (inducedChar β) (Lh p) w ℓ s m := by
    intro s m
    simp only [leviIntegrandB]
    rw [hΨB _ (mem_levi.1 m.2), Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => by ring

  have hnA : ∀ m : levi F n β, ∫ u, ‖Φ (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) +
      unipMatrix F u)‖ ∂unipMeasure β ψ ≤ ∑ p ∈ S, ‖c p‖ *
        (‖tensorConst β ψ (fun ij x => ((‖cosetFamily p ij x‖ : ℝ) : ℂ))‖ *
          ‖L p ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)‖) := by
    intro m
    have hX := mem_levi.1 m.2
    have hint : ∀ p, Integrable (fun u => T p (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) +
        unipMatrix F u)) (unipMeasure β ψ) := fun p =>
      integrable_add_unipMatrix (unipMeasure β ψ) (hTsb p) hX
    calc ∫ u, ‖Φ (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u)‖
          ∂unipMeasure β ψ
        ≤ ∫ u, ∑ p ∈ S, ‖c p‖ * ‖T p (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) +
            unipMatrix F u)‖ ∂unipMeasure β ψ := by
          refine integral_mono (integrable_add_unipMatrix (unipMeasure β ψ) hΦ hX).norm
            (integrable_finsetSum _ fun p _ => (hint p).norm.const_mul _) fun u => ?_
          rw [hc]
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl fun p _ => norm_mul _ _
      _ = ∑ p ∈ S, ‖c p‖ * (‖tensorConst β ψ (fun ij x => ((‖cosetFamily p ij x‖ : ℝ) : ℂ))‖ *
            ‖L p ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)‖) := by
          rw [integral_finsetSum _ fun p _ => (hint p).norm.const_mul _]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [integral_const_mul, integral_norm_matrixTensor_add_unip ψ _ hX]
  choose C hC0 hC using fun p => integral_norm_fourier_matrixTensor_add_unip (β := β) (ψ := ψ)
    (cosetFamily p)
  have hnB : ∀ m : levi F n β, ∫ u, ‖localMatrixFourier ψ Φ
      (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u)‖ ∂unipMeasure β ψ ≤
        ∑ p ∈ S, ‖c p‖ * (C p * ‖Lh p ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)‖) := by
    intro m
    have hX := mem_levi.1 m.2
    have hint : ∀ p, Integrable (fun u => localMatrixFourier ψ (T p)
        (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u)) (unipMeasure β ψ) :=
      fun p => integrable_add_unipMatrix (unipMeasure β ψ) ((hTsb p).localMatrixFourier hψ hψ1) hX
    calc ∫ u, ‖localMatrixFourier ψ Φ (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) +
          unipMatrix F u)‖ ∂unipMeasure β ψ
        ≤ ∫ u, ∑ p ∈ S, ‖c p‖ * ‖localMatrixFourier ψ (T p)
            (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u)‖
              ∂unipMeasure β ψ := by
          refine integral_mono (integrable_add_unipMatrix (unipMeasure β ψ)
            (hΦ.localMatrixFourier hψ hψ1) hX).norm
            (integrable_finsetSum _ fun p _ => (hint p).norm.const_mul _) fun u => ?_
          rw [hΦh]
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl fun p _ => norm_mul _ _
      _ = ∑ p ∈ S, ‖c p‖ * (C p * ‖Lh p ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)‖) := by
          rw [integral_finsetSum _ fun p _ => (hint p).norm.const_mul _]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [integral_const_mul, hC p hX]
  have hnorm : ∀ (m : levi F n β) (Ξ : Matrix (Fin n) (Fin n) F → ℂ),
      ‖∫ u, ((‖Ξ (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u)‖ : ℝ) : ℂ)
        ∂unipMeasure β ψ‖ =
        ∫ u, ‖Ξ (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u)‖
          ∂unipMeasure β ψ := fun m Ξ => by
    rw [integral_complex_ofReal, Complex.norm_real,
      Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  refine ⟨⟨s₁, fun s hs => ?_⟩, ⟨-s₁, fun s hs => ?_⟩, hRsum.congr ⟨s₁, fun s hs => ?_⟩
    ⟨-s₁, fun s hs => ?_⟩⟩
  · refine lintegral_lt_top_of_le_sum (S := S)
      (a := fun p => ‖c p‖ * ‖tensorConst β ψ (fun ij x => ((‖cosetFamily p ij x‖ : ℝ) : ℂ))‖)
      (fun p => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun p hp => hA p s (lt_of_le_of_lt (hsA p hp) hs)) fun m => ?_
    rw [norm_leviIntegrand, hnorm]
    refine (mul_le_mul_of_nonneg_right (hnA m) (norm_nonneg _)).trans (le_of_eq ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [norm_leviIntegrand]
    ring
  · refine lintegral_lt_top_of_le_sum (S := S) (a := fun p => ‖c p‖ * C p)
      (fun p => mul_nonneg (norm_nonneg _) (hC0 p))
      (fun p hp => hB p s (lt_of_lt_of_le hs (hsB p hp))) fun m => ?_
    rw [norm_leviIntegrandB, hnorm]
    refine (mul_le_mul_of_nonneg_right (hnB m) (norm_nonneg _)).trans (le_of_eq ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [norm_leviIntegrandB]
    ring
  · simp_rw [hptA s]
    rw [integral_finsetSum _ fun p hp =>
      (hA p s (lt_of_le_of_lt (hsA p hp) hs)).const_mul (c p * K p)]
    exact Finset.sum_congr rfl fun p _ => integral_const_mul _ _
  · simp_rw [hptB s]
    rw [integral_finsetSum _ fun p hp =>
      (hB p s (lt_of_lt_of_le hs (hsB p hp))).const_mul (c p * K p)]
    exact Finset.sum_congr rfl fun p _ => integral_const_mul _ _

end GodementJacquet

end GroundTheory.Automorphic
