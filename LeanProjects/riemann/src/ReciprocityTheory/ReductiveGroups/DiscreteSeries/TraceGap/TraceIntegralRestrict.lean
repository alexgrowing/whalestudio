import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.LayerLeGeneratedTensorFock
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.TotalDegreeBindLeOfLinear

noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

section Int

variable {Kg : Type*} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
  {μ : Measure Kg} [IsFiniteMeasure μ]

theorem integrable_of_cont {F : Type*} [NormedAddCommGroup F] [SecondCountableTopologyEither Kg F]
    {f : Kg → F} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [SecondCountableTopologyEither Kg H]

theorem trace_integral_restrict (L : Submodule ℂ H) [FiniteDimensional ℂ L] {c : Kg → ℂ} (hc : Continuous c)
    (A : Kg → (H →L[ℂ] H)) (hA : ∀ v, Continuous fun k => A k v) (hAL : ∀ k, ∀ x ∈ L, A k x ∈ L)
    (B : H →L[ℂ] H) (hB : ∀ w, B w = ∫ k, c k • A k w ∂μ) (hBL : ∀ x ∈ L, B x ∈ L) :
    LinearMap.trace ℂ L ((B : H →ₗ[ℂ] H).restrict hBL) =
      ∫ k, c k * LinearMap.trace ℂ L ((A k : H →ₗ[ℂ] H).restrict (hAL k)) ∂μ := by
  let b := stdOrthonormalBasis ℂ L
  have hint : ∀ i, Integrable (fun k => c k • A k ((b i : L) : H)) μ :=
    fun i => integrable_of_cont (hc.smul (hA _))
  have h1 : ∀ i, inner ℂ (b i) (((B : H →ₗ[ℂ] H).restrict hBL) (b i)) =
      ∫ k, c k * inner ℂ ((b i : L) : H) (A k ((b i : L) : H)) ∂μ := by
    intro i
    rw [Submodule.coe_inner, LinearMap.coe_restrict_apply]
    change inner ℂ ((b i : L) : H) (B ((b i : L) : H)) = _
    rw [hB, ← integral_inner (hint i)]
    simp only [inner_smul_right]
  rw [LinearMap.trace_eq_sum_inner _ b]
  simp only [h1]
  rw [← integral_finsetSum _ fun i _ => integrable_of_cont (μ := μ)
    (f := fun k => c k * inner ℂ ((b i : L) : H) (A k ((b i : L) : H))) (hc.mul (continuous_const.inner (hA _)))]
  congr 1
  funext k
  rw [LinearMap.trace_eq_sum_inner _ b, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Submodule.coe_inner, LinearMap.coe_restrict_apply]
  rfl

end Int

section Str

variable {n : ℕ} {ε : Fin n → Bool}
  {Kg : Type*} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
  {μ : Measure Kg} [IsFiniteMeasure μ]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem int_str_eq (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {Y Y₀ : Submodule ℂ (TensorProduct ℂ D (Fock n))} [FiniteDimensional ℂ Y] (hle : Y₀ ≤ Y)
    (hSK : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ Y, wK hD hk y ∈ Y)
    (hY0K : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ Y₀, wK hD hk y ∈ Y₀)
    (hYG : ∀ y ∈ Y, gradT y ∈ Y) (hY0G : ∀ y ∈ Y₀, gradT y ∈ Y₀)
    {φ : Kg → Matrix (Fin n) (Fin n) ℂ} (hφc : Continuous φ) (hφK : ∀ g, φ g ∈ Kset ε)
    {c : Kg → ℂ} (hc : Continuous c)
    (hrange : ∀ y : TSub Y, tsubVal Y ((∫ k, c k • tOp hD hSK (φ k) ∂μ) y) ∈ Y₀) :
    ∫ k, c k * LinearMap.trace ℂ Y ((gradT ∘ₗ wK hD (hφK k)).restrict
        (fun y hy => hYG _ (hSK _ (hφK k) y hy))) ∂μ =
      ∫ k, c k * LinearMap.trace ℂ Y₀ ((gradT ∘ₗ wK hD (hφK k)).restrict
        (fun y hy => hY0G _ (hY0K _ (hφK k) y hy))) ∂μ := by
  classical
  set Yt := TSub Y
  let W : Kg → (Yt →L[ℂ] Yt) := fun k => tOp hD hSK (φ k)
  have hWc : Continuous W := by
    rw [continuous_clm_apply]
    intro y
    exact ((tOp_isURepOn hD hSK hσ).2.2 y).comp_continuous hφc hφK
  let Γt : Yt →L[ℂ] Yt := LinearMap.toContinuousLinearMap
    ((gradT.restrict hYG : Y →ₗ[ℂ] Y) : Yt →ₗ[ℂ] Yt)
  let Y0t : Submodule ℂ Yt := Y₀.comap (tsubVal Y)
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl Y0t
  let π : Yt →ₗ[ℂ] Yt := Y0t.subtype ∘ₗ Y0t.linearProjOfIsCompl C hC
  have hπ : ∀ z ∈ Y0t, π z = z := fun z hz => by
    show ((Y0t.linearProjOfIsCompl C hC z : Y0t) : Yt) = z
    have := Submodule.linearProjOfIsCompl_apply_left hC ⟨z, hz⟩
    exact congrArg Subtype.val this
  have hπr : ∀ z, π z ∈ Y0t := fun z => (Y0t.linearProjOfIsCompl C hC z).2
  let ℓl : (Yt →L[ℂ] Yt) →ₗ[ℂ] ℂ :=
    { toFun := fun A => LinearMap.trace ℂ Yt ((LinearMap.id - π) ∘ₗ (Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (A : Yt →ₗ[ℂ] Yt))
      map_add' := fun A A' => by simp [LinearMap.comp_add]
      map_smul' := fun a A => by simp [LinearMap.comp_smul] }
  let ℓ := LinearMap.toContinuousLinearMap ℓl
  have hint : Integrable (fun k => c k • W k) μ := integrable_of_cont (hc.smul hWc)
  set Bt := ∫ k, c k • W k ∂μ
  have hB0 : ℓ Bt = 0 := by
    show LinearMap.trace ℂ Yt ((LinearMap.id - π) ∘ₗ (Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (Bt : Yt →ₗ[ℂ] Yt)) = 0
    have : (LinearMap.id - π) ∘ₗ (Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (Bt : Yt →ₗ[ℂ] Yt) = 0 := by
      apply LinearMap.ext
      intro y
      have hy : Γt (Bt y) ∈ Y0t := hY0G _ (hrange y)
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.zero_apply]
      rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe, hπ _ hy, sub_self]
    rw [this, map_zero]
  have hcomm : ℓ Bt = ∫ k, c k * ℓ (W k) ∂μ := by
    rw [← ContinuousLinearMap.integral_comp_comm ℓ hint]
    simp only [map_smul, smul_eq_mul]

  have hWk : ∀ k, ((W k : Yt →L[ℂ] Yt) : Yt →ₗ[ℂ] Yt) =
      (((wK hD (hφK k)).restrict (hSK _ (hφK k)) : Y →ₗ[ℂ] Y) : Yt →ₗ[ℂ] Yt) := by
    intro k
    simp only [W, tOp, dif_pos (hφK k)]
    rfl
  have hY : ∀ k, LinearMap.trace ℂ Y ((gradT ∘ₗ wK hD (hφK k)).restrict
      (fun y hy => hYG _ (hSK _ (hφK k) y hy))) =
      LinearMap.trace ℂ Yt ((Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt)) := by
    intro k
    rw [hWk]
    rfl
  have hY0 : ∀ k, LinearMap.trace ℂ Y₀ ((gradT ∘ₗ wK hD (hφK k)).restrict
      (fun y hy => hY0G _ (hY0K _ (hφK k) y hy))) =
      LinearMap.trace ℂ Yt (π ∘ₗ (Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt)) := by
    intro k
    have hr : LinearMap.range (π ∘ₗ (Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt)) ≤ Y0t := by
      rintro _ ⟨y, rfl⟩
      exact hπr _
    rw [trace_eq_trace_restrict_of_range_le _ _ hr]
    have hmem : ∀ z : Y0t, tsubVal Y (z : Yt) ∈ Y₀ := fun z => z.2
    let f : Y0t →ₗ[ℂ] Y₀ :=
      { toFun := fun z => ⟨tsubVal Y (z : Yt), hmem z⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hf : Function.Bijective f := by
      constructor
      · intro x y hxy
        have h' : ((f x : Y₀) : TensorProduct ℂ D (Fock n)) = ((f y : Y₀) : TensorProduct ℂ D (Fock n)) := by
          rw [hxy]
        exact Subtype.ext (tsubVal_injective h')
      · intro y
        exact ⟨⟨(show Yt from ⟨y, hle y.2⟩), y.2⟩, rfl⟩
    let e := LinearEquiv.ofBijective f hf
    rw [← LinearMap.trace_conj' _ e]
    congr 1
    apply LinearMap.ext
    intro y
    rw [LinearEquiv.conj_apply_apply]
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [LinearEquiv.symm_apply_apply]
    apply Subtype.ext
    have hx : (Γt : Yt →ₗ[ℂ] Yt) ((W k : Yt →ₗ[ℂ] Yt) (x : Yt)) ∈ Y0t := by
      rw [hWk]
      exact hY0G _ (hY0K _ (hφK k) _ x.2)
    show _ = tsubVal Y (π ((Γt : Yt →ₗ[ℂ] Yt) ((W k : Yt →ₗ[ℂ] Yt) (x : Yt))))
    rw [hπ _ hx, hWk]
    rfl
  have hℓ : ∀ k, ℓ (W k) = LinearMap.trace ℂ Yt ((Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt)) -
      LinearMap.trace ℂ Yt (π ∘ₗ (Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt)) := by
    intro k
    show LinearMap.trace ℂ Yt ((LinearMap.id - π) ∘ₗ (Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt)) = _
    rw [LinearMap.sub_comp, map_sub, LinearMap.id_comp]
  have htc : Continuous fun k => LinearMap.trace ℂ Yt ((Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt)) := by
    let m : (Yt →L[ℂ] Yt) →ₗ[ℂ] ℂ :=
      { toFun := fun A => LinearMap.trace ℂ Yt ((Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (A : Yt →ₗ[ℂ] Yt))
        map_add' := fun A A' => by simp [LinearMap.comp_add]
        map_smul' := fun a A => by simp [LinearMap.comp_smul] }
    exact (LinearMap.continuous_of_finiteDimensional m).comp hWc
  have hℓc : Continuous fun k => ℓ (W k) := ℓ.continuous.comp hWc
  have hdiff : ∫ k, c k * (LinearMap.trace ℂ Yt ((Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt)) -
      LinearMap.trace ℂ Yt (π ∘ₗ (Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt))) ∂μ = 0 := by
    rw [← hB0, hcomm]
    simp only [hℓ]
  simp only [hY, hY0]
  have hi1 : Integrable (fun k => c k * LinearMap.trace ℂ Yt ((Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt))) μ :=
    integrable_of_cont (hc.mul htc)
  have hi2 : Integrable (fun k => c k *
      LinearMap.trace ℂ Yt (π ∘ₗ (Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt))) μ := by
    refine integrable_of_cont (hc.mul ?_)
    have : (fun k => LinearMap.trace ℂ Yt (π ∘ₗ (Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt))) =
        fun k => LinearMap.trace ℂ Yt ((Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt)) - ℓ (W k) := by
      funext k
      rw [hℓ]
      ring
    rw [this]
    exact htc.sub hℓc
  rw [← sub_eq_zero, ← integral_sub hi1 hi2]
  simpa only [mul_sub] using hdiff

end Str

section Range

variable {n : ℕ} {ε : Fin n → Bool}
  {Kg : Type*} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
  {μ : Measure Kg} [IsFiniteMeasure μ]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [SecondCountableTopologyEither Kg H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem btot_range (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {Y : Submodule ℂ (TensorProduct ℂ D (Fock n))} [FiniteDimensional ℂ Y]
    (hSK : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ Y, wK hD hk y ∈ Y)
    {L : Submodule ℂ D} {φ : Kg → Matrix (Fin n) (Fin n) ℂ} (hφc : Continuous φ) (hφK : ∀ g, φ g ∈ Kset ε)
    {c : Kg → ℂ} (hc : Continuous c)
    (hL : ∀ (s s' : Finset (Fin (n * n))) (u : H),
      ∫ k, (c k * ffMat ε (φ k) s s') • σ (φ k) u ∂μ ∈ L.map D.subtype)
    (hYP : Y ≤ physicalSubspace ε) (y : TSub Y) :
    tsubVal Y ((∫ k, c k • tOp hD hSK (φ k) ∂μ) y) ∈ tensFock (n := n) L ⊓ physicalSubspace ε := by
  refine ⟨?_, hYP (tsubVal_mem _)⟩
  apply mem_tensorFock_of_coeffs
  intro s
  have hW : Continuous fun k => tOp hD hSK (φ k) := by
    rw [continuous_clm_apply]
    intro v
    exact ((tOp_isURepOn hD hSK hσ).2.2 v).comp_continuous hφc hφK
  have hint : Integrable (fun k => c k • tOp hD hSK (φ k)) μ := integrable_of_cont (hc.smul hW)
  let Ψ : TSub Y →L[ℂ] H := LinearMap.toContinuousLinearMap
    (D.subtype ∘ₗ tcoef ((fockBasis n).coord s) ∘ₗ tsubVal Y)
  have hΨ : ∀ z, Ψ z = ((tcoef ((fockBasis n).coord s) (tsubVal Y z) : D) : H) := fun z => rfl
  have h1 : Ψ ((∫ k, c k • tOp hD hSK (φ k) ∂μ) y) = ∫ k, c k • Ψ (tOp hD hSK (φ k) y) ∂μ := by
    rw [ContinuousLinearMap.integral_apply hint, ← ContinuousLinearMap.integral_comp_comm Ψ
      (hint.apply_continuousLinearMap y)]
    simp only [ContinuousLinearMap.smul_apply, map_smul]
  have h2 : ∀ k, c k • Ψ (tOp hD hSK (φ k) y) =
      ∑ s', (c k * ffMat ε (φ k) s s') • σ (φ k) ((tcoef ((fockBasis n).coord s') (tsubVal Y y) : D) : H) := by
    intro k
    rw [hΨ, tOp_apply hD hSK (hφK k), tco_wK, Submodule.coe_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun s' _ => ?_
    rw [coord_ff_basis, Submodule.coe_smul, smul_smul]
    rfl
  have hmem : Ψ ((∫ k, c k • tOp hD hSK (φ k) ∂μ) y) ∈ L.map D.subtype := by
    rw [h1]
    simp_rw [h2]
    rw [integral_finsetSum]
    · exact Submodule.sum_mem _ fun s' _ => hL s s' _
    · intro s' _
      exact integrable_of_cont ((hc.mul ((ffMat_continuous s s').comp hφc)).smul
        (((hσ.2.2 _).comp_continuous hφc fun g => kset_mem_UJset (hφK g))))
  obtain ⟨x, hx, hxe⟩ := hmem
  have : tcoef ((fockBasis n).coord s) (tsubVal Y ((∫ k, c k • tOp hD hSK (φ k) ∂μ) y)) = x :=
    Subtype.ext (hxe.trans (hΨ _)).symm
  rw [this]
  exact hx

end Range

end ReciprocityTheory.ChartRestriction.DS.TRGap
