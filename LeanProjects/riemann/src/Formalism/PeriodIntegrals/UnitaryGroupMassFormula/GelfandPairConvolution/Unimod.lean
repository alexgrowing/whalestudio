import Mathlib

noncomputable section

namespace PI.UnitaryGroupMassFormula.GelfConv

open MeasureTheory Measure

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]

theorem eq_of_isMulLeftInvariant_of_univ (μ ν : Measure G) [μ.IsHaarMeasure]
    [ν.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts ν] (h : ν Set.univ = μ Set.univ) :
    ν = μ := by
  have hc : ν = haarScalarFactor ν μ • μ := isMulInvariant_eq_smul_of_compactSpace ν μ
  set C := haarScalarFactor ν μ
  have hμt : μ Set.univ ≠ ⊤ := isCompact_univ.measure_lt_top.ne
  have : (C : ENNReal) * μ Set.univ = 1 * μ Set.univ := by
    rw [one_mul, ← smul_eq_mul, ← ENNReal.smul_def, ← Measure.smul_apply, ← hc, h]
  have hC : C = 1 := by
    rwa [ENNReal.mul_left_inj (NeZero.ne _) hμt, ENNReal.coe_eq_one] at this
  rw [hc, hC, one_smul]

theorem isMulRightInvariant_of_compact (μ : Measure G) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant :=
  ⟨fun g => eq_of_isMulLeftInvariant_of_univ μ (map (· * g) μ)
    (by rw [map_apply (measurable_mul_const g) MeasurableSet.univ, Set.preimage_univ])⟩

theorem isInvInvariant_of_compact (μ : Measure G) [μ.IsHaarMeasure] : μ.IsInvInvariant := by
  have := isMulRightInvariant_of_compact μ
  have : IsFiniteMeasure μ.inv := ⟨by rw [inv_apply, Set.inv_univ]; exact measure_lt_top _ _⟩
  exact ⟨eq_of_isMulLeftInvariant_of_univ μ μ.inv (by rw [inv_apply, Set.inv_univ])⟩

theorem measurePreserving_of_hom (μ : Measure G) [μ.IsHaarMeasure] (σ : G →* G)
    (hc : Continuous σ) (hs : Function.Surjective σ) : MeasurePreserving σ μ μ :=
  MonoidHom.measurePreserving hc hs rfl

theorem measurePreserving_conj (μ : Measure G) [μ.IsHaarMeasure] (h : G) :
    MeasurePreserving (fun x => h * x * h⁻¹) μ μ := by
  let c : G →* G :=
    { toFun := fun x => h * x * h⁻¹
      map_one' := by simp
      map_mul' := fun x y => by group }
  exact measurePreserving_of_hom μ c (by simp only [c, MonoidHom.coe_mk, OneHom.coe_mk]; fun_prop)
    (fun y => ⟨h⁻¹ * y * h, by simp only [c, MonoidHom.coe_mk, OneHom.coe_mk]; group⟩)

theorem measurePreserving_anti (μ : Measure G) [μ.IsHaarMeasure] (τ : G → G) (hc : Continuous τ)
    (hm : ∀ x y, τ (x * y) = τ y * τ x) (hi : ∀ x, τ (τ x) = x) :
    MeasurePreserving τ μ μ := by
  have := isInvInvariant_of_compact μ
  have h1 : τ 1 = 1 := by
    have := hm 1 1
    simp only [mul_one] at this
    exact (mul_eq_left.mp this.symm)
  have hinv : ∀ x, τ x⁻¹ = (τ x)⁻¹ := fun x => by
    apply eq_inv_of_mul_eq_one_left
    rw [← hm, mul_inv_cancel, h1]
  let σ : G →* G :=
    { toFun := fun x => τ x⁻¹
      map_one' := by simp [h1]
      map_mul' := fun x y => by simp only [mul_inv_rev]; rw [hm] }
  have hσc : Continuous σ := hc.comp continuous_inv
  have hσs : Function.Surjective σ := fun y => ⟨(τ y)⁻¹, by simp [σ, hi]⟩
  have hσ := measurePreserving_of_hom μ σ hσc hσs
  have : τ = Inv.inv ∘ σ := funext fun x => by simp [σ, hinv]
  rw [this]
  exact (measurePreserving_inv μ).comp hσ

theorem integral_comp_homeo {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure G) (e : G ≃ₜ G) (he : MeasurePreserving e μ μ) (f : G → E) :
    ∫ x, f (e x) ∂μ = ∫ x, f x ∂μ :=
  he.integral_comp e.measurableEmbedding f

end PI.UnitaryGroupMassFormula.GelfConv
