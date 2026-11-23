import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory

noncomputable section

def cubeIco (κ : Type) : Set (κ → ℝ) := {x | ∀ i, x i ∈ Set.Ico (0 : ℝ) 1}

theorem cubeIco_eq (κ : Type) : cubeIco κ = Set.univ.pi fun _ => Set.Ico (0 : ℝ) 1 := by
  ext x
  simp [cubeIco, Set.mem_pi]

theorem cubeIco_meas (κ : Type) [Finite κ] : MeasurableSet (cubeIco κ) := by
  rw [cubeIco_eq]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ico

theorem vol_cubeIco (κ : Type) [Fintype κ] : volume (cubeIco κ) = 1 := by
  rw [cubeIco_eq, Real.volume_pi_Ico]
  simp

theorem cube_ae_eq (κ : Type) [Fintype κ] :
    cubeIco κ =ᵐ[volume] {x : κ → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} := by
  have h2 : {x : κ → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} = Set.univ.pi fun _ => Set.Ioc (0 : ℝ) 1 := by
    ext x; simp [Set.mem_pi]
  rw [cubeIco_eq, h2]
  exact (Measure.univ_pi_Ico_ae_eq_Icc).trans (Measure.univ_pi_Ioc_ae_eq_Icc).symm

theorem avg_fd_cube {ι κ : Type} [Fintype ι] [Fintype κ]
    (B : Module.Basis κ ℝ (EuclideanSpace ℂ ι)) (f : EuclideanSpace ℂ ι → ℝ) :
    ⨍ v in ZSpan.fundamentalDomain B, f v = ∫ x in cubeIco κ, f (B.equivFun.symm x) := by
  classical
  let e : EuclideanSpace ℂ ι ≃L[ℝ] (κ → ℝ) := B.equivFun.toContinuousLinearEquiv
  have hfd : ZSpan.fundamentalDomain B = e ⁻¹' cubeIco κ := by
    ext v
    simp [ZSpan.mem_fundamentalDomain, cubeIco, e]
  have hme : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  set μ : Measure (κ → ℝ) := (volume : Measure (EuclideanSpace ℂ ι)).map e with hμ
  haveI : μ.IsAddHaarMeasure := e.isAddHaarMeasure_map _
  have hsm : μ = μ.addHaarScalarFactor volume • volume := Measure.isAddLeftInvariant_eq_smul μ volume
  set c := μ.addHaarScalarFactor volume with hcdef
  have hvol : volume (ZSpan.fundamentalDomain B) = (c : ENNReal) := by
    rw [hfd, ← hme.map_apply, ← hμ, hsm]
    simp [vol_cubeIco]
  have hc : c ≠ 0 := by
    intro h0
    have h' : μ = 0 := by rw [hsm, h0, zero_smul]
    exact (NeZero.ne μ) h'
  have hint : ∫ v in ZSpan.fundamentalDomain B, f v = (c : ℝ) * ∫ x in cubeIco κ, f (e.symm x) := by
    have h3 : ∫ v in e ⁻¹' cubeIco κ, f v = ∫ v in e ⁻¹' cubeIco κ, (fun x => f (e.symm x)) (e v) := by
      simp
    have key := hme.setIntegral_map (μ := (volume : Measure (EuclideanSpace ℂ ι)))
      (fun x => f (e.symm x)) (cubeIco κ)
    rw [hfd, h3, ← key, ← hμ]
    conv_lhs => rw [hsm]
    rw [Measure.restrict_smul, integral_smul_nnreal_measure]
    all_goals rw [NNReal.smul_def, smul_eq_mul]
  rw [setAverage_eq, hint, Measure.real, hvol]
  have : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  simp only [ENNReal.coe_toReal, smul_eq_mul]
  field_simp
  rfl

theorem avg_fd_swap {ι κ₁ κ₂ : Type} [Fintype ι] [Fintype κ₁] [Fintype κ₂]
    (B₁ : Module.Basis κ₁ ℝ (EuclideanSpace ℂ ι)) (B₂ : Module.Basis κ₂ ℝ (EuclideanSpace ℂ ι))
    (h : Submodule.span ℤ (Set.range B₁) = Submodule.span ℤ (Set.range B₂))
    (f : EuclideanSpace ℂ ι → ℝ)
    (hf : ∀ γ ∈ Submodule.span ℤ (Set.range B₁), ∀ v, f (γ + v) = f v) :
    ⨍ v in ZSpan.fundamentalDomain B₁, f v = ⨍ v in ZSpan.fundamentalDomain B₂, f v := by
  haveI : VAddInvariantMeasure (Submodule.span ℤ (Set.range B₁)) (EuclideanSpace ℂ ι) volume :=
    ⟨fun c s _ => measure_preimage_add volume (c : EuclideanSpace ℂ ι) s⟩
  have h1 := ZSpan.isAddFundamentalDomain B₁ (volume : Measure (EuclideanSpace ℂ ι))
  have h2 := ZSpan.isAddFundamentalDomain B₂ (volume : Measure (EuclideanSpace ℂ ι))
  rw [← h] at h2
  have hinv : ∀ (g : Submodule.span ℤ (Set.range B₁)) (x : EuclideanSpace ℂ ι), f (g +ᵥ x) = f x :=
    fun g x => hf g g.2 x
  rw [setAverage_eq, setAverage_eq, h1.setIntegral_eq h2 hinv]
  simp only [Measure.real, h1.measure_eq h2]

end

end ReciprocityTheory.ChartRestriction.G.I2
