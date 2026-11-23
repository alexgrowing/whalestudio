import Mathlib
import Formalism.PeriodIntegrals.UMultOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompactGelfandAverage.AvgStep

noncomputable section

namespace PI.UnitaryGroupMassFormula.GelfCpt

open MeasureTheory Matrix

theorem integrable_of_cont {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] {F : X → ℂ} (hF : Continuous F) :
    Integrable F ν :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem haar_rightInv (μ : Measure G) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  constructor
  intro g
  have e := Measure.isMulLeftInvariant_eq_smul (Measure.map (· * g) μ) μ
  have hu : Measure.map (· * g) μ Set.univ = μ Set.univ := by
    rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, Set.preimage_univ]
  have h0 : μ Set.univ ≠ 0 := (Measure.measure_univ_pos.mpr (NeZero.ne μ)).ne'
  have ht : μ Set.univ ≠ ⊤ := measure_ne_top μ Set.univ
  have h1 : ((Measure.haarScalarFactor (Measure.map (· * g) μ) μ : NNReal) : ENNReal) * μ Set.univ =
      1 * μ Set.univ := by
    rw [one_mul]
    conv_rhs => rw [← hu, e]
    simp
  have hc : ((Measure.haarScalarFactor (Measure.map (· * g) μ) μ : NNReal) : ENNReal) = 1 :=
    (ENNReal.mul_left_inj h0 ht).1 h1
  rw [e, ENNReal.coe_eq_one.mp hc, one_smul]

theorem integral_conj (μ : Measure G) [μ.IsHaarMeasure] (F : G → ℂ) (h : G) :
    ∫ g, F (h * g * h⁻¹) ∂μ = ∫ g, F g ∂μ := by
  have := haar_rightInv μ
  have e1 := integral_mul_left_eq_self (μ := μ) (fun y => F (y * h⁻¹)) h
  have e2 := integral_mul_right_eq_self (μ := μ) F h⁻¹
  exact e1.trans e2

theorem mul_intMat_mul (μ : Measure G) [IsFiniteMeasure μ] {N : ℕ} (ρ : G →* GL (Fin N) ℂ)
    (hc : PI.UMultOne.Cont ρ) {f : G → ℂ} (hf : Continuous f) (M M' : Matrix (Fin N) (Fin N) ℂ)
    (i j : Fin N) :
    (M * intMat μ ρ f * M') i j =
      ∫ g, f g * (M * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * M') i j ∂μ := by
  have hR : ∀ k l, Continuous fun g => ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) k l :=
    fun k l => (continuous_apply l).comp ((continuous_apply k).comp hc)
  simp only [Matrix.mul_apply, intMat, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [← integral_const_mul, ← integral_mul_const]
      congr 1
      funext g
      ring
    · intro k _
      exact integrable_of_cont μ (hf.mul ((continuous_const.mul (hR k l)).mul continuous_const))
  · intro l _
    exact integrable_finsetSum _ (fun k _ =>
      integrable_of_cont μ (hf.mul ((continuous_const.mul (hR k l)).mul continuous_const)))

theorem intMat_conj (μ : Measure G) [μ.IsHaarMeasure] {N : ℕ} (ρ : G →* GL (Fin N) ℂ)
    (hc : PI.UMultOne.Cont ρ) {f : G → ℂ} (hf : Continuous f) (h : G)
    (hA : ((ρ h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * intMat μ ρ f =
      intMat μ ρ f * ((ρ h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) (i j : Fin N) :
    ∫ g, f (h⁻¹ * g * h) * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j ∂μ =
      intMat μ ρ f i j := by
  have hRmul : ∀ x y, ((ρ (x * y) : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      ((ρ x : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *
        ((ρ y : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := fun x y => by
    rw [map_mul, Units.val_mul]
  have e : ((ρ h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * intMat μ ρ f *
      ((ρ h⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = intMat μ ρ f := by
    rw [hA, Matrix.mul_assoc, ← hRmul, mul_inv_cancel, map_one, Units.val_one, Matrix.mul_one]
  rw [← e, mul_intMat_mul μ ρ hc hf]
  refine (integral_conj μ (fun x => f (h⁻¹ * x * h) *
    ((ρ x : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j) h).symm.trans ?_
  congr 1
  funext g
  have hg : h⁻¹ * (h * g * h⁻¹) * h = g := by group
  simp only [hg, hRmul]

end

theorem avgStep : AvgStep := by
  intro G _ _ _ _ _ _ _ _ μ _ H hH N ρ hc f hf hA
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  letI : MeasurableSpace H := borel H
  haveI : BorelSpace H := ⟨rfl⟩
  let ν : Measure H := Measure.haarMeasure ⊤
  haveI : IsProbabilityMeasure ν := ⟨by
    have := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts H))
    rwa [TopologicalSpace.PositiveCompacts.coe_top] at this⟩
  have hF : Continuous (Function.uncurry fun (g : G) (h : H) => f ((h : G)⁻¹ * g * h)) :=
    hf.comp (((continuous_subtype_val.comp continuous_snd).inv.mul continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd))
  refine ⟨fun g => ∫ h : H, f ((h : G)⁻¹ * g * h) ∂ν, ?_, ?_, ?_⟩
  · have := continuous_parametric_integral_of_continuous (μ := ν) hF isCompact_univ
    simpa only [Measure.restrict_univ] using this
  · intro k hk x
    show ∫ h : H, f ((h : G)⁻¹ * (k * x * k⁻¹) * h) ∂ν = ∫ h : H, f ((h : G)⁻¹ * x * h) ∂ν
    have e := integral_mul_left_eq_self (μ := ν) (fun h : H => f ((h : G)⁻¹ * x * h))
      (⟨k, hk⟩⁻¹ : H)
    rw [← e]
    congr 1
    funext h
    show f ((h : G)⁻¹ * (k * x * k⁻¹) * h) = f (((⟨k, hk⟩⁻¹ * h : H) : G)⁻¹ * x * ((⟨k, hk⟩⁻¹ * h : H) : G))
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev, inv_inv, mul_assoc]
  · ext i j
    have hR : Continuous fun g => ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j :=
      (continuous_apply j).comp ((continuous_apply i).comp hc)
    have hI : Integrable (Function.uncurry fun (g : G) (h : H) =>
        f ((h : G)⁻¹ * g * h) * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j)
        (μ.prod ν) :=
      integrable_of_cont _ (hF.mul (hR.comp continuous_fst))
    simp only [intMat, Matrix.of_apply]
    calc ∫ g, (∫ h : H, f ((h : G)⁻¹ * g * h) ∂ν) *
          ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j ∂μ
        = ∫ g, ∫ h : H, f ((h : G)⁻¹ * g * h) *
            ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j ∂ν ∂μ := by
          congr 1; funext g; rw [integral_mul_const]
      _ = ∫ h : H, ∫ g, f ((h : G)⁻¹ * g * h) *
            ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j ∂μ ∂ν :=
          integral_integral_swap hI
      _ = ∫ _h : H, intMat μ ρ f i j ∂ν := by
          congr 1; funext h
          exact intMat_conj μ ρ hc hf (h : G) (hA h h.2) i j
      _ = ∫ g, f g * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j ∂μ := by
          simp [intMat]

end PI.UnitaryGroupMassFormula.GelfCpt
