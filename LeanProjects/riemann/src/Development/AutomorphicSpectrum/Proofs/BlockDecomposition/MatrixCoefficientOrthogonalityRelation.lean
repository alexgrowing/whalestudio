import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulInner
open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.RgHeA
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.RgHeA

theorem isInvInvariant_of_right_haar {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : μ.IsInvInvariant := by
  haveI : IsFiniteMeasureOnCompacts μ.inv :=
    ⟨fun K hK => by rw [Measure.inv_apply]; exact hK.inv.measure_lt_top⟩
  obtain ⟨c, hc⟩ : ∃ c : NNReal, μ.inv = c • μ := ⟨_, Measure.isMulLeftInvariant_eq_smul μ.inv μ⟩
  have hsq : μ = (c * c) • μ := by
    calc μ = μ.inv.inv := (Measure.inv_inv μ).symm
      _ = (c • μ).inv := by rw [hc]
      _ = c • μ.inv := by rw [Measure.inv_def, Measure.inv_def, Measure.map_smul]
      _ = (c * c) • μ := by rw [hc, smul_smul]
  let K := Classical.arbitrary (TopologicalSpace.PositiveCompacts G)
  have hpos : μ K ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'
  have hfin : μ K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have hK : μ K = ((c * c) • μ) K := by rw [← hsq]
  rw [Measure.smul_apply, Measure.nnreal_smul_coe_apply] at hK
  have h1 : ((c * c : NNReal) : ENNReal) = 1 :=
    ((ENNReal.mul_left_inj hpos hfin).1 (by rw [one_mul]; exact hK.symm))
  have hcc : (c : ℝ) * c = 1 := by exact_mod_cast ENNReal.coe_eq_one.1 h1
  have hc1 : c = 1 := by
    have : (c : ℝ) = 1 := by nlinarith [c.coe_nonneg]
    exact_mod_cast this
  exact ⟨by rw [hc, hc1, one_smul]⟩

theorem isSelfAdjoint_coefOp : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (hσ : IsU σ), IsU ρ → ∀ (v : B) (hm : Integrable (fun g => star ⟪v, ρ g v⟫_ℂ) ν),
    IsSelfAdjoint (coefOp ν σ hσ (fun g => star ⟪v, ρ g v⟫_ℂ) hm) := by
  intro Γ _ _ _ _ _ _ _ ν _ _ A B _ _ _ _ _ _ σ ρ hσ hρ v hm
  haveI := GlobalTheory.CompanionTheory.RgHeA.isInvInvariant_of_right_haar ν
  obtain ⟨_, hadj, _, _⟩ := PositivityTheory.UnitaryDecomposition.X4.uRep_of hσ
  obtain ⟨_, hρadj, _, _⟩ := PositivityTheory.UnitaryDecomposition.X4.uRep_of hρ
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro a b
  try simp only [ContinuousLinearMap.coe_coe]
  rw [← inner_conj_symm, GlobalTheory.CompanionTheory.RgHeA.inner_coefOp, GlobalTheory.CompanionTheory.RgHeA.inner_coefOp, ← integral_conj]
  calc ∫ g, (starRingEnd ℂ) (star ⟪v, ρ g v⟫_ℂ * ⟪b, σ g a⟫_ℂ) ∂ν
      = ∫ g, star ⟪v, ρ g⁻¹ v⟫_ℂ * ⟪a, σ g⁻¹ b⟫_ℂ ∂ν := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        have e1 : star ⟪v, ρ g⁻¹ v⟫_ℂ = ⟪v, ρ g v⟫_ℂ := by
          rw [← hρadj]
          exact inner_conj_symm _ _
        have e2 : (starRingEnd ℂ) ⟪b, σ g a⟫_ℂ = ⟪a, σ g⁻¹ b⟫_ℂ := by
          rw [inner_conj_symm, hadj]
        show (starRingEnd ℂ) (star ⟪v, ρ g v⟫_ℂ * ⟪b, σ g a⟫_ℂ) = star ⟪v, ρ g⁻¹ v⟫_ℂ * ⟪a, σ g⁻¹ b⟫_ℂ
        rw [map_mul, e1, e2, starRingEnd_apply, star_star]
    _ = ∫ g, star ⟪v, ρ g v⟫_ℂ * ⟪a, σ g b⟫_ℂ ∂ν :=
        integral_inv_eq_self (fun g => star ⟪v, ρ g v⟫_ℂ * ⟪a, σ g b⟫_ℂ) ν

end GlobalTheory.CompanionTheory.RgHeA
