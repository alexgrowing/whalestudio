import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.SIntShiftEqSmul
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.ContinuousBlkWConj

noncomputable section

open MeasureTheory Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Lap.TopPi

open ReciprocityTheory.ChartRestriction.DS.Lap

variable {k r : ℕ}

theorem inv_mem_UWset {z : Fin (2 * r + k + 1) → ℂ} {g : Mat k r} (hg : g ∈ Formalism.QuantumDeterminants.UWset k r z) :
    g⁻¹ ∈ Formalism.QuantumDeterminants.UWset k r z := by
  obtain ⟨hgH, hfix, hz⟩ := hg
  have hinv : g⁻¹ * g = 1 := ReciprocityTheory.ChartRestriction.DS.Xi.StepA.UH_inv_mul k r hgH
  have key : ∀ y, g *ᵥ y = y → g⁻¹ *ᵥ y = y := by
    intro y hy
    calc g⁻¹ *ᵥ y = g⁻¹ *ᵥ (g *ᵥ y) := by rw [hy]
      _ = (g⁻¹ * g) *ᵥ y := by rw [Matrix.mulVec_mulVec]
      _ = y := by rw [hinv, Matrix.one_mulVec]
  exact ⟨inv_mem_UH' hgH, fun a => ⟨key _ (hfix a).1, key _ (hfix a).2⟩, key _ hz⟩

theorem isClosed_UWset (z : Fin (2 * r + k + 1) → ℂ) : IsClosed (Formalism.QuantumDeterminants.UWset k r z) := by
  have hU : IsClosed {g : Mat k r | gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r} :=
    isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  have h1 : IsClosed {g : Mat k r | ∀ a : Fin r,
      g *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) = Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) ∧
        g *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI k r a) = Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI k r a)} := by
    simp only [Set.ofPred_forall, Set.ofPred_and]
    exact isClosed_iInter fun a =>
      (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const).inter
        (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const)
  have h2 : IsClosed {g : Mat k r | g *ᵥ z = z} :=
    isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const
  exact hU.inter (h1.inter h2)

theorem piInv_facts (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) {Vp : Type} [NormedAddCommGroup Vp]
    [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp] (π : Mat k r → (Vp →L[ℂ] Vp))
    (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z)
    (hπ : Formalism.MainNotions.S.IsHCTypeW k r z u π) (hμW : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hμN : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) :
    AEStronglyMeasurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => π (Matrix.of p.1)⁻¹) (μW.prod μN) ∧
      ∀ᵐ p ∂(μW.prod μN), ∀ v : Vp, ‖π (Matrix.of p.1)⁻¹ v‖ = ‖v‖ := by
  have hπU := hcTypeW_uRep k r z u Vp π hz hT hπ
  have := hμW.1
  have := hμN.1
  have hof : Continuous fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.1 : Mat k r) :=
    continuous_fst
  have hTae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z :=
    Measure.quasiMeasurePreserving_fst.ae (ae_iff.2 hμW.2.2.1)
  have hTc : IsClosed {p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r | Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z} :=
    (isClosed_UWset z).preimage hof
  have hπc : ContinuousOn π (Formalism.QuantumDeterminants.UWset k r z) := continuousOn_clm_apply.2 hπU.2.2
  have hinv : ContinuousOn (fun g : Mat k r => g⁻¹) (Formalism.QuantumDeterminants.UWset k r z) := by
    intro g hg
    have hgi : g⁻¹ * g = 1 := ReciprocityTheory.ChartRestriction.DS.Xi.StepA.UH_inv_mul k r hg.1
    have hu : IsUnit g.det := Matrix.isUnit_det_of_left_inverse hgi
    have hc := NormedRing.inverse_continuousAt hu.unit
    rw [IsUnit.unit_spec] at hc
    exact (continuousAt_matrix_inv g hc).continuousWithinAt
  have hcont : ContinuousOn (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => π (Matrix.of p.1)⁻¹)
      {p | Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z} :=
    hπc.comp (hinv.comp hof.continuousOn fun p hp => hp) fun p hp => inv_mem_UWset hp
  refine ⟨?_, ?_⟩
  · have h := hcont.aestronglyMeasurable (μ := μW.prod μN) hTc.measurableSet
    have hTae' : ∀ᵐ p ∂(μW.prod μN),
        p ∈ {p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r | Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z} := hTae
    rw [Measure.restrict_eq_self_of_ae_mem hTae'] at h
    exact h
  · filter_upwards [hTae] with p hp v
    exact hπU.2.1 _ (inv_mem_UWset hp) v

end ReciprocityTheory.ChartRestriction.DS.Lap.TopPi
