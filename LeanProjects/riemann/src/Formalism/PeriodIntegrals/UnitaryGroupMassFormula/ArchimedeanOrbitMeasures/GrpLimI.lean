import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpTube
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpChartC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.JacGlue

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem tubeG_eq {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (V : Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) :
    TubeG X u' V = PI.AprimeInfG.tubeS (MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'))
      V Set.univ := by
  ext g
  constructor
  · rintro ⟨g', hg', he⟩
    have hs : g'⁻¹ * g ∈ MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u') := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, he, inv_smul_smul]
    exact ⟨g', hg', ⟨_, hs⟩, Set.mem_univ _, by simp⟩
  · rintro ⟨a, ha, h, -, rfl⟩
    refine ⟨a, ha, ?_⟩
    rw [mul_smul, MulAction.mem_stabilizer_iff.1 h.2]

def GrpChart {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) {ι : Type} [Fintype ι]
    (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) : Prop :=
  ∃ (η : Type) (_ : Fintype η)
    (χ : EuclideanSpace ℝ η → MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'))
    (r0 : ℝ) (d : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → ℝ) (e : EuclideanSpace ℝ η → ℝ)
    (ν : Measure (MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'))),
    ν.IsMulLeftInvariant ∧ SFinite ν ∧ ν Set.univ ≠ 0 ∧ ν Set.univ ≠ ⊤ ∧
    PI.AprimeInfG.TubeChart X.measG.μGinf (MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'))
      ν κ χ r0 d e ∧
    ContinuousAt d 0 ∧ 0 < d 0 ∧ ContinuousAt e 0 ∧ 0 < e 0 ∧ d 0 / e 0 * (ν Set.univ).toReal = gVal X

theorem grpLim_of_chart {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) {ι : Type} [Fintype ι]
    (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (h : GrpChart X u' κ) : GrpLim X u' κ := by
  obtain ⟨η, hη, χ, r0, d, e, ν, hL, hSF, h0, hf, hC, hd, hd0, he, he0, hval⟩ := h
  have : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [X.B.I.cm.deg2]; norm_num)
  have : SecondCountableTopology (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
    PI.AprimeInfT.secondCountable_HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  have : X.measG.μGinf.IsHaarMeasure := X.measG_norm.2.1
  have := hL
  have := hSF
  obtain ⟨⟨ρ0, hρ0, hP⟩, hT⟩ := PI.AprimeInfG.tube_ratio X.measG.μGinf _ ν h0 hf hC hd hd0 he he0
  refine ⟨⟨ρ0, hρ0, fun ρ hρ hρ' => ?_⟩, fun ρ hρ hρl => ?_⟩
  · rw [tubeG_eq]; exact hP ρ hρ hρ'
  · simp only [tubeG_eq]
    rw [← hval]
    exact hT.comp (tendsto_nhdsWithin_iff.2 ⟨hρl, Filter.Eventually.of_forall hρ⟩)

def GrpPieces {D7' : D7} (X : HidaSetting D7') (u' : D7'.what₂.Word) {ι : Type} [Fintype ι]
    (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) : Prop :=
  ∃ (η : Type) (_ : Fintype η)
    (χ : EuclideanSpace ℝ η → MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'))
    (r0 : ℝ) (φ : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)
    (U : Set (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)) (D : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → ℝ)
    (F : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → EuclideanSpace ℝ ι × EuclideanSpace ℝ η)
    (F' : EuclideanSpace ℝ ι × EuclideanSpace ℝ η →
      (EuclideanSpace ℝ ι × EuclideanSpace ℝ η →L[ℝ] EuclideanSpace ℝ ι × EuclideanSpace ℝ η))
    (e : EuclideanSpace ℝ η → ℝ)
    (ν : Measure (MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'))),
    ν.IsMulLeftInvariant ∧ SFinite ν ∧ ν Set.univ ≠ 0 ∧ ν Set.univ ≠ ⊤ ∧ 0 < r0 ∧
    ContinuousOn κ (ball 0 r0) ∧ ContinuousOn χ (ball 0 r0) ∧ Set.InjOn χ (ball 0 r0) ∧
    (∀ a ∈ ball (0 : EuclideanSpace ℝ ι) r0, ∀ b ∈ ball (0 : EuclideanSpace ℝ ι) r0,
      (κ a)⁻¹ * κ b ∈ MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u') → a = b) ∧
    (∀ A ⊆ U, MeasurableSet A → X.measG.μGinf (φ '' A) = ∫⁻ z in A, ENNReal.ofReal (D z)) ∧
    (∀ p ∈ ball (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) r0, HasFDerivWithinAt F (F' p) (ball 0 r0) p) ∧
    Set.InjOn F (ball 0 r0) ∧ F '' ball 0 r0 ⊆ U ∧
    (∀ p ∈ ball (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) r0, κ p.1 * (χ p.2 : HA _ _ _) = φ (F p)) ∧
    (∀ s, 0 < s → s ≤ r0 → ν (χ '' ball 0 s) = ∫⁻ y in ball 0 s, ENNReal.ofReal (e y)) ∧
    ContinuousAt F 0 ∧ ContinuousAt (fun p => |(F' p).det|) 0 ∧ ContinuousAt D (F 0) ∧ ContinuousAt e 0 ∧
    0 < e 0 ∧ 0 < |(F' 0).det| * D (F 0) ∧ |(F' 0).det| * D (F 0) / e 0 * (ν Set.univ).toReal = gVal X

theorem grpChart_of_pieces {D7' : D7} (X : HidaSetting D7') (u' : D7'.what₂.Word) {ι : Type} [Fintype ι]
    (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (h : GrpPieces X u' κ) :
    GrpChart X u' κ := by
  obtain ⟨η, hη, χ, r0, φ, U, D, F, F', e, ν, hL, hSF, h0, hf, hr0, hκc, hχc, hχi, hinj, hφ, hF, hFi, hFU, hΦ,
    hνH, hFc, hdet, hD, he, he0, hd0, hval⟩ := h
  have : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [X.B.I.cm.deg2]; norm_num)
  have : SecondCountableTopology (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
    PI.AprimeInfT.secondCountable_HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  have : X.measG.μGinf.IsHaarMeasure := X.measG_norm.2.1
  have hcl : IsClosed ((MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u') :
      Subgroup (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) : Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) :=
    by
      have hc := PI.AprimeInfT.continuous_orbit (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))
      show IsClosed ((fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J => g • Y0 X u') ⁻¹' {Y0 X u'})
      exact isClosed_singleton.preimage hc
  exact ⟨η, hη, χ, r0, fun p => |(F' p).det| * D (F p), e, ν, hL, hSF, h0, hf,
    PI.AprimeInfG.tubeChart_of X.measG.μGinf _ hcl ν κ χ hr0 hκc hχc hχi hinj φ U D hφ F F' hF hFi hFU hΦ e hνH,
    PI.AprimeInfG.contAt_dens hFc hdet hD, hd0, he, he0, hval⟩

theorem grpLim_of_pieces {D7' : D7} (X : HidaSetting D7') (u' : D7'.what₂.Word) {ι : Type} [Fintype ι]
    (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (h : GrpPieces X u' κ) : GrpLim X u' κ :=
  grpLim_of_chart X u' κ (grpChart_of_pieces X u' κ h)

end PI.AprimeInfW
