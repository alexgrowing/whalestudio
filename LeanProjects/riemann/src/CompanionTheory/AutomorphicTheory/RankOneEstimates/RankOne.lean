import CompanionTheory.AutomorphicTheory.RankOneEstimates.DecSender
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.ThmMOfXi
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.FrameBlockWMem
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDiagExists
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.IsHaarOnIffGroupsUnitaryUnipotentImports
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.BesselSubgroupParameterMeasurePreservingImports
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.BesselCharacterUnipotentRadicalPropertiesImports
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.EqSmulOfTwoSided
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.DiscreteSeriesUnitarySmoothBasicImports
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt

open Matrix MeasureTheory Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Formalism.QuantumDeterminants ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Mult1
open scoped InnerProductSpace ENNReal

noncomputable section

namespace CompanionTheory.FamilyDerivativeExpansion.M1

lemma haar_smul {k r : ℕ} {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ) {c : ℝ≥0∞} (h0 : c ≠ 0)
    (h1 : c ≠ ⊤) : B.IsHaarOn U (c • μ) where
  conc := by rw [Measure.smul_apply, h.conc, smul_zero]
  left := fun a ha => by rw [Measure.map_smul, h.left a ha]
  right := fun a ha => by rw [Measure.map_smul, h.right a ha]
  finite_compact := fun K hK => by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top h1.lt_top (h.finite_compact K hK)
  ne_zero := fun e => h.ne_zero (by
    have := congrArg (fun m : Measure (Mt k r) => m Set.univ) e
    simp only [Measure.smul_apply, smul_eq_mul, Measure.coe_zero, Pi.zero_apply, mul_eq_zero] at this
    exact Measure.measure_univ_eq_zero.1 (this.resolve_left h0))

theorem be_rank_one {k r : ℕ} (hk : 1 ≤ k) {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mx k r → (H →L[ℂ] H)}
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ} {π : Mx k r → (Wp →L[ℂ] Wp)} {μW μN : Measure (Mt k r)}
    (hl : IsHCParam lam) (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam h)
    (hh : 120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ h) (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hπ : PI.UpqRep.IsHCTypeW k r z u π) (hW : PI.BesselPeriodGGP.IsHaarOn (UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Nset k r) μN) :
    ∃ L : H → Wp, ∀ w ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
      Integrable (ThreeDimData.beInt z cStd π σ w v) (μW.prod μN) ∧
      be z cStd π σ μW μN w v = (innerSL ℂ (L v)).smulRight (L w) := by
  obtain ⟨hrep, hiso, hcont, hirr⟩ := TopTA.pi_facts (u := u) (π := π) hz hT hπ
  obtain ⟨D0, hDz, hDπ, hD0⟩ := stDiagExists multiplicity_one_hypotheses_hold k r Wp z π hk hz hT hrep hiso hcont hirr
  subst hDz hDπ
  have hfin : IsFiniteMeasure μW := (GlobalTheory.UnipotentRadicalHaar.unimodular_normal k r _ μW μN hz hT hW hN).2.1
  have hm0 : μW Set.univ ≠ 0 := fun e => hW.2.1 (Measure.measure_univ_eq_zero.1 e)
  have hm1 : μW Set.univ ≠ ⊤ := measure_ne_top _ _
  have hWB : B.IsHaarOn (UWset k r D0.z) ((μW Set.univ)⁻¹ • μW) :=
    haar_smul (((GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r μW).2.2 _ hz hT hk).1 hW) (ENNReal.inv_ne_zero.2 hm1) (ENNReal.inv_ne_top.2 hm0)
  let D : B.RealPlaceData k r Wp Wp :=
    { D0 with
      μW := (μW Set.univ)⁻¹ • μW, μW' := (μW Set.univ)⁻¹ • μW, μN := μN, haarW := hWB
      haarW' := by rw [hD0.z_eq]; exact hWB
      haarN := (GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r μN).2.1.1 hN }
  have hD : IsDiag D := ⟨hD0.z_eq, hD0.π_eq, rfl, by
    show ((μW Set.univ)⁻¹ • μW) Set.univ = 1
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hm0 hm1], hD0.irr⟩
  obtain ⟨hU, hsq⟩ := TopTA.sqInt_of_DSHpk (σ := σ) hσ D.haarG
  have hm : thrStar ε + ((4 * (2 * r + k + 1) ^ 3 : ℕ) : ℝ) < h := by
    have := DecS.thr_le (n := 2 * r + k + 1) (by omega) ε
    have h1 : (0 : ℝ) < ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := by positivity
    rw [Nat.cast_mul, Nat.cast_pow]
    push_cast at *
    linarith
  have dec : ∀ w ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
      ∃ C : ℝ, ∀ x ∈ B.GV k r, ‖⟪v, σ x w⟫_ℂ‖ ≤ C * B.gN x ^ (-aM k r) := by
    intro w hw v hv
    obtain ⟨C, Ws, -, h2⟩ := DecS.decayM hl hσ hg _ hm v hv
    exact ⟨_, fun x hx => h2 (aM k r) (by unfold aM nR; push_cast; rfl) w hw x hx⟩
  obtain ⟨-, -, -, -, hsm, -, hKT, ⟨w0, hw0, hw0K, -⟩, -⟩ :=
    GlobalTheory.T.discreteSeries_unitary_smooth_basic CompanionTheory.D.gk.admitted.k_finite_smooth k r ε lam ⟨H, σ⟩ ⟨hl, hσ⟩
  have hw0s := hsm w0 (hKT w0 hw0K)
  obtain ⟨C0, hC0⟩ := dec w0 hw0s w0 hw0s
  let X : SigData k r := ⟨H, σ, hU, TopTA.irr_of_DSHpk (σ := σ) hσ, w0, hw0, aM k r, C0, hC0⟩
  have hS : SqIntG D X := hsq
  obtain ⟨l, -, hl2⟩ := thmM k r Wp D X hD hS le_rfl
  have hmp := GlobalTheory.T.besselSubgroup_parameter_measurePreserving k r D.z D.μW μN hk hz hT (((GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r D.μW).2.2 _ hz hT hk).2 hWB) hN
  obtain ⟨-, -, hT4, -, -, hae⟩ := hmp
  have hψ := GlobalTheory.T.besselCharacter_unipotentRadical_properties k r D.z cStd hz
  have e : μW.prod μN = μW Set.univ • D.μW.prod μN := by
    haveI := hN.1
    show _ = μW Set.univ • ((μW Set.univ)⁻¹ • μW).prod μN
    rw [Measure.prod_smul_left, smul_smul, ENNReal.mul_inv_cancel hm0 hm1, one_smul]
  refine ⟨fun w => ((√(μW Set.univ).toReal : ℝ) : ℂ) • l w, fun w hw v hv => ?_⟩
  have hb : Mult1.AS k r + 1 ≤ aM k r := by
    unfold Mult1.AS aM
    have : (1 : ℝ) ≤ nR k r := by unfold nR; exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
    have := one_le_pow₀ (n := 3) this
    linarith
  have hI := stBeConv multiplicity_one_hypotheses_hold k r Wp D X hD hS (aM k r) hb w v (dec w hw v hv)
  have hae2 : ThreeDimData.beInt D.z cStd D.π σ w v =ᵐ[D.μW.prod μN] fun p => Mult1.beInt D X w v
      (((fun i j => (Matrix.of p.1 : Mx k r) i j),
        (fun i j => (Matrix.of p.1 * Matrix.of p.2 * (Matrix.of p.1)⁻¹ : Mx k r) i j)) : Mt k r × Mt k r) := by
    filter_upwards [hae] with p hp
    have hi := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hp.1).2.2
    have e1 : (Matrix.of p.1 * Matrix.of p.2 * (Matrix.of p.1)⁻¹ : Mx k r) * Matrix.of p.1 =
        Matrix.of p.1 * Matrix.of p.2 := by rw [Matrix.mul_assoc, hi, Matrix.mul_one]
    have e2 := (hψ.2.2.2.1 _ hp.1 _ hp.2).2.2.1
    show _ = (⟪v, σ ((Matrix.of p.1 * Matrix.of p.2 * (Matrix.of p.1)⁻¹ : Mx k r) * Matrix.of p.1) w⟫_ℂ *
      star (psi k r D.z cStd (Matrix.of p.1 * Matrix.of p.2 * (Matrix.of p.1)⁻¹))) • D.π (Matrix.of p.1)⁻¹
    rw [e1, e2]
    rfl
  have hI2 : Integrable (ThreeDimData.beInt D.z cStd D.π σ w v) (D.μW.prod μN) :=
    (integrable_congr hae2).2 (hT4.integrable_comp_of_integrable hI)
  have hv1 : ∫ p, ThreeDimData.beInt D.z cStd D.π σ w v p ∂(D.μW.prod μN) = rk1 (l w) (l v) := by
    rw [integral_congr_ae hae2, ← hl2 w (dec w hw w0 hw0s) v (dec v hv w0 hw0s)]
    have := integral_map (μ := D.μW.prod μN) hT4.measurable.aemeasurable
      (f := Mult1.beInt D X w v) (by rw [hT4.map_eq]; exact hI.aestronglyMeasurable)
    rw [hT4.map_eq] at this
    exact this.symm
  refine ⟨by rw [e]; exact hI2.smul_measure hm1, ?_⟩
  unfold be
  rw [e, integral_smul_measure]
  show (μW Set.univ).toReal • ∫ p, ThreeDimData.beInt D.z cStd D.π σ w v p ∂(D.μW.prod μN) = _
  rw [hv1]
  ext ξ
  have hs : ((√(μW Set.univ).toReal : ℝ) : ℂ) * ((√(μW Set.univ).toReal : ℝ) : ℂ) = ((μW Set.univ).toReal : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt ENNReal.toReal_nonneg]
  simp only [rk1, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    inner_smul_left, Complex.conj_ofReal, smul_smul]
  rw [← Complex.coe_smul, smul_smul, ← hs]
  congr 1
  ring

end CompanionTheory.FamilyDerivativeExpansion.M1
