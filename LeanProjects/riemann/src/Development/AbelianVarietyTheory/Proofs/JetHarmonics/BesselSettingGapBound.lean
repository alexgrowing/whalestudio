import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsHaarOnIffGroupsUnitaryUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselPeriodAdjointPairStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselCharacterUnipotentRadicalPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupParameterMeasurePreservingStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DecayThresholdsOfSpectralGapConditionStatement

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselFirstLeft

theorem sigmaFinite_of_haar {k r : ℕ} {U : Set (B.Mat k r)} {μ : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (h : B.IsHaarOn U μ) : SigmaFinite μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun {K} hK => h.finite_compact K hK⟩
  infer_instance

theorem left_integral {k r : ℕ} (R : Rep k r) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (l : R.H → Wp) (hk : 1 ≤ k) (hz : Formalism.QuantumDeterminants.inWb k r z)
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hW : B.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : B.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) (hl : IsBeL R z π μW μN l)
    {Y x : R.H} (hY : Y ∈ R.sm) (hx : x ∈ R.TK) :
    Integrable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.2) *
        ⟪x, R.σ ((Matrix.of p.1)⁻¹ * (Matrix.of p.2)⁻¹) Y⟫_ℂ) • π (Matrix.of p.1)) (μW.prod μN) ∧
    ∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
      (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.2) *
        ⟪x, R.σ ((Matrix.of p.1)⁻¹ * (Matrix.of p.2)⁻¹) Y⟫_ℂ) • π (Matrix.of p.1) ∂(μW.prod μN) =
      (innerSL ℂ (l x)).smulRight (l Y) := by
  obtain ⟨-, -, -, -, hinv, hae⟩ := GlobalTheory.T.besselSubgroup_parameter_measurePreserving k r z μW μN hk hz hT
    (((GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r μW).2.2 z hz hT hk).2 hW) ((GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r μN).2.1.2 hN)
  obtain ⟨-, -, hψ, -, hU, -⟩ := GlobalTheory.T.besselCharacter_unipotentRadical_properties k r z Formalism.QuantumDeterminants.cStd hz
  obtain ⟨hint, hbe⟩ := hl.2 Y hY x hx
  set φ := (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => ((Matrix.of p.1)⁻¹ : Mx k r) i j), (fun i j => ((Matrix.of p.2)⁻¹ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) with hφ
  have heq : (fun p => beInt z Formalism.QuantumDeterminants.cStd π R.σ Y x (φ p)) =ᵐ[μW.prod μN]
      (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.2) *
        ⟪x, R.σ ((Matrix.of p.1)⁻¹ * (Matrix.of p.2)⁻¹) Y⟫_ℂ) • π (Matrix.of p.1)) := by
    filter_upwards [hae] with p hp
    have h1 : ((Matrix.of p.1 : Mx k r)⁻¹)⁻¹ = Matrix.of p.1 :=
      Matrix.nonsing_inv_nonsing_inv _ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_unit (hU _ hp.1 _ hp.1).2.2)
    have h2 := (hψ _ hp.2).2
    change (⟪x, R.σ ((Matrix.of p.1 : Mx k r)⁻¹ * (Matrix.of p.2 : Mx k r)⁻¹) Y⟫_ℂ *
      star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.2 : Mx k r)⁻¹)) • π ((Matrix.of p.1 : Mx k r)⁻¹)⁻¹ = _
    rw [h1, h2, star_star, mul_comm]
  refine ⟨((hinv.integrable_comp hint.aestronglyMeasurable).2 hint).congr heq, ?_⟩
  rw [← integral_congr_ae heq, ← hbe, be]
  have := integral_map hinv.aemeasurable (f := beInt z Formalism.QuantumDeterminants.cStd π R.σ Y x)
    (by rw [hinv.map_eq]; exact hint.aestronglyMeasurable)
  rw [hinv.map_eq] at this
  exact this.symm

theorem bessel_integrate_left : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → ∀ γ ∈ JF.Om k r D.z D.z', ∃ A : R.H → Wq → Wq → Wp, (∀ y a c (t : ℂ), A y (t • a) c = star t • A y a c) ∧ ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ (X : Wq →L[ℂ] Wp) (c : Wq), B.JF D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ c = A y (ContinuousLinearMap.adjoint X (l x)) c := by
  intro hyp k r ε mu h R Wp _ _ _ _ Wq _ _ _ _ D l l' hDS hgap hok hl hl' γ hγ
  refine ⟨fun y a c => ∫ q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
    (star (Formalism.QuantumDeterminants.psi k r D.z' Formalism.QuantumDeterminants.cStd (Matrix.of q.2)) * ⟪a, D.π' (Matrix.of q.1)⁻¹ c⟫_ℂ) •
      l (R.σ (γ * Matrix.of q.2 * Matrix.of q.1) y) ∂(D.μW'.prod D.μN), ?_, ?_⟩
  · intro y a c t
    rw [← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only [inner_smul_left, smul_smul]
    congr 1
    rw [starRingEnd_apply]; ring
  intro x hx y hy X c
  haveI := sigmaFinite_of_haar D.haarW
  haveI := sigmaFinite_of_haar D.haarW'
  haveI := sigmaFinite_of_haar D.haarN
  obtain ⟨hmul, -, -, hsm, hTK, -⟩ := GlobalTheory.rep_basic_of_isDS hyp.1.2.2.1 k r ε mu R hDS
  have hcoef : IsCoef R l l' (fun g => ⟪x, R.σ g y⟫_ℂ • X) ⟪l x, X (l' y)⟫_ℂ :=
    ⟨1, fun _ => x, fun _ => y, fun _ => X, fun _ => ⟨hx, hy⟩, fun g _ => by simp, by simp⟩
  have hcc := (GlobalTheory.T.smooth_and_inCC_of_isCoef_of_gap hyp k r ε mu h R Wp Wq l l' _ _ hDS hgap hok hcoef).2 0
  have hint := (Formalism.FourierDecayAlt.P.bessel_integral_converges k r Wp Wq D _ _ (GlobalTheory.T.decayThresholds_of_spectralGapCondition k r h hok).1 hcc).1 γ hγ
  have hJ : B.JF D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ =
      ∫ p, JF.integrand D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ p ∂D.μSS := rfl
  rw [hJ, ContinuousLinearMap.integral_apply hint]
  have hint' : Integrable (fun p => JF.integrand D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ p c)
      ((D.μW.prod D.μN).prod (D.μW'.prod D.μN)) :=
    (ContinuousLinearMap.apply ℂ Wp c).integrable_comp hint
  rw [B.RealPlaceData.μSS, integral_prod_symm _ hint']
  have hae := (GlobalTheory.T.besselSubgroup_parameter_measurePreserving k r D.z D.μW D.μN D.k_pos D.z_mem D.T_pos
    (((GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r D.μW).2.2 _ D.z_mem D.T_pos D.k_pos).2 D.haarW)
    ((GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r D.μN).2.1.2 D.haarN)).2.2.2.2.2
  have hae' := (GlobalTheory.T.besselSubgroup_parameter_measurePreserving k r D.z' D.μW' D.μN D.k_pos D.z'_mem D.T'_pos
    (((GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r D.μW').2.2 _ D.z'_mem D.T'_pos D.k_pos).2 D.haarW')
    ((GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r D.μN).2.1.2 D.haarN)).2.2.2.2.2
  obtain ⟨-, -, -, -, hU, hNG⟩ := GlobalTheory.T.besselCharacter_unipotentRadical_properties k r D.z Formalism.QuantumDeterminants.cStd D.z_mem
  obtain ⟨-, -, -, -, hU', -⟩ := GlobalTheory.T.besselCharacter_unipotentRadical_properties k r D.z' Formalism.QuantumDeterminants.cStd D.z'_mem
  refine integral_congr_ae ?_
  filter_upwards [hae'] with q hq
  have hg : γ * Matrix.of q.2 * Matrix.of q.1 ∈ GG k r :=
    Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hγ.1 (hNG _ hq.2)) (hU' _ hq.1 _ hq.1).2.2
  obtain ⟨hI, hE⟩ := left_integral R D.z D.π D.μW D.μN l D.k_pos D.z_mem D.T_pos D.haarW D.haarN hl
    (hsm _ hg y (hTK y hy)) hx
  have hE' := congrArg (fun T : Wp →L[ℂ] Wp =>
    star (Formalism.QuantumDeterminants.psi k r D.z' Formalism.QuantumDeterminants.cStd (Matrix.of q.2)) • T (X (D.π' (Matrix.of q.1)⁻¹ c))) hE
  simp only [ContinuousLinearMap.integral_apply hI] at hE'
  rw [← integral_smul] at hE'
  rw [ContinuousLinearMap.adjoint_inner_left, ← smul_smul]
  refine Eq.trans (integral_congr_ae ?_) hE'
  filter_upwards [hae] with p hp
  have hs : (Matrix.of p.1 : Mx k r)⁻¹ * (Matrix.of p.2 : Mx k r)⁻¹ ∈ GG k r :=
    Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv (hU _ hp.1 _ hp.1).2.2) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv (hNG _ hp.2))
  rw [← hmul _ hs _ hg]
  simp only [JF.integrand, JF.xiP, B.rho, B.sgs, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    map_smul, smul_smul, Matrix.mul_assoc]
  congr 1
  ring

end GlobalTheory.BesselFirstLeft
