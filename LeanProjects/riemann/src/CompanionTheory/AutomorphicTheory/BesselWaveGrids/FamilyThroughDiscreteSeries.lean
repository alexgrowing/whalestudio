import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import Formalism.HermitianCurvature.StatementTBB
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.ImportsBisTer
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.DiscreteSeriesUnitarySmoothBasicImports
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorDecompositionInjectiveParameters
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.IsFRepDualStandardUnitaryRep
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.IsHaarOnIffGroupsUnitaryUnipotentImports
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.BesselSubgroupParameterMeasurePreservingImports
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.BesselCharacterUnipotentRadicalPropertiesImports
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.BetaInfEqIntegralOfIntegrableCoefficientImports
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.BesselNormSqEqConstMulArchPairingImports
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.DecayThresholdsOfSpectralGapConditionImports
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.BesselNormSqEqBigCellNormSqAltImports
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.NumericalFamilyShapeGaps
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.AemeasurableBesselNormIntegrandBigCellImports
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.NormSqIntegralInnerWeightLeImports
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.ImportsMore
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.SumNormSqHermTranslatesOrthonormalImports
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.WeilFormulaIntegrableComplexImports
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GapCoefficientBoundStatement
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.CasimirScalarOfCapelliDeterminantEigenvalueImpor
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.FrameWConjMatrixUnitsImports
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.ExistsLieUnitaryElementSimpleRootImports
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.ProductMomentBoundDensityMassOneImports
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.NumericalFamilyProductBoundConstantLeImports
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.BesselFunctionLocalityInvariantFactorFiniteSumIm
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.FactorizationOfConjHomogeneousAndHomogeneous
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.ExistsRegularRepBesselBigCellVectorEqBesselImpor
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqUnitNormalizationLe
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BaseRepCapelliEigenDual
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellExpansionSmulStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellExpansionOfBesselFunctionZeroStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BaseRepCapelliEigen
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsCoefContinuousOn
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.N1AddEZLe
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HsqNonneg
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopNum

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace CompanionTheory.WaveGrid.Ball

section sup

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

structure Sup0 (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (q0 : ℕ)
    (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq)
    (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ)
    (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ) : Prop where
  fam : IsFam lam q0 R
  left : haveI := FiniteDimensional.complete ℂ Wp
    SideFam p.T.base.z p.T.base.π p.T.base.μW p.T.base.μN p.T.base.μG q0 R l dg
  right : haveI := FiniteDimensional.complete ℂ Wq
    SideFam p.T.base.z' p.T.base.π' p.T.base.μW' p.T.base.μN p.T.base.μG q0 R l' dg
  coef : ∀ ν, n1 ν ≤ q0 → NzOn (R ν) (l ν) → NzOn (R ν) (l' ν) →
    IsCoef (R ν) (l ν) (l' ν) (J ν) (s ν) ∧ ‖s ν‖ = dg ν
  zero : ∀ ν, ¬ (n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)) → J ν = 0
  tau_zero : ∀ ν I, J ν = 0 ∨ J (ν + eZ I) = 0 → tau ν I = 0
  tau_eq : ∀ ν, n1 ν + (P.r + 1) * (P.r + 2) ≤ q0 →
    ∃ io pr ep, TensH (cmp (P.r + 1)) (cmp (P.r + 1) (Formalism.QuantumDeterminants.Hpk P.k P.r)) (R ν)
        (fun I : Sub (2 * P.r + P.k + 1) (P.r + 1) => R (ν + eZ I.1)) io pr ep ∧
      ∀ I : Sub (2 * P.r + P.k + 1) (P.r + 1), J ν ≠ 0 → J (ν + eZ I.1) ≠ 0 → ∃ κ κ' : ℂ,
        (∀ v ∈ (R ν).sm, l (ν + eZ I.1)
          (∑ c, pr I c (tm (R ν) (wedge (Formalism.QuantumDeterminants.fvec P.k P.r p.T.base.z)) v c)) = κ • l ν v) ∧
        (∀ v ∈ (R ν).sm, l' (ν + eZ I.1)
          (∑ c, pr I c (tm (R ν) (wedge (Formalism.QuantumDeterminants.fvec P.k P.r p.T.base.z')) v c)) = κ' • l' ν v) ∧
        tau ν I.1 = (ep I : ℂ) * κ' * star κ * s ν / s (ν + eZ I.1)

end sup

theorem family_through_discreteSeries : Hyps → ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ)
    (b bv ga h : ℝ) (q0 : ℕ) (R0 : Rep k r) (ν₀ : Fin (2 * r + k + 1) → ℤ), Num k r lam u b bv ga h q0 →
    R0.IsDS (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν₀ a : ℝ)) →
    ∃ R : (Fin (2 * r + k + 1) → ℤ) → Rep k r, IsFam lam q0 R ∧ R ν₀ = R0 := by
  intro hH k r lam u b bv ga h q0 R0 ν₀ hN hR0
  classical
  have hex : DSExist := hH.2.2.2.1
  have hC : ∃ P, PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) P := by
    obtain ⟨P, hP, -⟩ := hR0.2
    exact ⟨P, hP⟩
  have hfam := (GlobalTheory.T.numericalFamily_shape_gaps k r lam u b bv ga h q0 hN).2
  have key : ∀ ν : Fin (2 * r + k + 1) → ℤ, ∃ R : Rep k r,
      (∑ a, (ν a).natAbs ≤ q0 → R.IsDS (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ))) ∧
      (ν = ν₀ → R = R0) := by
    intro ν
    by_cases h0 : ν = ν₀
    · refine ⟨R0, fun _ => ?_, fun _ => rfl⟩
      subst h0
      exact hR0
    · by_cases hq : ∑ a, (ν a).natAbs ≤ q0
      · obtain ⟨R, hR⟩ := hex k r _ _ (hfam ν hq).1 hC
        exact ⟨R, fun _ => hR, fun h => absurd h h0⟩
      · exact ⟨R0, fun h => absurd h hq, fun _ => rfl⟩
  choose R hR using key
  exact ⟨R, fun ν hν => (hR ν).1 hν, (hR ν₀).2 rfl⟩

theorem exists_coef_family : Hyps → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (s₀ : ℂ) (ν₀ : Fin (2 * P.r + P.k + 1) → ℤ), n1 ν₀ ≤ q0 → IsFam lam q0 R → (haveI := FiniteDimensional.complete ℂ Wp; SideFam p.T.base.z p.T.base.π p.T.base.μW p.T.base.μN p.T.base.μG q0 R l dg) → (haveI := FiniteDimensional.complete ℂ Wq; SideFam p.T.base.z' p.T.base.π' p.T.base.μW' p.T.base.μN p.T.base.μG q0 R l' dg) → IsCoef (R ν₀) (l ν₀) (l' ν₀) f s₀ → s₀ ≠ 0 → ∃ (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (t : ℝ), 0 < t ∧ J ν₀ = (fun g => (t : ℂ) • f g) ∧ (NzOn (R ν₀) (l ν₀) ∧ NzOn (R ν₀) (l' ν₀)) ∧ (∀ ν, n1 ν ≤ q0 → NzOn (R ν) (l ν) → NzOn (R ν) (l' ν) → IsCoef (R ν) (l ν) (l' ν) (J ν) (s ν) ∧ ‖s ν‖ = dg ν) ∧ (∀ ν, ¬ (n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)) → J ν = 0) := by
  intro hH P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R l l' dg f s₀ ν₀ h0 hfam hL hR hf hs₀
  haveI := FiniteDimensional.complete ℂ Wp
  haveI := FiniteDimensional.complete ℂ Wq
  classical
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hDS : ∀ ν, n1 ν ≤ q0 → (R ν).IsDS (PI.BesselPeriodGGP.eps48 P.k P.r) (fun a => lam a + (ν a : ℝ)) :=
    fun ν hν => hfam ν hν
  have hdg0 : 0 < dg ν₀ := (hL ν₀ h0).2.1
  have hsn : 0 < ‖s₀‖ := norm_pos_iff.mpr hs₀
  have hnz : NzOn (R ν₀) (l ν₀) ∧ NzOn (R ν₀) (l' ν₀) := by
    obtain ⟨m, x, y, X, hxy, -, hs⟩ := hf
    have hsm := (GlobalTheory.rep_basic_of_isDS hK _ _ _ _ (R ν₀) (hDS ν₀ h0)).2.2.2.2.1
    rw [hs] at hs₀
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs₀
    refine ⟨⟨x i, hsm _ (hxy i).1, fun h => hi ?_⟩, ⟨y i, hsm _ (hxy i).2, fun h => hi ?_⟩⟩
    · rw [h, inner_zero_left]
    · rw [h, map_zero, inner_zero_right]
  have hex : ∀ ν, ∃ (s : ℂ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)),
      (ν = ν₀ → F = fun g => ((dg ν₀ / ‖s₀‖ : ℝ) : ℂ) • f g) ∧
      (n1 ν ≤ q0 → NzOn (R ν) (l ν) → NzOn (R ν) (l' ν) → IsCoef (R ν) (l ν) (l' ν) F s ∧ ‖s‖ = dg ν) ∧
      (¬ (n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)) → F = 0) := by
    intro ν
    by_cases hν : ν = ν₀
    · subst ν
      refine ⟨((dg ν₀ / ‖s₀‖ : ℝ) : ℂ) * s₀, _, fun _ => rfl, fun _ _ _ => ⟨?_, ?_⟩, fun hn => ?_⟩
      · exact (GlobalTheory.isCoef_of_translate_smul_exists hK _ _ _ _ (R ν₀) Wp Wq (l ν₀) (l' ν₀) (hDS ν₀ h0)).2.1 f s₀ _ hf
      · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_pos hdg0 hsn).le]
        field_simp
      · exact absurd ⟨h0, hnz⟩ hn
    · by_cases hc : n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)
      · obtain ⟨h1, h2, h3⟩ := hc
        have e1 := GlobalTheory.bessel_nonzero_on_translates hH _ _ _ _ (R ν) Wp _ _ (l ν) (hDS ν h1) (hL ν h1).1.1 h2
        have e2 := GlobalTheory.bessel_nonzero_on_translates hH _ _ _ _ (R ν) Wq _ _ (l' ν) (hDS ν h1) (hR ν h1).1.1 h3
        obtain ⟨F, hF⟩ := (GlobalTheory.isCoef_of_translate_smul_exists hK _ _ _ _ (R ν) Wp Wq (l ν) (l' ν)
          (hDS ν h1)).2.2 e1 e2 (dg ν : ℂ)
        refine ⟨_, F, fun h => absurd h hν, fun _ _ _ => ⟨hF, ?_⟩, fun hn => absurd ⟨h1, h2, h3⟩ hn⟩
        rw [Complex.norm_real, Real.norm_of_nonneg (hL ν h1).2.1.le]
      · exact ⟨0, 0, fun h => absurd h hν, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hc, fun _ => rfl⟩
  choose s J h1 h2 h3 using hex
  exact ⟨s, J, dg ν₀ / ‖s₀‖, div_pos hdg0 hsn, h1 ν₀ rfl, hnz, h2, h3⟩

theorem exists_tau : Hyps → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)), Num P.k P.r lam P.u b bv ga h q0 → IsFam lam q0 R → (haveI := FiniteDimensional.complete ℂ Wp; SideFam p.T.base.z p.T.base.π p.T.base.μW p.T.base.μN p.T.base.μG q0 R l dg) → (haveI := FiniteDimensional.complete ℂ Wq; SideFam p.T.base.z' p.T.base.π' p.T.base.μW' p.T.base.μN p.T.base.μG q0 R l' dg) → (∀ ν, n1 ν ≤ q0 → NzOn (R ν) (l ν) → NzOn (R ν) (l' ν) → IsCoef (R ν) (l ν) (l' ν) (J ν) (s ν) ∧ ‖s ν‖ = dg ν) → (∀ ν, ¬ (n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)) → J ν = 0) → ∃ tau, Sup0 p lam q0 R l l' dg s J tau := by
  intro hH P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R l l' dg s J hNum hFam hL hR hco hz
  classical
  haveI := FiniteDimensional.complete ℂ Wp
  haveI := FiniteDimensional.complete ℂ Wq
  obtain ⟨-, hz1, hz2, -, -, ht1, ht2⟩ := p.hP
  obtain ⟨νq, νq', hS, hS'⟩ := GlobalTheory.T.besselDatum_both_sides_are_sides P.k P.r Wp Wq p.T.base P.u P.u' ht1 ht2
  have key : ∀ ν, ∃ t : Finset (Fin (2 * P.r + P.k + 1)) → ℂ,
      (∀ I, J ν = 0 ∨ J (ν + eZ I) = 0 → t I = 0) ∧
      (n1 ν + (P.r + 1) * (P.r + 2) ≤ q0 →
    ∃ io pr ep, TensH (cmp (P.r + 1)) (cmp (P.r + 1) (Formalism.QuantumDeterminants.Hpk P.k P.r)) (R ν)
        (fun I : Sub (2 * P.r + P.k + 1) (P.r + 1) => R (ν + eZ I.1)) io pr ep ∧
      ∀ I : Sub (2 * P.r + P.k + 1) (P.r + 1), J ν ≠ 0 → J (ν + eZ I.1) ≠ 0 → ∃ κ κ' : ℂ,
        (∀ v ∈ (R ν).sm, l (ν + eZ I.1)
          (∑ c, pr I c (tm (R ν) (wedge (Formalism.QuantumDeterminants.fvec P.k P.r p.T.base.z)) v c)) = κ • l ν v) ∧
        (∀ v ∈ (R ν).sm, l' (ν + eZ I.1)
          (∑ c, pr I c (tm (R ν) (wedge (Formalism.QuantumDeterminants.fvec P.k P.r p.T.base.z')) v c)) = κ' • l' ν v) ∧
        t I.1 = (ep I : ℂ) * κ' * star κ * s ν / s (ν + eZ I.1)) := by
    intro ν
    by_cases hν : n1 ν + (P.r + 1) * (P.r + 2) ≤ q0
    swap
    · exact ⟨fun _ => 0, fun _ _ => rfl, fun h => absurd h hν⟩
    have hν1 : n1 ν + (P.r + 1) ≤ q0 := by nlinarith
    have hν0 : n1 ν ≤ q0 := by omega
    obtain ⟨io, pr, ep, hT⟩ := (GlobalTheory.T.pieri_tensor_decomposition hH P.k P.r lam P.u b bv ga h q0 R hNum hFam ν).1 (P.r + 1) hν1
    have hI : ∀ I : Sub (2 * P.r + P.k + 1) (P.r + 1), n1 (ν + eZ I.1) ≤ q0 := by
      intro I
      have h1 : n1 (ν + eZ I.1) ≤ n1 ν + I.1.card := by
        unfold n1 eZ
        calc ∑ i, ((ν + fun i => if i ∈ I.1 then (1 : ℤ) else 0) i).natAbs
            ≤ ∑ i, ((ν i).natAbs + if i ∈ I.1 then 1 else 0) := by
              refine Finset.sum_le_sum fun i _ => ?_
              simp only [Pi.add_apply]
              split_ifs <;> omega
          _ = ∑ i, (ν i).natAbs + I.1.card := by
              rw [Finset.sum_add_distrib]; simp
      rw [I.2] at h1
      omega
    have hk : ∀ I : Sub (2 * P.r + P.k + 1) (P.r + 1), ∃ κ κ' : ℂ, J ν ≠ 0 →
        (∀ v ∈ (R ν).sm, l (ν + eZ I.1)
          (∑ c, pr I c (tm (R ν) (wedge (Formalism.QuantumDeterminants.fvec P.k P.r p.T.base.z)) v c)) = κ • l ν v) ∧
        (∀ v ∈ (R ν).sm, l' (ν + eZ I.1)
          (∑ c, pr I c (tm (R ν) (wedge (Formalism.QuantumDeterminants.fvec P.k P.r p.T.base.z')) v c)) = κ' • l' ν v) := by
      intro I
      by_cases hJ : J ν = 0
      · exact ⟨0, 0, fun h => absurd hJ h⟩
      have hn : n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν) := by
        by_contra hc
        exact hJ (hz ν hc)
      obtain ⟨κ, hκ⟩ := (GlobalTheory.T.bessel_tensor_projection_scalar_and_adjoint hH P.k P.r _ _ _ _ (P.r + 1) (R ν)
        (fun I : Sub (2 * P.r + P.k + 1) (P.r + 1) => R (ν + eZ I.1)) io pr ep _ _ _ Wp
        p.T.base.z p.T.base.π P.u p.T.base.μW p.T.base.μN p.T.base.μG νq
        (wedge (Formalism.QuantumDeterminants.fvec P.k P.r p.T.base.z)) (l ν) (hFam ν hν0) (fun I => hFam _ (hI I))
        (GlobalTheory.WedgeFRep.isFRep_cmp P.k P.r (P.r + 1)) hT hS
        (fun g hg => (GlobalTheory.FlagFix.fixes_wedge_and_form P.k P.r _ hz1 g hg).1) (hL ν hν0).1 hn.2.1 I
        (l (ν + eZ I.1)) (hL _ (hI I)).1).1
      obtain ⟨κ', hκ'⟩ := (GlobalTheory.T.bessel_tensor_projection_scalar_and_adjoint hH P.k P.r _ _ _ _ (P.r + 1) (R ν)
        (fun I : Sub (2 * P.r + P.k + 1) (P.r + 1) => R (ν + eZ I.1)) io pr ep _ _ _ Wq
        p.T.base.z' p.T.base.π' P.u' p.T.base.μW' p.T.base.μN p.T.base.μG νq'
        (wedge (Formalism.QuantumDeterminants.fvec P.k P.r p.T.base.z')) (l' ν) (hFam ν hν0) (fun I => hFam _ (hI I))
        (GlobalTheory.WedgeFRep.isFRep_cmp P.k P.r (P.r + 1)) hT hS'
        (fun g hg => (GlobalTheory.FlagFix.fixes_wedge_and_form P.k P.r _ hz2 g hg).1) (hR ν hν0).1 hn.2.2 I
        (l' (ν + eZ I.1)) (hR _ (hI I)).1).1
      exact ⟨κ, κ', fun _ => ⟨hκ, hκ'⟩⟩
    choose κ κ' hκ using hk
    refine ⟨fun I => if hc : I.card = P.r + 1 ∧ J ν ≠ 0 ∧ J (ν + eZ I) ≠ 0 then
      (ep ⟨I, hc.1⟩ : ℂ) * κ' ⟨I, hc.1⟩ * star (κ ⟨I, hc.1⟩) * s ν / s (ν + eZ I) else 0, ?_, fun _ => ?_⟩
    · intro I hI0
      refine dif_neg ?_
      rintro ⟨-, h1, h2⟩
      exact hI0.elim h1 h2
    · refine ⟨io, pr, ep, hT, fun I h1 h2 => ⟨κ I, κ' I, (hκ I h1).1, (hκ I h1).2, ?_⟩⟩
      exact dif_pos (⟨I.2, h1, h2⟩ : I.1.card = P.r + 1 ∧ J ν ≠ 0 ∧ J (ν + eZ I.1) ≠ 0)
  choose tau h1 h2 using key
  exact ⟨tau, ⟨hFam, hL, hR, hco, hz, h1, h2⟩⟩

theorem suppliedData_exists : Hyps → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R0 : Rep P.k P.r) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (ν₀ : Fin (2 * P.r + P.k + 1) → ℤ), n1 ν₀ ≤ q0 → Num P.k P.r lam P.u b bv ga h q0 → R0.IsDS (PI.BesselPeriodGGP.eps48 P.k P.r) (fun a => lam a + (ν₀ a : ℝ)) → PI.CapelliEig.IsKFinCoefT (k := P.k) (r := P.r) R0.σ f → TBB.jN2 p f ≠ 0 → ∃ (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ) (t : ℝ), 0 < t ∧ J ν₀ = (fun g => (t : ℂ) • f g) ∧ Sup0 p lam q0 R l l' dg s J tau := by
  intro hH P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R0 f ν₀ h0 hN hR0 hf hj
  haveI := FiniteDimensional.complete ℂ Wp
  haveI := FiniteDimensional.complete ℂ Wq
  obtain ⟨R, hfam, hR⟩ := family_through_discreteSeries hH P.k P.r lam P.u b bv ga h q0 R0 ν₀ hN hR0
  subst hR
  obtain ⟨l, l', dg, hl, hl'⟩ := GlobalTheory.T.exists_family_functionals hH P Wp Wq p lam b bv ga h q0 R hN hfam
  have hK : PI.KFinSmooth := hH.1.2.2.1
  obtain ⟨s₀, hs₀⟩ := (GlobalTheory.T.capelli_k_finite_coefficient hK P.k P.r _ _ (R ν₀) Wp Wq (l ν₀) (l' ν₀) hR0).1 f hf
  obtain ⟨⟨-, -, -, -, hgap⟩, hnum⟩ := GlobalTheory.T.numericalFamily_shape_gaps P.k P.r lam P.u b bv ga h q0 hN
  have hg : Formalism.QuantumDeterminants.GapAtLeast (PI.BesselPeriodGGP.eps48 P.k P.r) (fun a => lam a + (ν₀ a : ℝ)) (h / 2) :=
    (hnum ν₀ h0).2.2.1
  obtain ⟨c, -, hc⟩ := GlobalTheory.T.bessel_setting_uniform_constant hH P.k P.r Wp Wq p.T.base
  have hne : s₀ ≠ 0 := by
    intro hz
    apply hj
    rw [GlobalTheory.T.jN2_eq_normSq_base P Wp Wq p f,
      hc _ _ (h / 2) (R ν₀) (l ν₀) (l' ν₀) (dg ν₀) hR0 hg hgap (hl ν₀ h0).1 (hl' ν₀ h0).1 (hl ν₀ h0).2.2 f s₀ hs₀, hz]
    simp
  obtain ⟨s, J, t, ht, hJ, -, hcoef, hzero⟩ :=
    exists_coef_family hH P Wp Wq p lam b bv ga h q0 R l l' dg f s₀ ν₀ h0 hfam hl hl' hs₀ hne
  obtain ⟨tau, htau⟩ :=
    exists_tau hH P Wp Wq p lam b bv ga h q0 R l l' dg s J hN hfam hl hl' hcoef hzero
  exact ⟨R, l, l', dg, s, J, tau, t, ht, hJ, htau⟩

theorem sup_norm : Hyps → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ), Num P.k P.r lam P.u b bv ga h q0 → Sup0 p lam q0 R l l' dg s J tau → ∃ c : ℝ, 0 < c ∧ ∀ ν, n1 ν ≤ q0 → (J ν = 0 ∧ TBB.jN2 p (J ν) = 0 ∧ ¬ (NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν))) ∨ (J ν ≠ 0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν) ∧ s ν ≠ 0 ∧ TBB.jN2 p (J ν) = ENNReal.ofReal (c * Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ)))) := by
  intro hy P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R l l' dg s J tau hN hS
  haveI := FiniteDimensional.complete ℂ Wp
  haveI := FiniteDimensional.complete ℂ Wq
  obtain ⟨c₁, hc₁, h1⟩ := GlobalTheory.T.bessel_setting_uniform_constant hy P.k P.r Wp Wq p.T.base
  have hH : PI.BesselPeriodGGP.IsHaarOn (GG P.k P.r) p.T.base.μG := by
    haveI : IsFiniteMeasureOnCompacts p.T.base.μG := ⟨fun K hK => p.T.base.haarG.finite_compact K hK⟩
    haveI : IsLocallyFiniteMeasure p.T.base.μG := inferInstance
    exact ⟨inferInstance, p.T.base.haarG.ne_zero, p.T.base.haarG.conc, p.T.base.haarG.left⟩
  obtain ⟨c₂, hc₂, h2⟩ := GlobalTheory.BesselDegree.schur_fdeg hy P.k P.r (PI.BesselPeriodGGP.eps48 P.k P.r) _ hH
  obtain ⟨⟨-, -, -, -, hgap⟩, hfam⟩ := GlobalTheory.NumFam.num_fam P.k P.r lam P.u b bv ga h q0 hN
  refine ⟨c₁ * c₂, mul_pos hc₁ hc₂, fun ν hν => ?_⟩
  have hDS := hS.fam ν hν
  obtain ⟨hl, hdg, hfd⟩ := hS.left ν hν
  obtain ⟨hl', -, -⟩ := hS.right ν hν
  have hP := h1 _ _ (h / 2) (R ν) (l ν) (l' ν) (dg ν) hDS (hfam ν hν).2.2.1 hgap hl hl' hfd
  have h0 : TBB.jN2 p (0 : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) = 0 := by
    rw [GlobalTheory.T.jN2_eq_normSq_base, hP 0 0 ⟨0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun g _ => by simp, by simp⟩]
    simp
  by_cases hnz : NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)
  · right
    obtain ⟨hc, hs⟩ := hS.coef ν hν hnz.1 hnz.2
    have hj : TBB.jN2 p (J ν) = ENNReal.ofReal (c₁ * dg ν) := by
      rw [GlobalTheory.T.jN2_eq_normSq_base, hP _ _ hc, hs]
      congr 1
      field_simp
    obtain ⟨w, hw, -⟩ := (GlobalTheory.rep_basic_of_isDS hy.1.2.2.1 P.k P.r _ _ (R ν) hDS).2.2.2.2.2.2.2.1
    have hw0 : w ≠ 0 := by
      rintro rfl
      simp at hw
    have hd : dg ν = c₂ * Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ)) := by
      rw [← hfd w hw0, (h2 _ (R ν) hDS).1 w hw0]
    refine ⟨?_, hnz.1, hnz.2, ?_, ?_⟩
    · intro hJ
      rw [hJ, h0] at hj
      exact absurd hj.symm (ENNReal.ofReal_pos.2 (mul_pos hc₁ hdg)).ne'
    · intro hs0
      rw [hs0, norm_zero] at hs
      exact hdg.ne hs
    · rw [hj, hd, mul_assoc]
  · left
    have hJ := hS.zero ν (fun hh => hnz hh.2)
    exact ⟨hJ, by rw [hJ, h0], hnz⟩

theorem coef_norm_finite_and_zero : Hyps → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R0 : Rep P.k P.r) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (ν₀ : Fin (2 * P.r + P.k + 1) → ℤ), n1 ν₀ ≤ q0 → Num P.k P.r lam P.u b bv ga h q0 → R0.IsDS (PI.BesselPeriodGGP.eps48 P.k P.r) (fun a => lam a + (ν₀ a : ℝ)) → PI.CapelliEig.IsKFinCoefT (k := P.k) (r := P.r) R0.σ f → TBB.jN2 p f < ⊤ ∧ (AEMeasurable fun c : Fin (P.r + 1) → ℂ => ENNReal.ofReal (TBB.Ew p (fun _ => 1) f (P.r + 1) [] (TBB.bigPt P.r c))) ∧ (TBB.jN2 p f = 0 → ∀ c : Fin (P.r + 1) → ℂ, D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) → p.V f (TBB.bigPt P.r c) = 0) := by
  intro hH P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R0 f ν₀ h0 hN hR0 hf
  haveI := FiniteDimensional.complete ℂ Wp
  haveI := FiniteDimensional.complete ℂ Wq
  obtain ⟨R, hfam, hR⟩ := family_through_discreteSeries hH P.k P.r lam P.u b bv ga h q0 R0 ν₀ hN hR0
  subst hR
  obtain ⟨l, l', dg, hl, hl'⟩ := GlobalTheory.T.exists_family_functionals hH P Wp Wq p lam b bv ga h q0 R hN hfam
  obtain ⟨hB, hdg, hfd⟩ := hl ν₀ h0
  obtain ⟨hB', -, -⟩ := hl' ν₀ h0
  obtain ⟨⟨-, -, -, -, hok⟩, hν⟩ := GlobalTheory.NumFam.num_fam P.k P.r lam P.u b bv ga h q0 hN
  have hgap : Formalism.QuantumDeterminants.GapAtLeast (PI.BesselPeriodGGP.eps48 P.k P.r) (fun a => lam a + (ν₀ a : ℝ)) (h / 2) :=
    (hν ν₀ h0).2.2.1
  obtain ⟨s, hs⟩ := (GlobalTheory.isCoef_of_translate_smul_exists hH.1.2.2.1 P.k P.r _ _ (R ν₀) Wp Wq (l ν₀) (l' ν₀) hR0).1 f hf
  obtain ⟨c, hc, hnorm⟩ := GlobalTheory.T.bessel_setting_uniform_constant hH P.k P.r Wp Wq p.T.base
  have hj : TBB.jN2 p f = ENNReal.ofReal (c * ‖s‖ ^ 2 / dg ν₀) := by
    rw [GlobalTheory.T.jN2_eq_normSq_base]
    exact hnorm _ _ (h / 2) (R ν₀) (l ν₀) (l' ν₀) (dg ν₀) hR0 hgap hok hB hB' hfd f s hs
  have hck := (GlobalTheory.T.smooth_and_inCC_of_isCoef_of_gap hH P.k P.r _ _ (h / 2) (R ν₀) Wp Wq (l ν₀) (l' ν₀) f s hR0 hgap hok hs).1
  refine ⟨by rw [hj]; exact ENNReal.ofReal_lt_top,
    GlobalTheory.T.aemeasurable_besselNormIntegrand_bigCell P Wp Wq p f (GlobalTheory.CoefZero.continuousOn_of_ckOn hck), fun hz x hx hG => ?_⟩
  have hs0 : s = 0 := by
    by_contra hne
    rw [hj, ENNReal.ofReal_eq_zero] at hz
    have hpos : 0 < ‖s‖ := norm_pos_iff.mpr hne
    have : 0 < c * ‖s‖ ^ 2 / dg ν₀ := by positivity
    linarith
  obtain ⟨γ, hγ, -, hV⟩ := GlobalTheory.T.exists_regularRep_besselBigCellVector_eq_bessel P Wp Wq p x hx hG
  obtain ⟨OO, hOO⟩ := GlobalTheory.T.bessel_orbital_integral_integrable_and_eq_smul hH P.k P.r _ _ (h / 2) (R ν₀) Wp Wq p.T.base (l ν₀) (l' ν₀) hR0 hgap hok hB hB'
  rw [hV f, (hOO f s hs γ hγ).2, hs0, zero_smul]

theorem sup_meas : Hyps → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ), Num P.k P.r lam P.u b bv ga h q0 → Sup0 p lam q0 R l l' dg s J tau → ∀ ν, AEMeasurable fun c : Fin (P.r + 1) → ℂ => ENNReal.ofReal (TBB.Ew p (fun _ => 1) (J ν) (P.r + 1) [] (TBB.bigPt P.r c)) := by
  intro _ P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R l l' dg s J tau _ hS ν
  apply GlobalTheory.T.aemeasurable_besselNormIntegrand_bigCell
  by_cases hν : n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)
  · exact GlobalTheory.SupMeas.isCoef_continuousOn (hS.fam ν hν.1) (hS.coef ν hν.1 hν.2.1 hν.2.2).1
  · rw [hS.zero ν hν]
    exact continuousOn_const

theorem tau_bound : Hyps → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ), Num P.k P.r lam P.u b bv ga h q0 → Num P.k P.r lam P.u' b bv ga h q0 → Sup0 p lam q0 R l l' dg s J tau → ∀ ν, n1 ν + (P.r + 1) * (P.r + 2) ≤ q0 → ∀ I : Finset (Fin (2 * P.r + P.k + 1)), I.card = P.r + 1 → ‖tau ν I‖ ≤ Real.sqrt (Hsq P.r P.T b * Hsq P.r P.T' b) ^ (P.r + 1) := by
  intro hyp P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R l l' dg s J tau hN hN' hS ν hν I hI
  classical
  haveI := FiniteDimensional.complete ℂ Wp
  haveI := FiniteDimensional.complete ℂ Wq
  by_cases hz : J ν = 0 ∨ J (ν + eZ I) = 0
  · rw [hS.tau_zero ν I hz, norm_zero]
    positivity
  rw [not_or] at hz
  have h1 : n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν) := by
    by_contra hc
    exact hz.1 (hS.zero ν hc)
  have h2 : n1 (ν + eZ I) ≤ q0 ∧ NzOn (R (ν + eZ I)) (l (ν + eZ I)) ∧ NzOn (R (ν + eZ I)) (l' (ν + eZ I)) := by
    by_contra hc
    exact hz.2 (hS.zero _ hc)
  obtain ⟨-, -, -, hT, hT', hty, hty'⟩ := p.hP
  obtain ⟨νq, νq', hG, hG'⟩ := GlobalTheory.T.besselDatum_both_sides_are_sides P.k P.r Wp Wq p.T.base P.u P.u' hty hty'
  obtain ⟨io, pr, ep, hTens, hκ⟩ := hS.tau_eq ν hν
  obtain ⟨κ, κ', hk, hk', ht⟩ := hκ ⟨I, hI⟩ hz.1 hz.2
  have b1 := GlobalTheory.T.wedge_raising_scalar_sq_mul_degree_ratio_le hyp P.k P.r Wp lam P.u b bv ga h q0 _ _ _ _ _ νq R l dg
    ⟨hN, hS.fam, hG, hS.left⟩ ν hν io pr ep hTens h1.2.1 ⟨I, hI⟩ κ h2.2.1 hk
  have b2 := GlobalTheory.T.wedge_raising_scalar_sq_mul_degree_ratio_le hyp P.k P.r Wq lam P.u' b bv ga h q0 _ _ _ _ _ νq' R l' dg
    ⟨hN', hS.fam, hG', hS.right⟩ ν hν io pr ep hTens h1.2.2 ⟨I, hI⟩ κ' h2.2.2 hk'
  rw [hT] at b1
  rw [hT'] at b2
  have s1 := (hS.coef ν h1.1 h1.2.1 h1.2.2).2
  have s2 := (hS.coef _ h2.1 h2.2.1 h2.2.2).2
  have d1 := (hS.left ν h1.1).2.1
  have d2 := (hS.left _ h2.1).2.1
  have hep : ‖(ep ⟨I, hI⟩ : ℂ)‖ = 1 := by
    rcases hTens.ep_sq ⟨I, hI⟩ with h | h <;> simp [h]
  have ht' : tau ν I = (ep ⟨I, hI⟩ : ℂ) * κ' * star κ * s ν / s (ν + eZ I) := ht
  rw [ht', norm_div, norm_mul, norm_mul, norm_mul, hep, one_mul, norm_star, s1, s2]
  exact GlobalTheory.SupTau.arith _ _ _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) d1 d2 (GlobalTheory.SupTau.hsq_nonneg _ _ _) (GlobalTheory.SupTau.hsq_nonneg _ _ _) b1 b2

theorem supplied_pieri : Hyps → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ), Num P.k P.r lam P.u b bv ga h q0 → Sup0 p lam q0 R l l' dg s J tau → ∀ ν, n1 ν + (P.r + 1) * (P.r + 2) ≤ q0 → ∀ c : Fin (P.r + 1) → ℂ, D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) → (D.ptMatN (TBB.bigPt P.r c) (P.r + 1)).det • p.V (J ν) (TBB.bigPt P.r c) = ∑ I ∈ powersetCard (P.r + 1) (univ : Finset (Fin (2 * P.r + P.k + 1))), tau ν I • p.V (J (ν + eZ I)) (TBB.bigPt P.r c) := by
  intro H P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R l l' dg s J tau hN hS ν hν c hc hG
  haveI := FiniteDimensional.complete ℂ Wp
  haveI := FiniteDimensional.complete ℂ Wq
  obtain ⟨γ, hγ, hZ, hV⟩ := GlobalTheory.T.exists_regularRep_besselBigCellVector_eq_bessel P Wp Wq p c hc hG
  simp only [hV]
  by_cases hJ : J ν = 0
  · rw [hJ, GlobalTheory.SuppliedPieri.JF_zero, smul_zero]
    symm
    refine Finset.sum_eq_zero fun I _ => ?_
    rw [hS.tau_zero ν I (Or.inl hJ), zero_smul]
  obtain ⟨c0, -, hdich⟩ := sup_norm H P Wp Wq p lam b bv ga h q0 R l l' dg s J tau hN hS
  obtain ⟨⟨-, -, -, -, hGap⟩, hfam⟩ := GlobalTheory.NumFam.num_fam P.k P.r lam P.u b bv ga h q0 hN
  have hν0 : n1 ν ≤ q0 := by omega
  have hνI : ∀ I : Sub (2 * P.r + P.k + 1) (P.r + 1), n1 (ν + eZ I.1) ≤ q0 := by
    intro I
    have h1 := GlobalTheory.SuppliedPieri.n1_add_eZ_le ν I.1
    rw [I.2] at h1
    have h2 : P.r + 1 ≤ (P.r + 1) * (P.r + 2) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  obtain ⟨io, pr, ep, hT, htau⟩ := hS.tau_eq ν hν
  have hnz : NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν) := by
    by_contra hcon
    exact hJ (hS.zero ν fun hh => hcon hh.2)
  have key := GlobalTheory.T.tensor_weighted_bessel_gap H P.k P.r (Sub (2 * P.r + P.k + 1) (P.r + 1)) (Sub (2 * P.r + P.k + 1) (P.r + 1))
    (cmp (P.r + 1)) (cmp (P.r + 1) (Formalism.QuantumDeterminants.Hpk P.k P.r)) (P.r + 1) (R ν) (fun I => R (ν + eZ I.1)) io pr ep
    (PI.BesselPeriodGGP.eps48 P.k P.r) (fun a => lam a + (ν a : ℝ))
    (fun I a => lam a + ((ν + eZ I.1) a : ℝ)) (h / 2) Wp Wq p.T.base
    (wedge (Formalism.QuantumDeterminants.fvec P.k P.r p.T.base.z)) (wedge (Formalism.QuantumDeterminants.fvec P.k P.r p.T.base.z'))
    (l ν) (l' ν) (fun I => l (ν + eZ I.1)) (fun I => l' (ν + eZ I.1)) (J ν) (s ν)
    (fun I => J (ν + eZ I.1)) (fun I => s (ν + eZ I.1)) (fun I => tau ν I.1)
    (hS.fam ν hν0) (hfam ν hν0).2.2.1
    (fun I => ⟨hS.fam _ (hνI I), (hfam _ (hνI I)).2.2.1⟩) hGap
    (GlobalTheory.WedgeFRep.isFRep_cmp P.k P.r (P.r + 1)) hT
    (fun g hg => (GlobalTheory.FlagFix.fixes_wedge_and_form P.k P.r _ p.T.base.z_mem g hg).1)
    (fun g hg => (GlobalTheory.FlagFix.fixes_wedge_and_form P.k P.r _ p.T.base.z'_mem g hg).1)
    (fun I => ⟨(hS.left _ (hνI I)).1, (hS.right _ (hνI I)).1⟩)
    (hS.coef ν hν0 hnz.1 hnz.2).1
    (fun I => by
      rcases hdich _ (hνI I) with ⟨h0, -, hn⟩ | ⟨h0, hn, hn', hs, -⟩
      · exact Or.inl ⟨not_and_or.mp hn, hS.tau_zero ν I.1 (Or.inr h0)⟩
      · exact Or.inr ⟨(hS.coef _ (hνI I) hn hn').1, hs, htau I hJ h0⟩)
    γ hγ
  rw [GlobalTheory.TopMinorWedge.herm_cmp_wedge_eq_det, hZ] at key
  rw [key]
  symm
  exact Finset.sum_subtype _ (fun I => by simp) (fun I => tau ν I • B.JF p.T.base (J (ν + eZ I)) γ)

theorem wave_ball_estimate (H : Hyps) (C : ℝ) (hC : 0 ≤ C) (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 a₁ : ℕ)
    (R0 : Rep P.k P.r) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (ν₀ : Fin (2 * P.r + P.k + 1) → ℤ)
    (hN : Num P.k P.r lam P.u b bv ga h q0) (hN' : Num P.k P.r lam P.u' b bv ga h q0)
    (hT : P.T ≤ b ^ (C * ((2 * P.r + 2 : ℕ) : ℝ))) (hT' : P.T' ≤ b ^ (C * ((2 * P.r + 2 : ℕ) : ℝ)))
    (hq : n1 ν₀ + (P.r + 1) * a₁ + (P.r + 1) * (P.r + 2) ≤ q0)
    (hDS : R0.IsDS (PI.BesselPeriodGGP.eps48 P.k P.r) (fun a => lam a + (ν₀ a : ℝ)))
    (hf : haveI := FiniteDimensional.complete ℂ Wp; PI.CapelliEig.IsKFinCoefT (k := P.k) (r := P.r) R0.σ f) :
    Formalism.FourierDecayAlt.P.CutBP.FamilyDerivativeExpansion p f b (C / 2 + 6) a₁ := by
  obtain ⟨⟨hbv, hbv', hn', -, -⟩, -⟩ := GlobalTheory.NumFam.num_fam _ _ _ _ _ _ _ _ _ hN
  have hb : 2 ≤ b := by linarith
  have hν₀ : n1 ν₀ ≤ q0 := by omega
  obtain ⟨hfin, hmeas, hz⟩ := coef_norm_finite_and_zero H P Wp Wq p lam b bv ga h q0 R0 f ν₀ hν₀ hN hDS hf
  by_cases h0 : TBB.jN2 p f = 0
  · exact GlobalTheory.T.familyDerivativeExpansion_of_V_eq_zero P Wp Wq p f b _ a₁ (by linarith) hmeas (hz h0)
  obtain ⟨R, l, l', dg, s, J, tau, t, ht, hJ, hS⟩ :=
    suppliedData_exists H P Wp Wq p lam b bv ga h q0 R0 f ν₀ hν₀ hN hDS hf h0
  have hn : ∀ μ : Fin (2 * P.r + P.k + 1) → ℤ, n1 μ ≤ Formalism.FourierDecayAlt.P.CutBP.LatticeNorms.N1 (μ - ν₀) + n1 ν₀ := fun μ => by
    have e : Formalism.FourierDecayAlt.P.CutBP.LatticeNorms.N1 (μ - ν₀ + ν₀) ≤ _ := Formalism.FourierDecayAlt.P.CutBP.LatticeNorms.n1_add_le (μ - ν₀) ν₀
    rw [sub_add_cancel] at e
    exact e
  let d : Formalism.FourierDecayAlt.P.CutBP.PieriExpansionData P Wp Wq :=
    ⟨(2 * P.r + P.k + 1), J, ν₀, tau, (P.r + 1) * (P.r + 2), q0 - n1 ν₀, Real.sqrt (Hsq P.r P.T b * Hsq P.r P.T' b)⟩
  have hP : Formalism.FourierDecayAlt.P.CutBP.PieriExpansion p d := fun μ hμ c hc hG =>
    supplied_pieri H P Wp Wq p lam b bv ga h q0 R l l' dg s J tau hN hS μ
      (by have := hn μ; dsimp only [d] at hμ; omega) c hc hG
  have hTau : Formalism.FourierDecayAlt.P.CutBP.PieriCoefficientBound d := fun μ hμ I hI =>
    tau_bound H P Wp Wq p lam b bv ga h q0 R l l' dg s J tau hN hN' hS μ
      (by have := hn μ; dsimp only [d] at hμ; omega) I (Finset.mem_powersetCard.1 hI).2
  have hD : Formalism.FourierDecayAlt.P.CutBP.PieriDegreeConditions p d := by
    obtain ⟨c, hc, key⟩ := sup_norm H P Wp Wq p lam b bv ga h q0 R l l' dg s J tau hN hS
    have hdeg := GlobalTheory.FamilyDegreeRatio.degree_ratios P.k P.r lam P.u b bv ga h q0 hN
    dsimp only [d]
    refine ⟨?_, ?_, ?_⟩
    · show 0 < TBB.jN2 p (J ν₀)
      rw [hJ, Formalism.FourierDecayAlt.P.CutBP.norm_sq_const_smul]
      refine ENNReal.mul_pos ?_ h0
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      exact pow_pos (norm_pos_iff.2 (Complex.ofReal_ne_zero.2 ht.ne')) 2
    · intro μ hμ
      have hμ' : n1 μ ≤ q0 := by have := hn μ; dsimp only at hμ; omega
      show TBB.jN2 p (J μ) < ⊤ ∧ (TBB.jN2 p (J μ) = 0 → ∀ c : Fin (P.r + 1) → ℂ,
        D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) → p.V (J μ) (TBB.bigPt P.r c) = 0)
      rcases key μ hμ' with ⟨hJ, hz, -⟩ | ⟨-, -, -, -, he⟩
      · refine ⟨by rw [hz]; exact ENNReal.zero_lt_top, fun _ x _ _ => ?_⟩
        have e : J μ = fun g => (0 : ℂ) • J μ g := by
          funext g
          rw [hJ, zero_smul]
          rfl
        rw [e, Formalism.FourierDecayAlt.P.CutBP.V_csmul, zero_smul]
      · refine ⟨by rw [he]; exact ENNReal.ofReal_lt_top, fun hz => ?_⟩
        rw [he] at hz
        exact absurd hz (ENNReal.ofReal_pos.2 (mul_pos hc (hdeg μ hμ').1)).ne'
    · intro μ hμ hne I hI
      have hμ1 : n1 μ + (P.r + 1) * (P.r + 2) ≤ q0 := by have := hn μ; dsimp only at hμ; omega
      have hμ' : n1 μ ≤ q0 := le_trans (Nat.le_add_right _ _) hμ1
      have hcard : I.card = P.r + 1 := (mem_powersetCard.1 hI).2
      have hν : n1 (μ + eZ I) ≤ q0 := by
        have e1 : n1 (μ + eZ I) ≤ n1 μ + Formalism.FourierDecayAlt.P.CutBP.LatticeNorms.N1 (Formalism.FourierDecayAlt.P.CutBP.LatticeNorms.eI I) :=
          Formalism.FourierDecayAlt.P.CutBP.LatticeNorms.n1_add_le μ (Formalism.FourierDecayAlt.P.CutBP.LatticeNorms.eI I)
        rw [Formalism.FourierDecayAlt.P.CutBP.LatticeNorms.n1_eI_eq_card, hcard] at e1
        have e2 : P.r + 1 ≤ (P.r + 1) * (P.r + 2) := Nat.le_mul_of_pos_right _ (by omega)
        omega
      change TBB.jN2 p (J μ) ≠ 0 at hne
      show TBB.jN2 p (J (μ + eZ I)) ≤
        ENNReal.ofReal ((Real.exp 1 * ((2 * P.r + P.k + 1 : ℕ) : ℝ)) ^ (P.r + 1)) * TBB.jN2 p (J μ)
      rcases key μ hμ' with ⟨-, hz, -⟩ | ⟨-, -, -, -, he⟩
      · exact absurd hz hne
      rcases key _ hν with ⟨-, hz, -⟩ | ⟨-, -, -, -, he'⟩
      · rw [hz]; exact zero_le
      rw [he, he', ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      obtain ⟨hpos, hrat, -⟩ := hdeg μ hμ'
      have e1 := hrat I
      rw [hcard] at e1
      have e2 : ((2 * P.r + P.k + 1) : ℝ) ^ (P.r + 1) ≤ (Real.exp 1 * ((2 * P.r + P.k + 1 : ℕ) : ℝ)) ^ (P.r + 1) := by
        refine pow_le_pow_left₀ (by positivity) ?_ _
        push_cast
        exact le_mul_of_one_le_left (by positivity) (Real.one_le_exp zero_le_one)
      have e3 := e1.trans (mul_le_mul_of_nonneg_right e2 hpos.le)
      calc _ ≤ c * (_ * _) := mul_le_mul_of_nonneg_left e3 hc.le
        _ = _ := by ring

  have hM := sup_meas H P Wp Wq p lam b bv ga h q0 R l l' dg s J tau hN hS
  have hH := GlobalTheory.TopNum.top_num P.r P.T P.T' b C hC hb hT hT'
  have hE := Formalism.FourierDecayAlt.P.CutBP.family_expansion_of_parts p (Formalism.FourierDecayAlt.P.CutBP.unitF p (J ν₀)) b (C / 2 + 6) a₁ d
    rfl (Real.sqrt_nonneg _) (Nat.le_mul_of_pos_right _ (by omega)) (by dsimp only [d]; omega)
    (Formalism.FourierDecayAlt.P.CutBP.coefficient_growth_le_power _ P.r b _ (C + 10) _ hb (by dsimp only [d]; push_cast; exact hn') (Real.sqrt_nonneg _) hH (by linarith))
    hP hTau hD hM
  have hpos : 0 < TBB.jN2 p (J ν₀) := hD.1
  have hlt : TBB.jN2 p (J ν₀) < ⊤ := (hD.2.1 ν₀ (by simp [Formalism.FourierDecayAlt.P.CutBP.LatticeNorms.N1, d])).1
  have hsc : Formalism.FourierDecayAlt.P.CutBP.scF p (J ν₀) ≠ 0 := by
    unfold Formalism.FourierDecayAlt.P.CutBP.scF
    exact inv_ne_zero (Real.sqrt_pos.2 (ENNReal.toReal_pos hpos.ne' hlt.ne)).ne'
  have hE' := GlobalTheory.T.bigCellExpansion_smul P Wp Wq p _ b _ a₁ (((Formalism.FourierDecayAlt.P.CutBP.scF p (J ν₀) : ℂ) * (t : ℂ))⁻¹) hE
  have hne : ((Formalism.FourierDecayAlt.P.CutBP.scF p (J ν₀) : ℂ) * (t : ℂ)) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.2 hsc) (Complex.ofReal_ne_zero.2 ht.ne')
  have e : (fun g => (((Formalism.FourierDecayAlt.P.CutBP.scF p (J ν₀) : ℂ) * (t : ℂ))⁻¹) • Formalism.FourierDecayAlt.P.CutBP.unitF p (J ν₀) g) = f := by
    funext g
    have hg : J ν₀ g = (t : ℂ) • f g := congrFun hJ g
    unfold Formalism.FourierDecayAlt.P.CutBP.unitF
    rw [hg, smul_smul, smul_smul, mul_assoc, inv_mul_cancel₀ hne, one_smul]
  rw [e] at hE'
  exact hE'

theorem wave_ball_estimate_dual (H : Hyps) (C : ℝ) (hC : 0 ≤ C) (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 a₁ : ℕ)
    (R0 : Rep P.k P.r) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (ν₀ : Fin (2 * P.r + P.k + 1) → ℤ)
    (hN : Num P.k P.r lam P.u b bv ga h q0) (hN' : Num P.k P.r lam P.u' b bv ga h q0)
    (hT : P.T ≤ b ^ (C * ((2 * P.r + 2 : ℕ) : ℝ))) (hT' : P.T' ≤ b ^ (C * ((2 * P.r + 2 : ℕ) : ℝ)))
    (hq : n1 ν₀ + (P.r + 1) * a₁ + (P.r + 1) * (P.r + 2) ≤ q0)
    (hDS : R0.IsDS (PI.BesselPeriodGGP.eps48 P.k P.r) (fun a => lam a + (ν₀ a : ℝ)))
    (hf : haveI := FiniteDimensional.complete ℂ Wp; PI.CapelliEig.IsKFinCoefT (k := P.k) (r := P.r) R0.σ f) :
    Formalism.FourierDecayAlt.P.CutBP.BigCellDerivativeExpansion p f b (C / 2 + 6) a₁ := by
  have hb := (GlobalTheory.NumFam.num_fam P.k P.r lam P.u b bv ga h q0 hN).1
  exact Formalism.FourierDecayAlt.P.CutBP.big_cell_expansion_of_family p f b (C / 2 + 6) a₁ (by linarith [hb.1, hb.2.1])
    (wave_ball_estimate H C hC P Wp Wq p lam b bv ga h q0 a₁ R0 f ν₀ hN hN' hT hT' hq hDS hf)

end CompanionTheory.WaveGrid.Ball
