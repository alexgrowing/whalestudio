import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorMomentEstimateStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.PieriTensorDecompositionStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselSettingUniformConstantStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DiscreteSeriesUnitarySmoothBasic
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.HaarEqSmul
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupMomentClosureStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorWeightedBesselGapStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilyFunctionalSpanDualStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.CapelliKFiniteCoefficient
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ExistsKTypeNonzeroBessel
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselSettingGapDecayStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselPeriodAdjointPairStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ExistsFamilyFunctionalsStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilyThroughDiscreteSeries
import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilyFunctionalCoefficient
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilyFunctionalSpan
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsCoefContinuousOn
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.HsqNonneg
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.N1AddEZLe
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BaseRepCapelliEigenDual
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupMomentClosure
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupMomentRecursion
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.ProductMoment

namespace GlobalTheory
end GlobalTheory

open GlobalTheory BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open CompanionTheory.WaveGrid CompanionTheory.WaveGrid.BallW
open CompanionTheory.WaveGrid.MomL (fvL mnr momL SupL fixes_wedge herm_wedge length_wedge meas_mnr ew_sum_le)
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Gp91.WG

section sup

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

structure Sup0 (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (q0 : ℕ)
    (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq)
    (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ)
    (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ) : Prop where
  fam : IsFamG lam q0 R
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

theorem family_through_discreteSeries : HypsG → ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ)
    (b bv ga h : ℝ) (q0 : ℕ) (R0 : Rep k r) (ν₀ : Fin (2 * r + k + 1) → ℤ), Num k r lam u b bv ga h q0 →
    R0.IsDG (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν₀ a : ℝ)) →
    ∃ R : (Fin (2 * r + k + 1) → ℤ) → Rep k r, IsFamG lam q0 R ∧ R ν₀ = R0 := by
  intro hH k r lam u b bv ga h q0 R0 ν₀ hN hR0
  classical
  have hex : DSExistG := hH.2.2.2.1
  have hC : ∃ P, PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) P := by
    obtain ⟨P, hP, -⟩ := hR0.2
    exact ⟨P, hP⟩
  have hfam := (GlobalTheory.T.numericalFamily_shape_gaps k r lam u b bv ga h q0 hN).2
  have key : ∀ ν : Fin (2 * r + k + 1) → ℤ, ∃ R : Rep k r,
      (∑ a, (ν a).natAbs ≤ q0 → R.IsDG (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ))) ∧
      (ν = ν₀ → R = R0) := by
    intro ν
    by_cases h0 : ν = ν₀
    · refine ⟨R0, fun _ => ?_, fun _ => rfl⟩
      subst h0
      exact hR0
    · by_cases hq : ∑ a, (ν a).natAbs ≤ q0
      · obtain ⟨R, hR⟩ := hex k r _ _ (hfam ν hq).1 hC
          ⟨h / 2, (hfam ν hq).2.2.1, (GlobalTheory.T.numericalFamily_shape_gaps k r lam u b bv ga h q0 hN).1.2.2.2.2⟩
        exact ⟨R, fun _ => hR, fun h => absurd h h0⟩
      · exact ⟨R0, fun h => absurd h hq, fun _ => rfl⟩
  choose R hR using key
  exact ⟨R, fun ν hν => (hR ν).1 hν, (hR ν₀).2 rfl⟩

theorem exists_coef_family : HypsG → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (s₀ : ℂ) (ν₀ : Fin (2 * P.r + P.k + 1) → ℤ), n1 ν₀ ≤ q0 → IsFamG lam q0 R → (haveI := FiniteDimensional.complete ℂ Wp; SideFam p.T.base.z p.T.base.π p.T.base.μW p.T.base.μN p.T.base.μG q0 R l dg) → (haveI := FiniteDimensional.complete ℂ Wq; SideFam p.T.base.z' p.T.base.π' p.T.base.μW' p.T.base.μN p.T.base.μG q0 R l' dg) → IsCoef (R ν₀) (l ν₀) (l' ν₀) f s₀ → s₀ ≠ 0 → ∃ (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (t : ℝ), 0 < t ∧ J ν₀ = (fun g => (t : ℂ) • f g) ∧ (NzOn (R ν₀) (l ν₀) ∧ NzOn (R ν₀) (l' ν₀)) ∧ (∀ ν, n1 ν ≤ q0 → NzOn (R ν) (l ν) → NzOn (R ν) (l' ν) → IsCoef (R ν) (l ν) (l' ν) (J ν) (s ν) ∧ ‖s ν‖ = dg ν) ∧ (∀ ν, ¬ (n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)) → J ν = 0) := by
  intro hH P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R l l' dg f s₀ ν₀ h0 hfam hL hR hf hs₀
  haveI := FiniteDimensional.complete ℂ Wp
  haveI := FiniteDimensional.complete ℂ Wq
  classical
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hDS : ∀ ν, n1 ν ≤ q0 → (R ν).IsDG (PI.BesselPeriodGGP.eps48 P.k P.r) (fun a => lam a + (ν a : ℝ)) :=
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

theorem exists_tau : HypsG → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)), Num P.k P.r lam P.u b bv ga h q0 → IsFamG lam q0 R → (haveI := FiniteDimensional.complete ℂ Wp; SideFam p.T.base.z p.T.base.π p.T.base.μW p.T.base.μN p.T.base.μG q0 R l dg) → (haveI := FiniteDimensional.complete ℂ Wq; SideFam p.T.base.z' p.T.base.π' p.T.base.μW' p.T.base.μN p.T.base.μG q0 R l' dg) → (∀ ν, n1 ν ≤ q0 → NzOn (R ν) (l ν) → NzOn (R ν) (l' ν) → IsCoef (R ν) (l ν) (l' ν) (J ν) (s ν) ∧ ‖s ν‖ = dg ν) → (∀ ν, ¬ (n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)) → J ν = 0) → ∃ tau, Sup0 p lam q0 R l l' dg s J tau := by
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

theorem sup_norm : HypsG → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ), Num P.k P.r lam P.u b bv ga h q0 → Sup0 p lam q0 R l l' dg s J tau → ∃ c : ℝ, 0 < c ∧ ∀ ν, n1 ν ≤ q0 → (J ν = 0 ∧ TBB.jN2 p (J ν) = 0 ∧ ¬ (NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν))) ∨ (J ν ≠ 0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν) ∧ s ν ≠ 0 ∧ TBB.jN2 p (J ν) = ENNReal.ofReal (c * Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ)))) := by
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

theorem sup_meas : HypsG → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ), Num P.k P.r lam P.u b bv ga h q0 → Sup0 p lam q0 R l l' dg s J tau → ∀ ν, AEMeasurable fun c : Fin (P.r + 1) → ℂ => ENNReal.ofReal (TBB.Ew p (fun _ => 1) (J ν) (P.r + 1) [] (TBB.bigPt P.r c)) := by
  intro _ P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R l l' dg s J tau _ hS ν
  apply GlobalTheory.T.aemeasurable_besselNormIntegrand_bigCell
  by_cases hν : n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)
  · exact GlobalTheory.SupMeas.isCoef_continuousOn (hS.fam ν hν.1) (hS.coef ν hν.1 hν.2.1 hν.2.2).1
  · rw [hS.zero ν hν]
    exact continuousOn_const

theorem tau_bound : HypsG → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ), Num P.k P.r lam P.u b bv ga h q0 → Num P.k P.r lam P.u' b bv ga h q0 → Sup0 p lam q0 R l l' dg s J tau → ∀ ν, n1 ν + (P.r + 1) * (P.r + 2) ≤ q0 → ∀ I : Finset (Fin (2 * P.r + P.k + 1)), I.card = P.r + 1 → ‖tau ν I‖ ≤ Real.sqrt (Hsq P.r P.T b * Hsq P.r P.T' b) ^ (P.r + 1) := by
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

theorem supplied_pieri : HypsG → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ), Num P.k P.r lam P.u b bv ga h q0 → Sup0 p lam q0 R l l' dg s J tau → ∀ ν, n1 ν + (P.r + 1) * (P.r + 2) ≤ q0 → ∀ c : Fin (P.r + 1) → ℂ, D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) → (D.ptMatN (TBB.bigPt P.r c) (P.r + 1)).det • p.V (J ν) (TBB.bigPt P.r c) = ∑ I ∈ powersetCard (P.r + 1) (univ : Finset (Fin (2 * P.r + P.k + 1))), tau ν I • p.V (J (ν + eZ I)) (TBB.bigPt P.r c) := by
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

theorem suppliedData_existsW : HypsG → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R0 : Rep P.k P.r) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (ν₀ : Fin (2 * P.r + P.k + 1) → ℤ), n1 ν₀ ≤ q0 → Num P.k P.r lam P.u b bv ga h q0 → R0.IsDG (PI.BesselPeriodGGP.eps48 P.k P.r) (fun a => lam a + (ν₀ a : ℝ)) → CoefOf R0 f → TBB.jN2 p f ≠ 0 → ∃ (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ) (t : ℝ), 0 < t ∧ J ν₀ = (fun g => (t : ℂ) • f g) ∧ Sup0 p lam q0 R l l' dg s J tau := by
  intro hH P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R0 f ν₀ h0 hN hR0 hf hj
  haveI := FiniteDimensional.complete ℂ Wp
  haveI := FiniteDimensional.complete ℂ Wq
  obtain ⟨R, hfam, hR⟩ := family_through_discreteSeries hH P.k P.r lam P.u b bv ga h q0 R0 ν₀ hN hR0
  subst hR
  obtain ⟨l, l', dg, hl, hl'⟩ := GlobalTheory.T.exists_family_functionals hH P Wp Wq p lam b bv ga h q0 R hN hfam
  have hK : PI.KFinSmooth := hH.1.2.2.1
  obtain ⟨s₀, hs₀⟩ := hf (l ν₀) (l' ν₀)
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

theorem coef_norm_finite_and_zeroW : HypsG → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R0 : Rep P.k P.r) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (ν₀ : Fin (2 * P.r + P.k + 1) → ℤ), n1 ν₀ ≤ q0 → Num P.k P.r lam P.u b bv ga h q0 → R0.IsDG (PI.BesselPeriodGGP.eps48 P.k P.r) (fun a => lam a + (ν₀ a : ℝ)) → CoefOf R0 f → TBB.jN2 p f < ⊤ ∧ (AEMeasurable fun c : Fin (P.r + 1) → ℂ => ENNReal.ofReal (TBB.Ew p (fun _ => 1) f (P.r + 1) [] (TBB.bigPt P.r c))) ∧ (TBB.jN2 p f = 0 → ∀ c : Fin (P.r + 1) → ℂ, D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) → p.V f (TBB.bigPt P.r c) = 0) := by
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
  obtain ⟨s, hs⟩ := hf (l ν₀) (l' ν₀)
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

theorem familyDerivativeExpansion_of_isDS_of_coefOf (H : HypsG) (C : ℝ) (hC : 0 ≤ C) (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 a₁ : ℕ)
    (R0 : Rep P.k P.r) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (ν₀ : Fin (2 * P.r + P.k + 1) → ℤ)
    (hN : Num P.k P.r lam P.u b bv ga h q0) (hN' : Num P.k P.r lam P.u' b bv ga h q0)
    (hT : P.T ≤ b ^ (C * ((2 * P.r + 2 : ℕ) : ℝ))) (hT' : P.T' ≤ b ^ (C * ((2 * P.r + 2 : ℕ) : ℝ)))
    (hq : n1 ν₀ + (P.r + 1) * a₁ + (P.r + 1) * (P.r + 2) ≤ q0)
    (hDS : R0.IsDG (PI.BesselPeriodGGP.eps48 P.k P.r) (fun a => lam a + (ν₀ a : ℝ)))
    (hf : CoefOf R0 f) :
    Formalism.FourierDecayAlt.P.CutBP.FamilyDerivativeExpansion p f b (C / 2 + 6) a₁ := by
  obtain ⟨⟨hbv, hbv', hn', -, -⟩, -⟩ := GlobalTheory.NumFam.num_fam _ _ _ _ _ _ _ _ _ hN
  have hb : 2 ≤ b := by linarith
  have hν₀ : n1 ν₀ ≤ q0 := by omega
  obtain ⟨hfin, hmeas, hz⟩ := coef_norm_finite_and_zeroW H P Wp Wq p lam b bv ga h q0 R0 f ν₀ hν₀ hN hDS hf
  by_cases h0 : TBB.jN2 p f = 0
  · exact GlobalTheory.T.familyDerivativeExpansion_of_V_eq_zero P Wp Wq p f b _ a₁ (by linarith) hmeas (hz h0)
  obtain ⟨R, l, l', dg, s, J, tau, t, ht, hJ, hS⟩ :=
    suppliedData_existsW H P Wp Wq p lam b bv ga h q0 R0 f ν₀ hν₀ hN hDS hf h0
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

theorem bigCellDerivativeExpansion_of_isDS_of_coefOf (H : HypsG) (C : ℝ) (hC : 0 ≤ C) (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 a₁ : ℕ)
    (R0 : Rep P.k P.r) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (ν₀ : Fin (2 * P.r + P.k + 1) → ℤ)
    (hN : Num P.k P.r lam P.u b bv ga h q0) (hN' : Num P.k P.r lam P.u' b bv ga h q0)
    (hT : P.T ≤ b ^ (C * ((2 * P.r + 2 : ℕ) : ℝ))) (hT' : P.T' ≤ b ^ (C * ((2 * P.r + 2 : ℕ) : ℝ)))
    (hq : n1 ν₀ + (P.r + 1) * a₁ + (P.r + 1) * (P.r + 2) ≤ q0)
    (hDS : R0.IsDG (PI.BesselPeriodGGP.eps48 P.k P.r) (fun a => lam a + (ν₀ a : ℝ)))
    (hf : CoefOf R0 f) :
    Formalism.FourierDecayAlt.P.CutBP.BigCellDerivativeExpansion p f b (C / 2 + 6) a₁ := by
  have hb := (GlobalTheory.NumFam.num_fam P.k P.r lam P.u b bv ga h q0 hN).1
  exact Formalism.FourierDecayAlt.P.CutBP.big_cell_expansion_of_family p f b (C / 2 + 6) a₁ (by linarith [hb.1, hb.2.1])
    (familyDerivativeExpansion_of_isDS_of_coefOf H C hC P Wp Wq p lam b bv ga h q0 a₁ R0 f ν₀ hN hN' hT hT' hq hDS hf)

set_option maxHeartbeats 400000 in

theorem product_moment : HypsG → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), SetupG lam u b bv ga h q0 z π μW μN μG νq R l dg → ∀ (j : ℕ) (hj : j ≤ r) ν, n1 ν + (r + 1) ^ 2 ≤ q0 → NzOn (R ν) (l ν) → ∃ w ∈ (R ν).sm, ‖w‖ = 1 ∧ ∫⁻ x, ENNReal.ofReal ((∏ a : Fin (j + 1), lenA k r z (Matrix.of x) (Fin.castLE (Nat.succ_le_succ hj) a) ^ 2) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ (r + 1)) := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg hS j hj ν hν hnz
  classical
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hNum := hS.1
  have hFam := hS.2.1
  have hSide := hS.2.2.1
  have hSF := hS.2.2.2
  have hk : 1 ≤ k := hNum.1
  have hν0 : n1 ν ≤ q0 := le_trans (Nat.le_add_right _ _) hν
  obtain ⟨Q, hQ⟩ := (GlobalTheory.CayleyChoice.cayley_exists_and_any k r).1 hk
  have hQu : IsUnit Q := hQ.1.1
  have hE : ∀ ν', ∃ E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν').smSub,
      n1 ν' ≤ q0 → (R ν').IsE Q E ∧ Formalism.REAL.GlRel E := by
    intro ν'
    by_cases h' : n1 ν' ≤ q0
    · obtain ⟨E, hE⟩ := GlobalTheory.T.smoothVectors_discreteSeries_glModule hK k r _ _ (R ν') (hFam ν' h') Q hQu
      exact ⟨E, fun _ => hE⟩
    · exact ⟨fun _ _ => 0, fun h'' => absurd h'' h'⟩
  choose E hE using hE
  have hDS := hFam ν hν0
  obtain ⟨w, hw1, -, hwK, hwF⟩ := GlobalTheory.T.exists_lowest_kFinite_vector_discreteSeries hK k r _ _ (R ν) hDS Q (E ν) hQ (hE ν hν0).1
  have hMod := GlobalTheory.T.cayley_endomorphisms_modular hH k r _ _ (R ν) hk hDS Q (E ν) hQ (hE ν hν0).1
  have hLev := GlobalTheory.lev_zero_of_kHighest _ _ _ (E ν) _ w hMod.1 hMod.2.1 hwK hwF
  have hw1' : ‖(w : (R ν).H)‖ = 1 := hw1
  have hwsm : (w : (R ν).H) ∈ (R ν).sm := w.2
  refine ⟨(w : (R ν).H), hwsm, hw1', ?_⟩
  obtain ⟨hG, -, hlen, hmeas⟩ := GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r _ _ (R ν) Wp z π u μW μN μG νq hDS hSide
  obtain ⟨hBeL, hdg, -⟩ := hSF ν hν0
  have hT : 0 < Formalism.QuantumDeterminants.Tz k r z := hSide.2.1
  obtain ⟨⟨hb1, hb2, -, -, -⟩, -⟩ := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hNum
  have hq2 : ∀ q ≤ (r + 1) ^ 2, 0 + 2 * q ≤ 4 * (2 * r + k + 1) ^ 2 := by
    intro q hq
    have : (r + 1) ^ 2 ≤ (2 * r + k + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hb : (1 : ℝ) ≤ b := by linarith
  have e0 : Fin.castLE (Nat.succ_le_succ hj) (0 : Fin (j + 1)) = 0 := rfl
  have e1 : ∀ a : Fin j, Fin.castLE (Nat.succ_le_succ hj) a.succ = (Fin.castLE hj a).succ := fun _ => rfl
  have e2 : ∀ a : Fin j, Fin.castLE (Nat.succ_le_succ hj) a.castSucc = (Fin.castLE hj a).castSucc := fun _ => rfl
  have hjr : (j + 1) ^ 2 ≤ (r + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hA : 0 ≤ (((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) := by
    have : 0 ≤ bv := by linarith
    positivity
  have hmain := GlobalTheory.T.product_moment_bound_density_mass_one (Formalism.QuantumDeterminants.Mt k r) νq j (fun a x => lenA k r z (Matrix.of x) (Fin.castLE (Nat.succ_le_succ hj) a))
    (fun x => dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)
    (((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) (b ^ 2)
    (fun a => hlen (Fin.castLE (Nat.succ_le_succ hj) a))
    (fun a => hG.mono fun x hx => (GlobalTheory.TensLen.lengths k r z hSide.1 hT _ hx).2.2.1 (Fin.castLE (Nat.succ_le_succ hj) a))
    (((hmeas (l ν) hBeL.1 w hwsm).norm.aemeasurable.pow_const 2).const_mul _)
    (fun x => mul_nonneg hdg.le (by positivity))
    (by
      have := ((GlobalTheory.T.bessel_functional_l2_bound_and_isometry hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν0).2 hnz).2 w hwsm
      simpa only [one_mul, hw1', one_pow, ENNReal.ofReal_one] using this)
    hA (one_le_pow₀ hb)
    (fun q hq => by
      have := GlobalTheory.T.family_setup_cayley_recursion hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE q ν
        (by omega) 0 (hq2 q (hq.trans hjr)) w hLev
      rw [← e0] at this
      simpa only [hw1, one_pow, mul_one] using this)
    (fun a q hq => by
      have := GlobalTheory.T.family_setup_cayley_bound hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE ν hν0
        0 q (hq2 q (hq.trans hjr)) (Fin.castLE hj a) w hLev
      rw [← e1, ← e2] at this
      simpa only [hw1, one_pow, mul_one] using this)
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  have h1 : (b ^ 2) ^ (2 * j) ≤ (b ^ 2) ^ (2 * r) := pow_le_pow_right₀ (one_le_pow₀ hb) (by omega)
  have h2 := (mul_le_mul_of_nonneg_left h1 hA).trans (GlobalTheory.T.numericalFamily_productBound_constant_le k r lam u b bv ga h q0 _ hNum hT)
  have h3 : 1 ≤ Hsq r (Formalism.QuantumDeterminants.Tz k r z) b := one_le_mul_of_one_le_of_one_le (le_max_left _ _) (one_le_pow₀ hb)
  exact (pow_le_pow_left₀ (mul_nonneg hA (by positivity)) h2 _).trans (pow_le_pow_right₀ h3 (by omega))

theorem kappa_bound : HypsG → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), SetupG lam u b bv ga h q0 z π μW μN μG νq R l dg → ∀ (j : ℕ) (hj : j ≤ r) ν, n1 ν + (r + 1) * (r + 2) ≤ q0 → ∀ io pr ep, TensH (cmp (j + 1)) (cmp (j + 1) (Formalism.QuantumDeterminants.Hpk k r)) (R ν) (fun I : Sub (2 * r + k + 1) (j + 1) => R (ν + eZ I.1)) io pr ep → NzOn (R ν) (l ν) → ∀ (I : Sub (2 * r + k + 1) (j + 1)) (κ₀ : ℂ), NzOn (R (ν + eZ I.1)) (l (ν + eZ I.1)) → (∀ v ∈ (R ν).sm, l (ν + eZ I.1) (∑ c, pr I c (tm (R ν) (wedge (fvL hj z)) v c)) = κ₀ • l ν v) → ‖κ₀‖ ^ 2 * dg ν / dg (ν + eZ I.1) ≤ Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ (r + 1) := by
  intro hyp k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg hS j hj ν hν io pr ep hT hnz I κ₀ hnzI hκ
  classical
  have hS' := hS
  obtain ⟨hNum, hFam, hG, hSF⟩ := hS'
  have hν0 : n1 ν ≤ q0 := by omega
  have hνJ : ∀ J : Sub (2 * r + k + 1) (j + 1), n1 (ν + eZ J.1) + (r + 1) ^ 2 ≤ q0 := by
    intro J
    have := GlobalTheory.WedgeKappa.n1_add_eZ_le_add_card ν J.1
    rw [J.2] at this
    nlinarith
  have hνJ0 : ∀ J : Sub (2 * r + k + 1) (j + 1), n1 (ν + eZ J.1) ≤ q0 := fun J =>
    le_trans (Nat.le_add_right _ _) (hνJ J)
  have hDS := hFam ν hν0
  have hDSJ := fun J : Sub (2 * r + k + 1) (j + 1) => hFam (ν + eZ J.1) (hνJ0 J)
  have hF := GlobalTheory.WedgeFRep.isFRep_cmp k r (j + 1)
  have hdual := fun J : Sub (2 * r + k + 1) (j + 1) =>
    GlobalTheory.T.bessel_tensor_projection_scalar_and_adjoint hyp k r _ _ _ _ _ (R ν) _ io pr ep _ _ _ Wp z π u μW μN μG νq
      (wedge (fvL hj z)) (l ν) hDS hDSJ hF hT hG
      (fun s hs => fixes_wedge hj hG.1 s hs) (hSF ν hν0).1 hnz J
      (l (ν + eZ J.1)) (hSF _ (hνJ0 J)).1
  have hex : ∀ J : Sub (2 * r + k + 1) (j + 1), ∃ c : ℂ, (J = I → c = κ₀) ∧
      ∀ y ∈ (R (ν + eZ J.1)).sm, l ν (ev (cmp (j + 1) (Formalism.QuantumDeterminants.Hpk k r)) (R ν) (wedge (fvL hj z))
        (fun c => io J c y)) = ((ep J : ℂ) * star c) • l (ν + eZ J.1) y := by
    intro J
    by_cases hJ : J = I
    · subst hJ
      exact ⟨κ₀, fun _ => rfl, (hdual J).2 κ₀ hκ⟩
    · obtain ⟨c, hc⟩ := (hdual J).1
      exact ⟨c, fun h => absurd h hJ, (hdual J).2 c hc⟩
  choose κ hκI hκd using hex
  have hd0 : 0 < dg ν := (hSF ν hν0).2.1
  have hdJ : ∀ J : Sub (2 * r + k + 1) (j + 1), 0 < dg (ν + eZ J.1) := fun J => (hSF _ (hνJ0 J)).2.1
  have hmass := GlobalTheory.T.bessel_functional_l2_bound_and_isometry hyp k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS
  obtain ⟨w, hw, hw1, hint⟩ := product_moment hyp k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS j hj _ (hνJ I) hnzI
  have hinj : Function.Injective (fun (J : Sub (2 * r + k + 1) (j + 1)) (a : Fin (2 * r + k + 1)) =>
      lam a + (((ν + eZ J.1) a : ℤ) : ℝ)) := by
    intro J J' hJ
    apply Subtype.ext
    apply GlobalTheory.WedgeKappa.eZ_injective
    funext a
    have := congrFun hJ a
    simp only [Pi.add_apply, add_right_inj, Int.cast_inj] at this
    exact this
  have h8 := GlobalTheory.T.tensor_moment_weighted hyp k r _ _ _ _ _ (R ν) _ io pr ep _ _ _ Wp z π u μW μN μG νq
    (wedge (fvL hj z)) (fun w => ((Real.sqrt (dg ν) : ℝ) : ℂ) • l ν w)
    (fun J w => ((Real.sqrt (dg (ν + eZ J.1)) : ℝ) : ℂ) • l (ν + eZ J.1) w)
    (fun J => if NzOn (R (ν + eZ J.1)) (l (ν + eZ J.1)) then
      (ep J : ℂ) * star (κ J) * ((Real.sqrt (dg ν) : ℝ) : ℂ) / ((Real.sqrt (dg (ν + eZ J.1)) : ℝ) : ℂ) else 0)
    hDS hDSJ hinj hF hT hG ((hmass ν hν0).2 hnz).1
    (fun J => by
      by_cases hJ : NzOn (R (ν + eZ J.1)) (l (ν + eZ J.1))
      · exact Or.inl ((hmass _ (hνJ0 J)).2 hJ).1
      · exact Or.inr (if_neg hJ))
    (fun J y hy => by
      rw [hκd J y hy]
      by_cases hJ : NzOn (R (ν + eZ J.1)) (l (ν + eZ J.1))
      · rw [if_pos hJ, smul_smul, smul_smul]
        congr 1
        have : ((Real.sqrt (dg (ν + eZ J.1)) : ℝ) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hdJ J)).ne'
        field_simp
      · have : l (ν + eZ J.1) y = 0 := by
          by_contra hne
          exact hJ ⟨y, hy, hne⟩
        rw [if_neg hJ, this]
        simp)
    I ((hmass _ (hνJ0 I)).2 hnzI).1 w hw
  have hae := (GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hyp.1.2.2.1 k r _ _ (R ν) Wp z π u μW μN μG νq hDS hG).1
  rw [if_pos hnzI, hκI I rfl, hw1] at h8
  have h9 := h8.trans (le_trans (le_of_eq (lintegral_congr_ae ?_)) hint)
  · have hH : 0 ≤ Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ (r + 1) := by
      apply pow_nonneg
      unfold Hsq
      apply mul_nonneg (le_trans zero_le_one (le_max_left _ _))
      rw [show 20 * (r + 1) = 2 * (10 * (r + 1)) by ring, pow_mul]
      positivity
    rw [ENNReal.ofReal_le_ofReal_iff hH] at h9
    refine le_trans (le_of_eq ?_) h9
    have hep : ‖(ep I : ℂ)‖ = 1 := by
      rcases hT.ep_sq I with h | h <;> simp [h]
    rw [norm_div, norm_mul, norm_mul, hep, norm_star, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, div_pow, mul_pow, sq_abs, sq_abs, Real.sq_sqrt hd0.le, Real.sq_sqrt (hdJ I).le]
    ring
  · filter_upwards [hae] with x hx
    rw [length_wedge hj z _, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, Real.sq_sqrt (hdJ I).le]

theorem exists_tauL : HypsG → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)), ∀ tau₀, Num P.k P.r lam P.u b bv ga h q0 → Sup0 p lam q0 R l l' dg s J tau₀ → ∀ (j : ℕ) (hj : j ≤ P.r), ∃ tau, SupL p q0 R l l' s J j hj tau := by
  intro hH P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R l l' dg s J tau₀ hNum hS0 j hj
  have hFam := hS0.fam
  have hL := hS0.left
  have hR := hS0.right
  have hz := hS0.zero
  classical
  haveI := FiniteDimensional.complete ℂ Wp
  haveI := FiniteDimensional.complete ℂ Wq
  obtain ⟨-, hz1, hz2, -, -, ht1, ht2⟩ := p.hP
  obtain ⟨νq, νq', hS, hS'⟩ := GlobalTheory.T.besselDatum_both_sides_are_sides P.k P.r Wp Wq p.T.base P.u P.u' ht1 ht2
  have key : ∀ ν, ∃ t : Finset (Fin (2 * P.r + P.k + 1)) → ℂ,
      (∀ I, J ν = 0 ∨ J (ν + eZ I) = 0 → t I = 0) ∧
      (n1 ν + (P.r + 1) * (P.r + 2) ≤ q0 →
    ∃ io pr ep, TensH (cmp (j + 1)) (cmp (j + 1) (Formalism.QuantumDeterminants.Hpk P.k P.r)) (R ν)
        (fun I : Sub (2 * P.r + P.k + 1) (j + 1) => R (ν + eZ I.1)) io pr ep ∧
      ∀ I : Sub (2 * P.r + P.k + 1) (j + 1), J ν ≠ 0 → J (ν + eZ I.1) ≠ 0 → ∃ κ κ' : ℂ,
        (∀ v ∈ (R ν).sm, l (ν + eZ I.1)
          (∑ c, pr I c (tm (R ν) (wedge (fvL hj p.T.base.z)) v c)) = κ • l ν v) ∧
        (∀ v ∈ (R ν).sm, l' (ν + eZ I.1)
          (∑ c, pr I c (tm (R ν) (wedge (fvL hj p.T.base.z')) v c)) = κ' • l' ν v) ∧
        t I.1 = (ep I : ℂ) * κ' * star κ * s ν / s (ν + eZ I.1)) := by
    intro ν
    by_cases hν : n1 ν + (P.r + 1) * (P.r + 2) ≤ q0
    swap
    · exact ⟨fun _ => 0, fun _ _ => rfl, fun h => absurd h hν⟩
    have hν1 : n1 ν + (j + 1) ≤ q0 := by nlinarith
    have hν0 : n1 ν ≤ q0 := by omega
    obtain ⟨io, pr, ep, hT⟩ := (GlobalTheory.T.pieri_tensor_decomposition hH P.k P.r lam P.u b bv ga h q0 R hNum hFam ν).1 (j + 1) hν1
    have hI : ∀ I : Sub (2 * P.r + P.k + 1) (j + 1), n1 (ν + eZ I.1) ≤ q0 := by
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
    have hk : ∀ I : Sub (2 * P.r + P.k + 1) (j + 1), ∃ κ κ' : ℂ, J ν ≠ 0 →
        (∀ v ∈ (R ν).sm, l (ν + eZ I.1)
          (∑ c, pr I c (tm (R ν) (wedge (fvL hj p.T.base.z)) v c)) = κ • l ν v) ∧
        (∀ v ∈ (R ν).sm, l' (ν + eZ I.1)
          (∑ c, pr I c (tm (R ν) (wedge (fvL hj p.T.base.z')) v c)) = κ' • l' ν v) := by
      intro I
      by_cases hJ : J ν = 0
      · exact ⟨0, 0, fun h => absurd hJ h⟩
      have hn : n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν) := by
        by_contra hc
        exact hJ (hz ν hc)
      obtain ⟨κ, hκ⟩ := (GlobalTheory.T.bessel_tensor_projection_scalar_and_adjoint hH P.k P.r _ _ _ _ (j + 1) (R ν)
        (fun I : Sub (2 * P.r + P.k + 1) (j + 1) => R (ν + eZ I.1)) io pr ep _ _ _ Wp
        p.T.base.z p.T.base.π P.u p.T.base.μW p.T.base.μN p.T.base.μG νq
        (wedge (fvL hj p.T.base.z)) (l ν) (hFam ν hν0) (fun I => hFam _ (hI I))
        (GlobalTheory.WedgeFRep.isFRep_cmp P.k P.r (j + 1)) hT hS
        (fun g hg => fixes_wedge hj hz1 g hg) (hL ν hν0).1 hn.2.1 I
        (l (ν + eZ I.1)) (hL _ (hI I)).1).1
      obtain ⟨κ', hκ'⟩ := (GlobalTheory.T.bessel_tensor_projection_scalar_and_adjoint hH P.k P.r _ _ _ _ (j + 1) (R ν)
        (fun I : Sub (2 * P.r + P.k + 1) (j + 1) => R (ν + eZ I.1)) io pr ep _ _ _ Wq
        p.T.base.z' p.T.base.π' P.u' p.T.base.μW' p.T.base.μN p.T.base.μG νq'
        (wedge (fvL hj p.T.base.z')) (l' ν) (hFam ν hν0) (fun I => hFam _ (hI I))
        (GlobalTheory.WedgeFRep.isFRep_cmp P.k P.r (j + 1)) hT hS'
        (fun g hg => fixes_wedge hj hz2 g hg) (hR ν hν0).1 hn.2.2 I
        (l' (ν + eZ I.1)) (hR _ (hI I)).1).1
      exact ⟨κ, κ', fun _ => ⟨hκ, hκ'⟩⟩
    choose κ κ' hκ using hk
    refine ⟨fun I => if hc : I.card = j + 1 ∧ J ν ≠ 0 ∧ J (ν + eZ I) ≠ 0 then
      (ep ⟨I, hc.1⟩ : ℂ) * κ' ⟨I, hc.1⟩ * star (κ ⟨I, hc.1⟩) * s ν / s (ν + eZ I) else 0, ?_, fun _ => ?_⟩
    · intro I hI0
      refine dif_neg ?_
      rintro ⟨-, h1, h2⟩
      exact hI0.elim h1 h2
    · refine ⟨io, pr, ep, hT, fun I h1 h2 => ⟨κ I, κ' I, (hκ I h1).1, (hκ I h1).2, ?_⟩⟩
      exact dif_pos (⟨I.2, h1, h2⟩ : I.1.card = j + 1 ∧ J ν ≠ 0 ∧ J (ν + eZ I.1) ≠ 0)
  choose tau h1 h2 using key
  exact ⟨tau, ⟨h1, h2⟩⟩

theorem tau_boundL : HypsG → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (tau₀ : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ), Num P.k P.r lam P.u b bv ga h q0 → Num P.k P.r lam P.u' b bv ga h q0 → Sup0 p lam q0 R l l' dg s J tau₀ → ∀ (j : ℕ) (hj : j ≤ P.r) tau, SupL p q0 R l l' s J j hj tau → ∀ ν, n1 ν + (P.r + 1) * (P.r + 2) ≤ q0 → ∀ I : Finset (Fin (2 * P.r + P.k + 1)), I.card = j + 1 → ‖tau ν I‖ ≤ Real.sqrt (Hsq P.r P.T b * Hsq P.r P.T' b) ^ (P.r + 1) := by
  intro hyp P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R l l' dg s J tau₀ hN hN' hS j hj tau hSL ν hν I hI
  classical
  haveI := FiniteDimensional.complete ℂ Wp
  haveI := FiniteDimensional.complete ℂ Wq
  by_cases hz : J ν = 0 ∨ J (ν + eZ I) = 0
  · rw [hSL.tau_zero ν I hz, norm_zero]
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
  obtain ⟨io, pr, ep, hTens, hκ⟩ := hSL.tau_eq ν hν
  obtain ⟨κ, κ', hk, hk', ht⟩ := hκ ⟨I, hI⟩ hz.1 hz.2
  have b1 := kappa_bound hyp P.k P.r Wp lam P.u b bv ga h q0 _ _ _ _ _ νq R l dg
    ⟨hN, hS.fam, hG, hS.left⟩ j hj ν hν io pr ep hTens h1.2.1 ⟨I, hI⟩ κ h2.2.1 hk
  have b2 := kappa_bound hyp P.k P.r Wq lam P.u' b bv ga h q0 _ _ _ _ _ νq' R l' dg
    ⟨hN', hS.fam, hG', hS.right⟩ j hj ν hν io pr ep hTens h1.2.2 ⟨I, hI⟩ κ' h2.2.2 hk'
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

theorem supplied_pieriL : HypsG → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (tau₀ : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ), Num P.k P.r lam P.u b bv ga h q0 → Sup0 p lam q0 R l l' dg s J tau₀ → ∀ (j : ℕ) (hj : j ≤ P.r) tau, SupL p q0 R l l' s J j hj tau → ∀ ν, n1 ν + (P.r + 1) * (P.r + 2) ≤ q0 → ∀ c : Fin (P.r + 1) → ℂ, D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) → mnr hj (TBB.bigPt P.r c) • p.V (J ν) (TBB.bigPt P.r c) = ∑ I ∈ powersetCard (j + 1) (univ : Finset (Fin (2 * P.r + P.k + 1))), tau ν I • p.V (J (ν + eZ I)) (TBB.bigPt P.r c) := by
  intro H P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R l l' dg s J tau₀ hN hS j hj tau hSL ν hν c hc hG
  haveI := FiniteDimensional.complete ℂ Wp
  haveI := FiniteDimensional.complete ℂ Wq
  obtain ⟨γ, hγ, hZ, hV⟩ := GlobalTheory.T.exists_regularRep_besselBigCellVector_eq_bessel P Wp Wq p c hc hG
  simp only [hV]
  by_cases hJ : J ν = 0
  · rw [hJ, GlobalTheory.SuppliedPieri.JF_zero, smul_zero]
    symm
    refine Finset.sum_eq_zero fun I _ => ?_
    rw [hSL.tau_zero ν I (Or.inl hJ), zero_smul]
  obtain ⟨c0, -, hdich⟩ := sup_norm H P Wp Wq p lam b bv ga h q0 R l l' dg s J tau₀ hN hS
  obtain ⟨⟨-, -, -, -, hGap⟩, hfam⟩ := GlobalTheory.NumFam.num_fam P.k P.r lam P.u b bv ga h q0 hN
  have hν0 : n1 ν ≤ q0 := by omega
  have hνI : ∀ I : Sub (2 * P.r + P.k + 1) (j + 1), n1 (ν + eZ I.1) ≤ q0 := by
    intro I
    have h1 := GlobalTheory.SuppliedPieri.n1_add_eZ_le ν I.1
    rw [I.2] at h1
    have h2 : P.r + 1 ≤ (P.r + 1) * (P.r + 2) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  obtain ⟨io, pr, ep, hT, htau⟩ := hSL.tau_eq ν hν
  have hnz : NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν) := by
    by_contra hcon
    exact hJ (hS.zero ν fun hh => hcon hh.2)
  have key := GlobalTheory.T.tensor_weighted_bessel_gap H P.k P.r (Sub (2 * P.r + P.k + 1) (j + 1)) (Sub (2 * P.r + P.k + 1) (j + 1))
    (cmp (j + 1)) (cmp (j + 1) (Formalism.QuantumDeterminants.Hpk P.k P.r)) (j + 1) (R ν) (fun I => R (ν + eZ I.1)) io pr ep
    (PI.BesselPeriodGGP.eps48 P.k P.r) (fun a => lam a + (ν a : ℝ))
    (fun I a => lam a + ((ν + eZ I.1) a : ℝ)) (h / 2) Wp Wq p.T.base
    (wedge (fvL hj p.T.base.z)) (wedge (fvL hj p.T.base.z'))
    (l ν) (l' ν) (fun I => l (ν + eZ I.1)) (fun I => l' (ν + eZ I.1)) (J ν) (s ν)
    (fun I => J (ν + eZ I.1)) (fun I => s (ν + eZ I.1)) (fun I => tau ν I.1)
    (hS.fam ν hν0) (hfam ν hν0).2.2.1
    (fun I => ⟨hS.fam _ (hνI I), (hfam _ (hνI I)).2.2.1⟩) hGap
    (GlobalTheory.WedgeFRep.isFRep_cmp P.k P.r (j + 1)) hT
    (fun g hg => fixes_wedge hj p.T.base.z_mem g hg)
    (fun g hg => fixes_wedge hj p.T.base.z'_mem g hg)
    (fun I => ⟨(hS.left _ (hνI I)).1, (hS.right _ (hνI I)).1⟩)
    (hS.coef ν hν0 hnz.1 hnz.2).1
    (fun I => by
      rcases hdich _ (hνI I) with ⟨h0, -, hn⟩ | ⟨h0, hn, hn', hs, -⟩
      · exact Or.inl ⟨not_and_or.mp hn, hSL.tau_zero ν I.1 (Or.inr h0)⟩
      · exact Or.inr ⟨(hS.coef _ (hνI I) hn hn').1, hs, htau I hJ h0⟩)
    γ hγ
  rw [herm_wedge hj, hZ] at key
  unfold mnr
  rw [key]
  symm
  exact Finset.sum_subtype _ (fun I => by simp) (fun I => tau ν I • B.JF p.T.base (J (ν + eZ I)) γ)

theorem momL_le (H : HypsG) (C : ℝ) (hC : 0 ≤ C) (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 a : ℕ)
    (R0 : Rep P.k P.r) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (j : ℕ) (hj : j ≤ P.r)
    (hN : Num P.k P.r lam P.u b bv ga h q0) (hN' : Num P.k P.r lam P.u' b bv ga h q0)
    (hT : P.T ≤ b ^ (C * ((2 * P.r + 2 : ℕ) : ℝ))) (hT' : P.T' ≤ b ^ (C * ((2 * P.r + 2 : ℕ) : ℝ)))
    (hq : (P.r + 1) * a + (P.r + 1) * (P.r + 2) ≤ q0)
    (hDS : R0.IsDG (PI.BesselPeriodGGP.eps48 P.k P.r) lam)
    (hf : BallW.CoefOf R0 f) :
    momL p f hj a ≤ ENNReal.ofReal (b ^ ((C + 12) * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * a)) * TBB.jN2 p f := by
  classical
  obtain ⟨⟨hbv, hbv', hn', -, -⟩, -⟩ := GlobalTheory.NumFam.num_fam _ _ _ _ _ _ _ _ _ hN
  have hb : 2 ≤ b := by linarith
  have h00 : n1 (0 : Fin (2 * P.r + P.k + 1) → ℤ) ≤ q0 := by simp [n1]
  have hDS0 : R0.IsDG (PI.BesselPeriodGGP.eps48 P.k P.r) (fun s => lam s + ((0 : Fin (2 * P.r + P.k + 1) → ℤ) s : ℝ)) := by
    simpa using hDS
  obtain ⟨-, -, hz⟩ := coef_norm_finite_and_zeroW H P Wp Wq p lam b bv ga h q0 R0 f 0 h00 hN hDS0 hf
  by_cases h0 : TBB.jN2 p f = 0
  · refine le_trans (le_of_eq ?_) bot_le
    refine (lintegral_congr fun c => ?_).trans lintegral_zero
    have e := ew_sum_le p f (∅ : Finset Unit) (fun _ => f) (fun _ => 0) 1 (TBB.bigPt P.r c)
      (fun h1 h2 => by rw [hz h0 c h1 h2]; simp)
    simp only [norm_one, one_pow, one_mul, Finset.sum_empty, mul_zero] at e
    exact ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by positivity) e)
  obtain ⟨R, l, l', dg, s, J, tau₀, t, ht, hJ, hS⟩ :=
    suppliedData_existsW H P Wp Wq p lam b bv ga h q0 R0 f 0 h00 hN hDS0 hf h0
  obtain ⟨tau, hSL⟩ := exists_tauL H P Wp Wq p lam b bv ga h q0 R l l' dg s J tau₀ hN hS j hj
  obtain ⟨c₀, hc₀, key⟩ := sup_norm H P Wp Wq p lam b bv ga h q0 R l l' dg s J tau₀ hN hS
  have hdeg := GlobalTheory.FamilyDegreeRatio.degree_ratios P.k P.r lam P.u b bv ga h q0 hN
  have hM := sup_meas H P Wp Wq p lam b bv ga h q0 R l l' dg s J tau₀ hN hS
  have hH := GlobalTheory.TopNum.top_num P.r P.T P.T' b C hC hb hT hT'
  set S := powersetCard (j + 1) (univ : Finset (Fin (2 * P.r + P.k + 1))) with hSd
  set Hh : ℝ := Real.sqrt (Hsq P.r P.T b * Hsq P.r P.T' b) ^ (P.r + 1) with hHh
  set X : ℝ := b ^ (P.r + 1) with hX
  have hX1 : 1 ≤ X := one_le_pow₀ (by linarith)
  have hH0 : 0 ≤ Hh := by positivity
  have hnj : ((2 * P.r + P.k + 1 : ℝ)) ^ (j + 1) ≤ X :=
    (pow_le_pow_left₀ (by positivity) hn' _).trans (pow_le_pow_right₀ (by linarith) (by omega))
  have hcard : (S.card : ℝ) ≤ X := by
    refine le_trans ?_ hnj
    rw [hSd, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast Nat.choose_le_pow _ _
  have main : ∀ (a : ℕ) (ν : Fin (2 * P.r + P.k + 1) → ℤ), n1 ν + (P.r + 1) * a + (P.r + 1) * (P.r + 2) ≤ q0 →
      momL p (J ν) hj a ≤ ENNReal.ofReal ((X ^ 3 * Hh ^ 2) ^ a) * TBB.jN2 p (J ν) := by
    intro a
    induction a with
    | zero =>
      intro ν _
      simp [momL, TBB.jN2]
    | succ a ih =>
      intro ν hν
      have hν1 : n1 ν + (P.r + 1) * (P.r + 2) ≤ q0 := by nlinarith
      have hν0 : n1 ν ≤ q0 := by omega
      have hI : ∀ I ∈ S, n1 (ν + eZ I) + (P.r + 1) * a + (P.r + 1) * (P.r + 2) ≤ q0 := fun I hI => by
        have h1 := GlobalTheory.SuppliedPieri.n1_add_eZ_le ν I
        rw [(mem_powersetCard.1 hI).2] at h1
        nlinarith
      have hτ : ∀ I ∈ S, ‖tau ν I‖ ≤ Hh := fun I hI =>
        tau_boundL H P Wp Wq p lam b bv ga h q0 R l l' dg s J tau₀ hN hN' hS j hj tau hSL ν hν1 I
          (mem_powersetCard.1 hI).2
      have hsum : ∑ I ∈ S, ‖tau ν I‖ ≤ X * Hh :=
        (Finset.sum_le_card_nsmul _ _ _ hτ).trans (by rw [nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hcard hH0)
      have hterm : ∀ I ∈ S, ENNReal.ofReal ‖tau ν I‖ * momL p (J (ν + eZ I)) hj a ≤
          ENNReal.ofReal ‖tau ν I‖ * (ENNReal.ofReal ((X ^ 3 * Hh ^ 2) ^ a * X) * TBB.jN2 p (J ν)) := by
        intro I hIS
        rcases key ν hν0 with ⟨hJ0, -, -⟩ | ⟨-, -, -, -, he⟩
        · rw [hSL.tau_zero ν I (Or.inl hJ0)]
          simp
        refine mul_le_mul' le_rfl ((ih _ (hI I hIS)).trans ?_)
        rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
        refine mul_le_mul' le_rfl ?_
        rcases key _ (show n1 (ν + eZ I) ≤ q0 by have := hI I hIS; omega) with ⟨-, hz', -⟩ | ⟨-, -, -, -, he'⟩
        · rw [hz']; exact zero_le
        rw [he, he', ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        obtain ⟨hpos, hrat, -⟩ := hdeg ν hν0
        have e1 := hrat I
        rw [(mem_powersetCard.1 hIS).2] at e1
        have e3 := e1.trans (mul_le_mul_of_nonneg_right hnj hpos.le)
        calc _ ≤ c₀ * (_ * _) := mul_le_mul_of_nonneg_left e3 hc₀.le
          _ = _ := by ring
      have hpt : ∀ c : Fin (P.r + 1) → ℂ, ENNReal.ofReal (‖mnr hj (TBB.bigPt P.r c)‖ ^ (2 * (a + 1)) *
            TBB.Ew p (fun _ => 1) (J ν) (P.r + 1) [] (TBB.bigPt P.r c)) ≤
          ENNReal.ofReal (X * Hh) * ∑ I ∈ S, ENNReal.ofReal ‖tau ν I‖ *
            ENNReal.ofReal (‖mnr hj (TBB.bigPt P.r c)‖ ^ (2 * a) *
              TBB.Ew p (fun _ => 1) (J (ν + eZ I)) (P.r + 1) [] (TBB.bigPt P.r c)) := by
        intro c
        have e := ew_sum_le p (J ν) S (fun I => J (ν + eZ I)) (tau ν) (mnr hj (TBB.bigPt P.r c)) (TBB.bigPt P.r c)
          (supplied_pieriL H P Wp Wq p lam b bv ga h q0 R l l' dg s J tau₀ hN hS j hj tau hSL ν hν1 c)
        have hnn : ∀ I ∈ S, 0 ≤ ‖tau ν I‖ * (‖mnr hj (TBB.bigPt P.r c)‖ ^ (2 * a) *
            TBB.Ew p (fun _ => 1) (J (ν + eZ I)) (P.r + 1) [] (TBB.bigPt P.r c)) := fun I _ =>
          mul_nonneg (norm_nonneg _) (mul_nonneg (by positivity) (Formalism.FourierDecayAlt.P.TBBx4.ew_nonneg p _ _))
        rw [← Finset.sum_congr rfl fun I _ => ENNReal.ofReal_mul (norm_nonneg (tau ν I)),
          ← ENNReal.ofReal_sum_of_nonneg hnn, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have e2 := mul_le_mul_of_nonneg_left e (show 0 ≤ ‖mnr hj (TBB.bigPt P.r c)‖ ^ (2 * a) by positivity)
        calc _ = ‖mnr hj (TBB.bigPt P.r c)‖ ^ (2 * a) * (‖mnr hj (TBB.bigPt P.r c)‖ ^ 2 *
              TBB.Ew p (fun _ => 1) (J ν) (P.r + 1) [] (TBB.bigPt P.r c)) := by ring
          _ ≤ _ := e2
          _ = (∑ I ∈ S, ‖tau ν I‖) * ∑ I ∈ S, ‖tau ν I‖ * (‖mnr hj (TBB.bigPt P.r c)‖ ^ (2 * a) *
              TBB.Ew p (fun _ => 1) (J (ν + eZ I)) (P.r + 1) [] (TBB.bigPt P.r c)) := by
            rw [mul_left_comm, Finset.mul_sum]
            congr 1
            exact Finset.sum_congr rfl fun I _ => by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hsum (Finset.sum_nonneg hnn)
      have hmeas : ∀ I, AEMeasurable fun c : Fin (P.r + 1) → ℂ => ENNReal.ofReal (‖mnr hj (TBB.bigPt P.r c)‖ ^ (2 * a) *
          TBB.Ew p (fun _ => 1) (J (ν + eZ I)) (P.r + 1) [] (TBB.bigPt P.r c)) := fun I => by
        have e : (fun c : Fin (P.r + 1) → ℂ => ENNReal.ofReal (‖mnr hj (TBB.bigPt P.r c)‖ ^ (2 * a) *
            TBB.Ew p (fun _ => 1) (J (ν + eZ I)) (P.r + 1) [] (TBB.bigPt P.r c))) = fun c =>
            ENNReal.ofReal (‖mnr hj (TBB.bigPt P.r c)‖ ^ (2 * a)) *
              ENNReal.ofReal (TBB.Ew p (fun _ => 1) (J (ν + eZ I)) (P.r + 1) [] (TBB.bigPt P.r c)) :=
          funext fun c => ENNReal.ofReal_mul (by positivity)
        rw [e]
        exact (((meas_mnr hj).norm.pow_const _).ennreal_ofReal.aemeasurable).mul (hM _)
      calc momL p (J ν) hj (a + 1) ≤ _ := lintegral_mono hpt
        _ = ENNReal.ofReal (X * Hh) * ∑ I ∈ S, ENNReal.ofReal ‖tau ν I‖ * momL p (J (ν + eZ I)) hj a := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum' _ fun I _ => (hmeas I).const_mul _]
          congr 1
          exact Finset.sum_congr rfl fun I _ => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (X * Hh) * (ENNReal.ofReal (X * Hh) *
            (ENNReal.ofReal ((X ^ 3 * Hh ^ 2) ^ a * X) * TBB.jN2 p (J ν))) := by
          refine mul_le_mul' le_rfl ((Finset.sum_le_sum hterm).trans ?_)
          rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun I _ => norm_nonneg _)]
          exact mul_le_mul' (ENNReal.ofReal_le_ofReal hsum) le_rfl
        _ = _ := by
          rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          ring
  have hm := main a 0 (by simpa [n1] using hq)
  have ht2 : ENNReal.ofReal (‖(t : ℂ)‖ ^ 2) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact pow_pos (norm_pos_iff.2 (Complex.ofReal_ne_zero.2 ht.ne')) 2
  have e1 : momL p (J 0) hj a = ENNReal.ofReal (‖(t : ℂ)‖ ^ 2) * momL p f hj a := by
    rw [hJ]
    unfold momL
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun c => ?_
    rw [Formalism.FourierDecayAlt.P.CutBP.Ew_csmul, ← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1
    ring
  rw [e1, hJ, Formalism.FourierDecayAlt.P.CutBP.norm_sq_const_smul, mul_left_comm] at hm
  refine ((ENNReal.mul_le_mul_iff_right ht2 ENNReal.ofReal_ne_top).1 hm).trans
    (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  have hb0 : 0 < b := by linarith
  rw [Real.rpow_mul hb0.le, Real.rpow_natCast]
  refine pow_le_pow_left₀ (by positivity) ?_ a
  have hm' : ((2 * P.r + 2 : ℕ) : ℝ) = 2 * ((P.r + 1 : ℕ) : ℝ) := by push_cast; ring
  have hr1 : (1 : ℝ) ≤ ((P.r + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 _
  have e2 : Hh ≤ b ^ ((C + 10) * ((2 * P.r + 2 : ℕ) : ℝ) * ((P.r + 1 : ℕ) : ℝ)) := by
    rw [Real.rpow_mul hb0.le, Real.rpow_natCast]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hH _
  have e3 : X = b ^ ((P.r + 1 : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
  calc X ^ 3 * Hh ^ 2 ≤ (b ^ ((P.r + 1 : ℕ) : ℝ)) ^ 3 *
        (b ^ ((C + 10) * ((2 * P.r + 2 : ℕ) : ℝ) * ((P.r + 1 : ℕ) : ℝ))) ^ 2 := by
        rw [← e3]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hH0 e2 2) (by positivity)
    _ = b ^ (((P.r + 1 : ℕ) : ℝ) * 3 + (C + 10) * ((2 * P.r + 2 : ℕ) : ℝ) * ((P.r + 1 : ℕ) : ℝ) * 2) := by
        rw [Real.rpow_add hb0, Real.rpow_mul hb0.le _ 3, Real.rpow_mul hb0.le _ 2]
        norm_cast
    _ ≤ _ := by
        refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
        rw [hm']
        nlinarith

end Gp91.WG
