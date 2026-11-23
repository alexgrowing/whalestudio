import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DiscreteSeriesUnitarySmoothBasic
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.BesselCharacterUnipotentRadicalPropertiesImports
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.BesselSubgroupParameterMeasurePreservingImports
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.DecayThresholdsOfSpectralGapConditionImports
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselPeriodAdjointPairStatement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem besselInner_haar {k r : ℕ} {U : Set (Mx k r)} {μ : Measure (Formalism.QuantumDeterminants.Mt k r)} (h : B.IsHaarOn U μ) :
    PI.BesselPeriodGGP.IsHaarOn U μ :=
  ⟨Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite h, h.ne_zero, h.conc, h.left⟩

theorem besselInner_integral {k r : ℕ} (R : Rep k r) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq]
    (D : B.RealPlaceData k r Wp Wq)
    (hmul : ∀ g ∈ GG k r, ∀ h ∈ GG k r, ∀ v, R.σ (g * h) v = R.σ g (R.σ h v))
    (huni : ∀ g ∈ GG k r, ∀ v w, ⟪R.σ g v, R.σ g w⟫_ℂ = ⟪v, w⟫_ℂ)
    {γ : Mx k r} (hγ : γ ∈ GG k r) (x y : R.H) (X : Wq →L[ℂ] Wp)
    (a : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) (ha1 : Matrix.of a.1 ∈ GG k r) (ha2 : Matrix.of a.2 ∈ GG k r)
    (hint : Integrable (beInt D.z' Formalism.QuantumDeterminants.cStd D.π' R.σ y (R.σ (γ⁻¹ * Matrix.of a.2 * Matrix.of a.1) x))
      (D.μW'.prod D.μN)) :
    ∫ b, JF.integrand D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ (a, b) ∂(D.μW'.prod D.μN) =
      Formalism.QuantumDeterminants.psi k r D.z Formalism.QuantumDeterminants.cStd (Matrix.of a.2) • (D.π (Matrix.of a.1)).comp (X.comp
        (be D.z' Formalism.QuantumDeterminants.cStd D.π' R.σ D.μW' D.μN y (R.σ (γ⁻¹ * Matrix.of a.2 * Matrix.of a.1) x))) := by
  obtain ⟨-, -, -, hT, -, hae⟩ := GlobalTheory.T.besselSubgroup_parameter_measurePreserving k r D.z' D.μW' D.μN D.k_pos D.z'_mem D.T'_pos
    (besselInner_haar D.haarW') (besselInner_haar D.haarN)
  obtain ⟨-, -, -, hconj, hW, hN⟩ := GlobalTheory.T.besselCharacter_unipotentRadical_properties k r D.z' Formalism.QuantumDeterminants.cStd D.z'_mem
  set v := R.σ (γ⁻¹ * Matrix.of a.2 * Matrix.of a.1) x with hv
  set G := beInt D.z' Formalism.QuantumDeterminants.cStd D.π' R.σ y v with hG
  set T : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r := fun p =>
    ((fun i j => (Matrix.of p.1 : Mx k r) i j),
      (fun i j => ((Matrix.of p.1)⁻¹ * Matrix.of p.2 * Matrix.of p.1 : Mx k r) i j)) with hTdef
  let L : (Wq →L[ℂ] Wq) →L[ℂ] (Wq →L[ℂ] Wp) :=
    Formalism.QuantumDeterminants.psi k r D.z Formalism.QuantumDeterminants.cStd (Matrix.of a.2) •
      ContinuousLinearMap.compL ℂ Wq Wq Wp ((D.π (Matrix.of a.1)).comp X)
  have hL : ∀ A, L A = Formalism.QuantumDeterminants.psi k r D.z Formalism.QuantumDeterminants.cStd (Matrix.of a.2) •
      (D.π (Matrix.of a.1)).comp (X.comp A) := fun A => rfl
  have key : (fun b => JF.integrand D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ (a, b)) =ᵐ[D.μW'.prod D.μN]
      fun b => L (G (T b)) := by
    filter_upwards [hae] with b hb
    obtain ⟨hb1, hb2⟩ := hb
    have hb1G : Matrix.of b.1 ∈ GG k r := (hW _ hb1 _ hb1).2.2
    have hb2G : Matrix.of b.2 ∈ GG k r := hN _ hb2
    have u1 := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh ha1
    have u2 := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh ha2
    have u3 := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hγ
    have u4 := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hb1G
    have hg0 : γ⁻¹ * Matrix.of a.2 * Matrix.of a.1 ∈ GG k r :=
      Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hγ) ha2) ha1
    have hs : B.sgs (a, b) γ ∈ GG k r :=
      Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul
        (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv ha1) (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv ha2)) hγ) hb2G) hb1G
    have e1 : (γ⁻¹ * Matrix.of a.2 * Matrix.of a.1) * B.sgs (a, b) γ =
        Matrix.of b.1 * ((Matrix.of b.1)⁻¹ * Matrix.of b.2 * Matrix.of b.1) := by
      simp only [B.sgs, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ u1,
        Matrix.mul_nonsing_inv_cancel_left _ _ u2, Matrix.mul_nonsing_inv_cancel_left _ _ u4,
        Matrix.nonsing_inv_mul_cancel_left _ _ u3]
    have e2 : ⟪x, R.σ (B.sgs (a, b) γ) y⟫_ℂ =
        ⟪v, R.σ (Matrix.of b.1 * ((Matrix.of b.1)⁻¹ * Matrix.of b.2 * Matrix.of b.1)) y⟫_ℂ := by
      rw [← e1, hmul _ hg0 _ hs, hv, huni _ hg0]
    have e3 := (hconj _ hb1 _ hb2).2.2.2
    have e4 : G (T b) = (⟪v, R.σ (Matrix.of b.1 * ((Matrix.of b.1)⁻¹ * Matrix.of b.2 * Matrix.of b.1)) y⟫_ℂ *
        star (Formalism.QuantumDeterminants.psi k r D.z' Formalism.QuantumDeterminants.cStd ((Matrix.of b.1)⁻¹ * Matrix.of b.2 * Matrix.of b.1))) •
        D.π' (Matrix.of b.1)⁻¹ := rfl
    rw [hL, e4, e3, ← e2]
    ext w
    simp only [JF.integrand, JF.xiP, B.rho, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      map_smul, smul_smul]
    congr 1
    ring
  have hGT : Integrable (fun b => G (T b)) (D.μW'.prod D.μN) := hT.integrable_comp_of_integrable hint
  rw [integral_congr_ae key, L.integral_comp_comm hGT, ← hL]
  congr 1
  have h2 := integral_map hT.aemeasurable (f := G) (by rw [hT.map_eq]; exact hint.aestronglyMeasurable)
  rw [hT.map_eq] at h2
  exact h2.symm

theorem besselJ_coef_through_right : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → ∀ γ ∈ JF.Om k r D.z D.z', ∃ Bb : R.H → Wp → Wq → Wp, (∀ x b c (t : ℂ), Bb x (t • b) c = t • Bb x b c) ∧ ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ (X : Wq →L[ℂ] Wp) (c : Wq), B.JF D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ c = Bb x (X (l' y)) c := by
  intro hH k r ε mu h R Wp _ _ _ _ Wq _ _ _ _ D l l' hDS hgap hOK _ hl' γ hγ
  obtain ⟨hmul, -, huni, -, hsm, hTK, -⟩ := GlobalTheory.rep_basic_of_isDS hH.1.2.2.1 k r ε mu R hDS
  refine ⟨fun x b c => ∫ a : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
      (Formalism.QuantumDeterminants.psi k r D.z Formalism.QuantumDeterminants.cStd (Matrix.of a.2) *
        ⟪l' (R.σ (γ⁻¹ * Matrix.of a.2 * Matrix.of a.1) x), c⟫_ℂ) • D.π (Matrix.of a.1) b ∂(D.μW.prod D.μN), ?_, ?_⟩
  · intro x b c t
    simp only
    rw [← integral_smul]
    congr 1
    funext a
    rw [map_smul, smul_comm]
  intro x hx y hy X c
  have hcoef : IsCoef R l l' (fun g => ⟪x, R.σ g y⟫_ℂ • X) ⟪l x, X (l' y)⟫_ℂ :=
    ⟨1, fun _ => x, fun _ => y, fun _ => X, fun _ => ⟨hx, hy⟩, fun g _ => by simp, by simp⟩
  have hcc := (GlobalTheory.T.smooth_and_inCC_of_isCoef_of_gap hH k r ε mu h R Wp Wq l l' _ _ hDS hgap hOK hcoef).2 0
  have hI := (Formalism.FourierDecayAlt.P.bessel_integral_converges k r Wp Wq D _ _ (GlobalTheory.T.decayThresholds_of_spectralGapCondition k r h hOK).1 hcc).1 γ hγ
  haveI := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  haveI := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  haveI := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'
  have hJ : B.JF D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ =
      ∫ p, JF.integrand D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ p ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)) := rfl
  have hI' : Integrable (JF.integrand D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ)
      ((D.μW.prod D.μN).prod (D.μW'.prod D.μN)) := hI
  rw [hJ, integral_prod _ hI', ContinuousLinearMap.integral_apply hI'.integral_prod_left]
  obtain ⟨-, -, -, -, -, hae⟩ := GlobalTheory.T.besselSubgroup_parameter_measurePreserving k r D.z D.μW D.μN D.k_pos D.z_mem D.T_pos
    (besselInner_haar D.haarW) (besselInner_haar D.haarN)
  obtain ⟨-, -, -, -, hW, hN⟩ := GlobalTheory.T.besselCharacter_unipotentRadical_properties k r D.z Formalism.QuantumDeterminants.cStd D.z_mem
  refine integral_congr_ae ?_
  filter_upwards [hae] with a ha
  have ha1 : Matrix.of a.1 ∈ GG k r := (hW _ ha.1 _ ha.1).2.2
  have ha2 : Matrix.of a.2 ∈ GG k r := hN _ ha.2
  have hg0 : γ⁻¹ * Matrix.of a.2 * Matrix.of a.1 ∈ GG k r :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hγ.1) ha2) ha1
  obtain ⟨hint, hbe⟩ := hl'.2 y (hsm y hy) _ (hTK _ hg0 x hx)
  rw [besselInner_integral R D hmul huni hγ.1 x y X a ha1 ha2 hint, hbe]
  simp [smul_smul]

end GlobalTheory
