import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.GL3MeanSquares.HookFormulaTorsion.FourFoldOrthogonalSum
import Development.AbelianVarietyTheory.Definitions.Foundations.LatticeIntegralCoordinates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SignedLogMeans
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ClassMeanPeriods
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.EquidistributedConjugates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JacobiThetaHalfCharacteristic
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PeriodLatticeAgreement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitPosMeanOfPositivePart
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAnalyticSetupPeriodLatticePair
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsReduced
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UniformizationHolds
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIntegralPeriodElementStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormThetaCharTermLe

noncomputable section

namespace GlobalTheory.Theta0MeanProof

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke
open scoped nonZeroDivisors

theorem lemA : ∀ (D : D7) (c : Ideal (𝓞 D.host.K)), c ≠ ⊥ → ∀ x : ℂ, x ≠ 0 →
    (∀ z ∈ lamOf D c x, ((1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) * z ∈ lamOf D c x) ∧
    ∃ ω₁ τ : ℂ, ω₁ ≠ 0 ∧ 0 < τ.im ∧ JacobiThetaHalfCharacteristic.IsPeriodLattice (lamOf D c x) ω₁ τ ∧
      1 / 2 ≤ τ.im ∧ 2 * τ.im ≤ Real.sqrt D.host.d := GlobalTheory.IdealLattice.main

theorem lemB : EquidistributedConjugates.ConjugatesEquidistributed → PeriodLatticeAgreement.LatticePeriodEta →
    ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
      (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → ∀ ρ : M →ₐ[ℚ] ℂ,
      discr (lamConj M ρ (lamOf D cc δ)) = 1 ∧ ∃ c : Ideal (𝓞 D.host.K), c ≠ ⊥ ∧ ∃ x : ℂ, x ≠ 0 ∧
        lamConj M ρ (lamOf D cc δ) = lamOf D c x := GlobalTheory.ConjLattice.conj_lattice_holds

theorem lemC : EquidistributedConjugates.ConjugatesEquidistributed → PeriodLatticeAgreement.LatticePeriodEta → ThetaConstantWeber.ThetaWeberStatement →
    ∀ (D : D7), Formalism.MainNotions.GL3Theta.admJ D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ)
      [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t →
      ∃ X : M, X ≠ 0 ∧ IsIntegral ℤ (X : ℂ) ∧ ∀ (ρ : M →ₐ[ℚ] ℂ) (ω₁ τ : ℂ), ω₁ ≠ 0 → 0 < τ.im →
        JacobiThetaHalfCharacteristic.IsPeriodLattice (lamConj M ρ (lamOf D cc δ)) ω₁ τ → ∀ a b : Fin 2, JacobiThetaHalfCharacteristic.IsEvenChar a b →
        JacobiThetaHalfCharacteristic.thetaChar a b (t ρ / ω₁) τ = 0 →
        ‖ρ X‖ = (‖JacobiThetaHalfCharacteristic.thetaChar a b 0 τ‖ / ‖ModularForm.eta τ‖) ^ 12 := GlobalTheory.T.exists_integral_period_element

theorem lemD : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (a b : Fin 2) (τ : ℂ), 1 / 2 ≤ τ.im →
    ‖JacobiThetaHalfCharacteristic.thetaChar a b 0 τ‖ ≤ C₀ := GlobalTheory.Glob.EvenThetaBound.evenThetaConst_bounded

theorem containsData {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {M : IntermediateField ℚ ℂ}
    (h : DataIn D (tor0 D cc δ) M) : EquidistributedConjugates.ContainsData D M (lamOf D cc δ) := by
  refine ⟨fun x => ?_, h.2.1, h.2.2⟩
  have := h.1 (D.eTau.symm 1) (x : D.host.E)
  rwa [show (tor0 D cc δ).emb (D.eTau.symm 1) (x : D.host.E) = embT D (D.eTau.symm 1) (x : D.host.E) from rfl,
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.embT_K D _ _ x.2] at this

theorem isPeriodLattice_iff {Λ : AddSubgroup ℂ} {ω₁ τ : ℂ} :
    JacobiThetaHalfCharacteristic.IsPeriodLattice Λ ω₁ τ ↔ Λ = PeriodLatticeAgreement.latt ω₁ τ := by
  constructor
  · intro h; ext x; exact (h x).trans PeriodLatticeAgreement.mem_latt.symm
  · rintro rfl x; exact PeriodLatticeAgreement.mem_latt

theorem log_normSq {Λ : AddSubgroup ℂ} {τ t : ℂ} {a b : Fin 2}
    (hpos : 0 < normSq1 Λ (th0 Λ t)) (hτ : 0 < τ.im)
    (hf : (normSq1 Λ (th0 Λ t))⁻¹ = Real.sqrt (2 * τ.im) * ‖JacobiThetaHalfCharacteristic.thetaChar a b 0 τ‖ ^ 2) :
    0 < ‖JacobiThetaHalfCharacteristic.thetaChar a b 0 τ‖ ∧ Real.log (normSq1 Λ (th0 Λ t)) =
      -(1 / 2) * Real.log 2 - (1 / 2) * Real.log τ.im - 2 * Real.log ‖JacobiThetaHalfCharacteristic.thetaChar a b 0 τ‖ := by
  set N := normSq1 Λ (th0 Λ t)
  set th := ‖JacobiThetaHalfCharacteristic.thetaChar a b 0 τ‖
  have hs : 0 < Real.sqrt (2 * τ.im) := Real.sqrt_pos.2 (by linarith)
  have hth : 0 < th := by
    have h1 : 0 < Real.sqrt (2 * τ.im) * th ^ 2 := hf ▸ inv_pos.2 hpos
    have h2 : 0 < th ^ 2 := pos_of_mul_pos_right h1 hs.le
    exact lt_of_le_of_ne (norm_nonneg _) (fun h => by rw [← h] at h2; simp at h2)
  refine ⟨hth, ?_⟩
  have e1 : Real.log N = -Real.log N⁻¹ := by rw [Real.log_inv]; ring
  rw [e1, hf, Real.log_mul hs.ne' (by positivity), Real.log_sqrt (by linarith), Real.log_mul (by norm_num) hτ.ne',
    Real.log_pow]
  push_cast; ring

theorem log_area {Λ : AddSubgroup ℂ} {ω₁ τ : ℂ} (hP : PeriodLatticeAgreement.LatticePeriodEta) (hω : ω₁ ≠ 0) (hτ : 0 < τ.im)
    (hL : JacobiThetaHalfCharacteristic.IsPeriodLattice Λ ω₁ τ) (hd : discr Λ = 1) :
    0 < ‖ModularForm.eta τ‖ ∧ Real.log (area Λ) =
      Real.log 4 + 2 * Real.log Real.pi + Real.log τ.im + 4 * Real.log ‖ModularForm.eta τ‖ := by
  rw [isPeriodLattice_iff] at hL
  subst hL
  have he : ModularForm.eta τ ≠ 0 := ModularForm.eta_ne_zero hτ
  have hen : 0 < ‖ModularForm.eta τ‖ := norm_pos_iff.2 he
  refine ⟨hen, ?_⟩
  have h := hP.2.2.1 ω₁ ⟨τ, hτ⟩ hω
  simp only [PeriodLatticeAgreement.period, hd, norm_one, Real.one_rpow, one_mul] at h
  change area (PeriodLatticeAgreement.latt ω₁ τ) / Real.pi = 4 * Real.pi * τ.im * ‖ModularForm.eta τ‖ ^ 4 at h
  have hpi := Real.pi_pos
  have h2 : area (PeriodLatticeAgreement.latt ω₁ τ) = 4 * Real.pi ^ 2 * τ.im * ‖ModularForm.eta τ‖ ^ 4 := by
    field_simp at h; linarith
  rw [h2, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) hτ.ne',
    Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
  push_cast; ring

theorem period_pos (hP : PeriodLatticeAgreement.LatticePeriodEta) (D : D7) (c : (Ideal (𝓞 D.host.K))⁰) :
    0 < ClassMeanPeriods.period D c := by
  have hc : (c : Ideal (𝓞 D.host.K)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero c
  obtain ⟨-, ω₁, τ, hω, hτ, hL, -, -⟩ := lemA D c hc 1 one_ne_zero
  rw [isPeriodLattice_iff] at hL
  have hA := hP.2.1 ω₁ ⟨τ, hτ⟩ hω
  have hD := hP.1 ω₁ ⟨τ, hτ⟩ hω
  change area (PeriodLatticeAgreement.latt ω₁ τ) = ‖ω₁‖ ^ 2 * τ.im at hA
  change discr (PeriodLatticeAgreement.latt ω₁ τ) = (2 * (Real.pi : ℂ) / ω₁) ^ 12 * ModularForm.eta τ ^ 24 at hD
  have he : ModularForm.eta τ ≠ 0 := ModularForm.eta_ne_zero hτ
  have hdn : discr (lamOf D c 1) ≠ 0 := by
    rw [hL, hD]
    have : (2 * (Real.pi : ℂ) / ω₁) ≠ 0 := div_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) hω
    exact mul_ne_zero (pow_ne_zero _ this) (pow_ne_zero _ he)
  have har : 0 < area (lamOf D c 1) := by
    rw [hL, hA]; have := norm_pos_iff.2 hω; positivity
  unfold ClassMeanPeriods.period
  have := norm_pos_iff.2 hdn
  have := Real.pi_pos
  positivity

theorem mean_log_area (hC : ClassMeanPeriods.ClassMean) (hG : EquidistributedConjugates.ConjugatesEquidistributed)
    (hP : PeriodLatticeAgreement.LatticePeriodEta) (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ) (hS : SignedLogMeans.HidaSetting D cc δ M t) :
    (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ (lamOf D cc δ)))) / (Module.finrank ℚ M : ℝ) =
      Real.log Real.pi + ClassMeanPeriods.classMeanValue D := by
  obtain ⟨hcc, hδ, hData, -⟩ := hS
  obtain ⟨r, hr⟩ := EquidistributedConjugates.exists_representatives D
  rw [(hG D cc δ hcc hδ M (containsData hData)).2.2 r hr]
  have hCM := ClassMeanPeriods.classMean_iff.1 hC D r hr
  unfold ClassMeanPeriods.meanLogPeriod at hCM
  have hh : (0 : ℝ) < (classNumber D.host.K : ℝ) := by exact_mod_cast classNumber_pos D.host.K
  have e : ∀ C, Real.log (EquidistributedConjugates.normArea D (r C : Ideal (𝓞 D.host.K))) =
      Real.log Real.pi + Real.log (ClassMeanPeriods.period D (r C)) := by
    intro C
    have h1 : EquidistributedConjugates.normArea D (r C : Ideal (𝓞 D.host.K)) = Real.pi * ClassMeanPeriods.period D (r C) := by
      unfold EquidistributedConjugates.normArea ClassMeanPeriods.period
      field_simp
    rw [h1, Real.log_mul Real.pi_ne_zero (period_pos hP D (r C)).ne']
  simp only [e, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [add_div, hCM]
  congr 1
  rw [show (Fintype.card (ClassGroup (𝓞 D.host.K)) : ℝ) = (classNumber D.host.K : ℝ) from rfl]
  field_simp

theorem sum_log_nonneg (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (X : M) (hX : X ≠ 0)
    (hXi : IsIntegral ℤ (X : ℂ)) : 0 ≤ ∑ ρ : M →ₐ[ℚ] ℂ, Real.log ‖ρ X‖ := by
  haveI : NumberField M := ⟨⟩
  have hXi' : IsIntegral ℤ X := by
    have : IsIntegral ℤ ((M.val : M →ₐ[ℚ] ℂ) X) := hXi
    exact (isIntegral_algHom_iff ((M.val : M →ₐ[ℚ] ℂ).restrictScalars ℤ) M.val.injective).1 this
  have h := Formalism.HermitianLattices.IntegralLatticeDensity.integer_mean_log_bound M ⟨X, hXi'⟩ (by
    intro h0; apply hX; exact congrArg Subtype.val h0)
  rw [← (RingHom.equivRatAlgHom M ℂ).sum_comp]
  exact h

theorem core (hN : JacobiThetaHalfCharacteristic.NormTheta0) (hC : ClassMeanPeriods.ClassMean) (hG : EquidistributedConjugates.ConjugatesEquidistributed)
    (hP : PeriodLatticeAgreement.LatticePeriodEta) (hW : ThetaConstantWeber.ThetaWeberStatement) {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hth : ∀ (a b : Fin 2) (τ : ℂ), 1 / 2 ≤ τ.im → ‖JacobiThetaHalfCharacteristic.thetaChar a b 0 τ‖ ≤ C₀)
    (D : D7) (hJ : Formalism.MainNotions.GL3Theta.admJ D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ) (hS : SignedLogMeans.HidaSetting D cc δ M t) :
    SignedLogMeans.meanLog M (lamOf D cc δ) t ≤ SignedLogMeans.bound D ∧
      SignedLogMeans.meanPosLog M (lamOf D cc δ) t ≤
        SignedLogMeans.meanLog M (lamOf D cc δ) t + ((1 / 4) * Real.log D.host.d + max 0 (2 * Real.log C₀)) := by
  classical
  have hArea := mean_log_area hC hG hP D cc δ M t hS
  obtain ⟨X, hX0, hXi, hXρ⟩ := lemC hG hP hW D hJ cc δ M t hS
  have hInt := sum_log_nonneg M X hX0 hXi
  have hB := lemB hG hP D cc δ M t hS
  have hT0 := hS.2.2.2
  set Λ := lamOf D cc δ with hΛ
  choose hdisc c hc x hx hΛeq using hB
  have hA := fun ρ => lemA D (c ρ) (hc ρ) (x ρ) (hx ρ)
  choose hstab ω τ hω hτ hLat hy1 hy2 using hA
  have hLat' : ∀ ρ, JacobiThetaHalfCharacteristic.IsPeriodLattice (lamConj M ρ Λ) (ω ρ) (τ ρ) := by
    intro ρ; rw [hΛeq ρ]; exact hLat ρ
  have htn : ∀ ρ, t ρ ∉ lamConj M ρ Λ := by
    intro ρ ht
    apply (hT0 ρ).2.1
    rw [hΛeq ρ] at ht ⊢
    exact hstab ρ _ ht
  have hNρ := fun ρ => hN _ (ω ρ) (τ ρ) (t ρ) (hω ρ) (hτ ρ) (hLat' ρ) (hT0 ρ).1 (htn ρ)
  have hex : ∀ ρ, ∃ ab : Fin 2 × Fin 2, JacobiThetaHalfCharacteristic.IsEvenChar ab.1 ab.2 ∧
      JacobiThetaHalfCharacteristic.thetaChar ab.1 ab.2 (t ρ / ω ρ) (τ ρ) = 0 := fun ρ => (hNρ ρ).1.exists
  choose ab hab0 hab1 using hex
  set th : (M →ₐ[ℚ] ℂ) → ℝ := fun ρ => ‖JacobiThetaHalfCharacteristic.thetaChar (ab ρ).1 (ab ρ).2 0 (τ ρ)‖ with hthdef
  set et : (M →ₐ[ℚ] ℂ) → ℝ := fun ρ => ‖ModularForm.eta (τ ρ)‖ with hetdef
  have F1 : ∀ ρ, 0 < th ρ ∧ Real.log (SignedLogMeans.conjNormSq M Λ ρ (t ρ)) =
      -(1 / 2) * Real.log 2 - (1 / 2) * Real.log (τ ρ).im - 2 * Real.log (th ρ) :=
    fun ρ => log_normSq (hNρ ρ).2.1 (hτ ρ) ((hNρ ρ).2.2 _ _ (hab0 ρ) (hab1 ρ))
  have F2 := fun ρ => log_area hP (hω ρ) (hτ ρ) (hLat' ρ) (hdisc ρ)
  have F3 : ∀ ρ, Real.log ‖ρ X‖ = 12 * (Real.log (th ρ) - Real.log (et ρ)) := by
    intro ρ
    rw [hXρ ρ (ω ρ) (τ ρ) (hω ρ) (hτ ρ) (hLat' ρ) _ _ (hab0 ρ) (hab1 ρ), Real.log_pow,
      Real.log_div (F1 ρ).1.ne' (F2 ρ).1.ne']
    push_cast; ring

  set n : ℝ := (Module.finrank ℚ M : ℝ) with hn
  have hcard : (Finset.univ : Finset (M →ₐ[ℚ] ℂ)).card = Module.finrank ℚ M := by
    rw [Finset.card_univ]; exact AlgHom.card ℚ M ℂ
  have hnpos : 0 < n := by rw [hn]; exact_mod_cast Module.finrank_pos
  set St := ∑ ρ, Real.log (th ρ)
  set Se := ∑ ρ, Real.log (et ρ)
  set Sy := ∑ ρ, Real.log (τ ρ).im
  have e1 : ∑ ρ, Real.log (SignedLogMeans.conjNormSq M Λ ρ (t ρ)) = -(1 / 2) * Real.log 2 * n - (1 / 2) * Sy - 2 * St := by
    rw [Finset.sum_congr rfl fun ρ _ => (F1 ρ).2]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, hcard, nsmul_eq_mul]
    rw [hn]; ring
  have e2 : ∑ ρ, Real.log (area (lamConj M ρ Λ)) = (Real.log 4 + 2 * Real.log Real.pi) * n + Sy + 4 * Se := by
    rw [Finset.sum_congr rfl fun ρ _ => (F2 ρ).2]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, hcard, nsmul_eq_mul]
    rw [hn]; ring
  have e3 : 0 ≤ St - Se := by
    have : ∑ ρ : M →ₐ[ℚ] ℂ, Real.log ‖ρ X‖ = 12 * (St - Se) := by
      rw [Finset.sum_congr rfl fun ρ _ => F3 ρ, ← Finset.mul_sum, Finset.sum_sub_distrib]
    linarith
  rw [e2] at hArea
  have hA2 : (Real.log 4 + 2 * Real.log Real.pi) * n + Sy + 4 * Se = (Real.log Real.pi + ClassMeanPeriods.classMeanValue D) * n := by
    rw [← hArea]; field_simp
  have hsd : 0 < Real.sqrt (D.host.d : ℝ) := Real.sqrt_pos.2 (by
    have := GlobalTheory.Theta0MeanCompare.one_le_d D; linarith)
  have hcmv : ClassMeanPeriods.classMeanValue D = Real.eulerMascheroniConstant + Real.log 2 + Real.log Real.pi -
      Real.log (Real.sqrt D.host.d) - logDerivativeAtOne D := by
    unfold ClassMeanPeriods.classMeanValue
    rw [Real.log_div (by positivity) hsd.ne', Real.log_mul two_ne_zero Real.pi_ne_zero]; ring
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  constructor
  · unfold SignedLogMeans.meanLog
    rw [div_le_iff₀ hnpos]
    change ∑ ρ, Real.log (SignedLogMeans.conjNormSq M Λ ρ (t ρ)) ≤ _
    rw [e1]
    unfold SignedLogMeans.bound
    rw [hcmv, hl4] at hA2
    nlinarith
  ·
    have hK : ∀ ρ, max 0 (Real.log (SignedLogMeans.conjNormSq M Λ ρ (t ρ))) ≤
        Real.log (SignedLogMeans.conjNormSq M Λ ρ (t ρ)) + ((1 / 4) * Real.log D.host.d + max 0 (2 * Real.log C₀)) := by
      intro ρ
      have hd1 : 0 ≤ Real.log (D.host.d : ℝ) := Real.log_nonneg (GlobalTheory.Theta0MeanCompare.one_le_d D)
      have hm := le_max_right 0 (2 * Real.log C₀)
      have hm0 := le_max_left 0 (2 * Real.log C₀)
      have h1 := (F1 ρ).2
      have h2 : Real.log (th ρ) ≤ Real.log C₀ :=
        Real.log_le_log (F1 ρ).1 (hth _ _ _ (hy1 ρ))
      have h3 : Real.log (2 * (τ ρ).im) ≤ Real.log (Real.sqrt D.host.d) :=
        Real.log_le_log (by linarith [hτ ρ]) (hy2 ρ)
      rw [Real.log_mul two_ne_zero (hτ ρ).ne'] at h3
      have h4 : Real.log (Real.sqrt (D.host.d : ℝ)) = (1 / 2) * Real.log D.host.d := by
        rw [Real.log_sqrt (by positivity)]; ring
      apply max_le
      · change _ ≤ Real.log (SignedLogMeans.conjNormSq M Λ ρ (t ρ)) + _
        rw [h1]; linarith
      · linarith
    set K := (1 / 4) * Real.log D.host.d + max 0 (2 * Real.log C₀)
    have hs := Finset.sum_le_sum fun ρ (_ : ρ ∈ (Finset.univ : Finset (M →ₐ[ℚ] ℂ))) => hK ρ
    rw [Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul] at hs
    unfold SignedLogMeans.meanPosLog SignedLogMeans.meanLog
    change (∑ ρ, max 0 (Real.log (SignedLogMeans.conjNormSq M Λ ρ (t ρ)))) / n ≤
      (∑ ρ, Real.log (SignedLogMeans.conjNormSq M Λ ρ (t ρ))) / n + K
    rw [div_add' _ _ _ hnpos.ne', div_le_div_iff_of_pos_right hnpos]
    rw [hn]; linarith

theorem log_sqrt_le_log_v (D : D7) : Real.log (Real.sqrt D.host.d) ≤ Real.log D.host.v := by
  have h1 := GlobalTheory.Theta0MeanCompare.two_sqrt_le_rd D
  have h2 := GlobalTheory.Theta0MeanCompare.one_le_sqrt_d D
  exact Real.log_le_log (by linarith) (by unfold Host.v; linarith)

theorem half_le_log_v (D : D7) : 1 / 2 ≤ Real.log D.host.v := by
  have h7 : (4 : ℝ) ≤ D.host.d := by
    have := D.host.hyp.2.2.2.1
    exact_mod_cast (by omega : 4 ≤ D.host.d)
  have hs : (2 : ℝ) ≤ Real.sqrt D.host.d := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt h7
  have h1 := log_sqrt_le_log_v D
  have h2 : Real.log 2 ≤ Real.log (Real.sqrt D.host.d) := Real.log_le_log (by norm_num) hs
  have := Real.log_two_gt_d9
  linarith

theorem bound_le_half (D : D7) {L : ℝ} (hL : Real.log D.host.v + |logDerivativeAtOne D| ≤ L) :
    SignedLogMeans.bound D ≤ (1 / 2) * L := by
  have h1 := log_sqrt_le_log_v D
  have h2 := le_abs_self (logDerivativeAtOne D)
  have h3 := Real.one_half_lt_eulerMascheroniConstant
  unfold SignedLogMeans.bound
  linarith

theorem log_d_le (D : D7) {L : ℝ} (hL : Real.log D.host.v + |logDerivativeAtOne D| ≤ L) :
    (1 / 4) * Real.log D.host.d ≤ (1 / 2) * L := by
  have h1 := log_sqrt_le_log_v D
  have h2 := abs_nonneg (logDerivativeAtOne D)
  have h4 : Real.log (Real.sqrt (D.host.d : ℝ)) = (1 / 2) * Real.log D.host.d := by
    rw [Real.log_sqrt (by positivity)]; ring
  linarith

theorem theta0Mean (hN : JacobiThetaHalfCharacteristic.NormTheta0) (hC : ClassMeanPeriods.ClassMean) (hG : EquidistributedConjugates.ConjugatesEquidistributed)
    (hP : PeriodLatticeAgreement.LatticePeriodEta) (hJ : ∀ D : D7, Formalism.MainNotions.GL3Theta.admJ D) (hW : ThetaConstantWeber.ThetaWeberStatement) :
    SignedLogMeans.Theta0Mean := by
  obtain ⟨C₀, hC₀, hth⟩ := lemD
  set C := max 0 (2 * Real.log C₀) with hCdef
  have hC0 : 0 ≤ C := le_max_left _ _
  refine ⟨⟨fun D cc δ M _ t hS => (core hN hC hG hP hW hC₀ hth D (hJ D) cc δ M t hS).1,
    fun D cc δ M _ t hS L hL => ?_, ⟨1 / 2, by norm_num, fun D cc δ M _ t hS L hL => ?_⟩⟩,
    ⟨C, hC0, fun D cc δ M _ t hS => ?_⟩, ⟨1 + 2 * C, by linarith, fun D cc δ M _ t hS L hL => ?_⟩⟩
  · have := (core hN hC hG hP hW hC₀ hth D (hJ D) cc δ M t hS).1
    rw [GlobalTheory.Theta0MeanCompare.bound_eq] at this
    exact this.trans (GlobalTheory.Theta0MeanCompare.kronBound_le D hL)
  · exact (core hN hC hG hP hW hC₀ hth D (hJ D) cc δ M t hS).1.trans (bound_le_half D hL)
  · obtain ⟨h1, h2⟩ := core hN hC hG hP hW hC₀ hth D (hJ D) cc δ M t hS
    linarith
  · obtain ⟨h1, h2⟩ := core hN hC hG hP hW hC₀ hth D (hJ D) cc δ M t hS
    have a1 := bound_le_half D hL
    have a2 := log_d_le D hL
    have a3 : 1 / 2 ≤ L := by have := half_le_log_v D; have := abs_nonneg (logDerivativeAtOne D); linarith
    have a4 : C ≤ 2 * C * L := by nlinarith
    linarith

end GlobalTheory.Theta0MeanProof
