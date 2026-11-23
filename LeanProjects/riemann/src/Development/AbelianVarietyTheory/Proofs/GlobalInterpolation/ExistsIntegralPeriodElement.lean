import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Definitions.Foundations.LatticeIntegralCoordinates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SignedLogMeans
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.EquidistributedConjugates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PeriodLatticeAgreement
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JacobiThetaHalfCharacteristic
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DifferentiableAtDerivAtZero
import Formalism.GL3MeanSquares.HookFormulaTorsion.FourFoldOrthogonalSum
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaCharHalfPeriodEqZeroIffStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HalfPeriodWeierstrassValueMemConjStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

noncomputable section
namespace GlobalTheory.IntegralX

lemma cubic_alg {e1 e2 e3 g h : ℂ} (h12 : e1 ≠ e2) (h13 : e1 ≠ e3) (h23 : e2 ≠ e3)
    (r1 : 4 * e1 ^ 3 - g * e1 - h = 0) (r2 : 4 * e2 ^ 3 - g * e2 - h = 0)
    (r3 : 4 * e3 ^ 3 - g * e3 - h = 0) :
    12 * e1 ^ 2 - g = 4 * (e1 - e2) * (e1 - e3) ∧ 12 * e2 ^ 2 - g = 4 * (e2 - e1) * (e2 - e3) ∧
      12 * e3 ^ 2 - g = 4 * (e3 - e1) * (e3 - e2) := by
  have a12 : 4 * (e1 ^ 2 + e1 * e2 + e2 ^ 2) = g :=
    mul_left_cancel₀ (sub_ne_zero.2 h12) (by linear_combination r1 - r2)
  have a13 : 4 * (e1 ^ 2 + e1 * e3 + e3 ^ 2) = g :=
    mul_left_cancel₀ (sub_ne_zero.2 h13) (by linear_combination r1 - r3)
  have s : e1 + e2 + e3 = 0 := by
    have : (e2 - e3) * (e1 + e2 + e3) = (e2 - e3) * 0 := by linear_combination (a12 - a13) / 4
    exact mul_left_cancel₀ (sub_ne_zero.2 h23) this
  obtain rfl : e3 = -e1 - e2 := by linear_combination s
  refine ⟨?_, ?_, ?_⟩ <;> linear_combination a12

lemma half_root (L : PeriodPair) {t : ℂ} (h2 : 2 * t ∈ L.lattice) (ht : t ∉ L.lattice) :
    4 * L.weierstrassP t ^ 3 - L.g₂ * L.weierstrassP t - L.g₃ = 0 := by
  have e1 := L.derivWeierstrassP_add_coe (-t) ⟨2 * t, h2⟩
  rw [L.derivWeierstrassP_neg] at e1
  have e2 : -t + 2 * t = t := by ring
  simp only [e2] at e1
  have e3 : L.derivWeierstrassP t = 0 := by linear_combination e1 / 2
  rw [← L.derivWeierstrassP_sq t ht, e3]
  simp

theorem cubic : ∀ τ : UpperHalfPlane, ThetaConstantWeber.HalfPeriodDiff τ → ThetaConstantWeber.JacobiProduct τ →
    12 * ThetaConstantWeber.wp τ (1 / 2) ^ 2 - (GlobalTheory.periodPairOfTau τ).g₂ =
        4 * (ThetaConstantWeber.wp τ (1 / 2) - ThetaConstantWeber.wp τ ((τ : ℂ) / 2)) * (ThetaConstantWeber.wp τ (1 / 2) - ThetaConstantWeber.wp τ ((1 + (τ : ℂ)) / 2)) ∧
    12 * ThetaConstantWeber.wp τ ((τ : ℂ) / 2) ^ 2 - (GlobalTheory.periodPairOfTau τ).g₂ =
        4 * (ThetaConstantWeber.wp τ ((τ : ℂ) / 2) - ThetaConstantWeber.wp τ (1 / 2)) * (ThetaConstantWeber.wp τ ((τ : ℂ) / 2) - ThetaConstantWeber.wp τ ((1 + (τ : ℂ)) / 2)) ∧
    12 * ThetaConstantWeber.wp τ ((1 + (τ : ℂ)) / 2) ^ 2 - (GlobalTheory.periodPairOfTau τ).g₂ =
        4 * (ThetaConstantWeber.wp τ ((1 + (τ : ℂ)) / 2) - ThetaConstantWeber.wp τ (1 / 2)) * (ThetaConstantWeber.wp τ ((1 + (τ : ℂ)) / 2) - ThetaConstantWeber.wp τ ((τ : ℂ) / 2)) := by
  intro τ hd hj
  obtain ⟨d1, d2, d3⟩ := hd
  unfold ThetaConstantWeber.JacobiProduct at hj
  have hη : ModularForm.eta (τ : ℂ) ≠ 0 := ModularForm.eta_ne_zero τ.2
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hprod : ThetaConstantWeber.thetaConst 0 0 τ * ThetaConstantWeber.thetaConst 0 1 τ * ThetaConstantWeber.thetaConst 1 0 τ ≠ 0 := by
    rw [hj]
    exact mul_ne_zero two_ne_zero (pow_ne_zero _ hη)
  have t0 : ThetaConstantWeber.thetaConst 0 0 τ ≠ 0 := fun h => hprod (by simp [h])
  have t1 : ThetaConstantWeber.thetaConst 0 1 τ ≠ 0 := fun h => hprod (by simp [h])
  have t2 : ThetaConstantWeber.thetaConst 1 0 τ ≠ 0 := fun h => hprod (by simp [h])
  obtain ⟨n1, n2, n3⟩ := ThetaConstantWeber.halfPeriods_notMem τ
  have mem : ∀ p q : ℤ, ((p : ℂ) * (τ : ℂ) + q) ∈ (GlobalTheory.periodPairOfTau τ).lattice := fun p q => by
    rw [GlobalTheory.mem_lattice_periodPairOfTau]
    exact ⟨p, q, by ring⟩
  have r1 := half_root (GlobalTheory.periodPairOfTau τ) (t := 1 / 2) (by simpa using mem 0 1) n1
  have r2 := half_root (GlobalTheory.periodPairOfTau τ) (t := (τ : ℂ) / 2) (by
    have := mem 1 0
    convert this using 1
    push_cast
    ring) n2
  have r3 := half_root (GlobalTheory.periodPairOfTau τ) (t := (1 + (τ : ℂ)) / 2) (by
    have := mem 1 1
    convert this using 1
    push_cast
    ring) n3
  refine cubic_alg (e1 := ThetaConstantWeber.wp τ (1 / 2)) (e2 := ThetaConstantWeber.wp τ ((τ : ℂ) / 2))
    (e3 := ThetaConstantWeber.wp τ ((1 + (τ : ℂ)) / 2)) (h := (GlobalTheory.periodPairOfTau τ).g₃) ?_ ?_ ?_ r1 r2 r3
  · rw [← sub_ne_zero, d1]
    exact mul_ne_zero (pow_ne_zero _ hp) (pow_ne_zero _ t0)
  · rw [← sub_ne_zero, d2]
    exact mul_ne_zero (pow_ne_zero _ hp) (pow_ne_zero _ t1)
  · intro h
    have h' : ThetaConstantWeber.wp τ ((1 + (τ : ℂ)) / 2) - ThetaConstantWeber.wp τ ((τ : ℂ) / 2) = 0 := by rw [h]; ring
    rw [d3] at h'
    exact mul_ne_zero (pow_ne_zero _ hp) (pow_ne_zero _ t2) h'

theorem scaling : ∀ (Λ : AddSubgroup ℂ) (ω₁ : ℂ) (τ : UpperHalfPlane), ω₁ ≠ 0 →
    JacobiThetaHalfCharacteristic.IsPeriodLattice Λ ω₁ (τ : ℂ) →
    g2 Λ = (GlobalTheory.periodPairOfTau τ).g₂ / ω₁ ^ 4 ∧ g3 Λ = (GlobalTheory.periodPairOfTau τ).g₃ / ω₁ ^ 6 ∧
    ∀ z : ℂ, z ∉ Λ → Formalism.MainNotions.StandardLatticesGL3.wpF Λ z = ThetaConstantWeber.wp τ (z / ω₁) / ω₁ ^ 2 := by
  intro Λ ω₁ τ hω hP
  have H := GlobalTheory.isHomothetic_scalePeriods (GlobalTheory.periodPairOfTau τ) ω₁ hω
  have hmem : ∀ z, z ∈ Λ ↔ z ∈ (GlobalTheory.scalePeriods (GlobalTheory.periodPairOfTau τ) ω₁ hω).lattice := by
    intro z
    have hz : ω₁ * (z / ω₁) = z := by field_simp
    rw [hP z, ← hz, H (z / ω₁), hz, GlobalTheory.mem_lattice_periodPairOfTau]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨n, m, by field_simp; ring⟩
    · rintro ⟨m, n, h⟩
      refine ⟨n, m, ?_⟩
      rw [← hz, ← h]
      ring
  obtain ⟨e2, e3, -, -, hw, -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary _ Λ hmem
  refine ⟨by rw [e2, H.g₂_eq]; field_simp, by rw [e3, H.g₃_eq]; field_simp, fun z hz => ?_⟩
  have hz' : ω₁ * (z / ω₁) = z := by field_simp
  rw [(hw z hz).1]
  have h := H.weierstrassP_mul (z / ω₁)
  rw [hz'] at h
  rw [h]
  unfold ThetaConstantWeber.wp
  field_simp

lemma thetaChar_zero (a b : Fin 2) (τ : UpperHalfPlane) :
    JacobiThetaHalfCharacteristic.thetaChar a b 0 (τ : ℂ) = ThetaConstantWeber.thetaConst (a : ℕ) (b : ℕ) τ := by
  simp only [JacobiThetaHalfCharacteristic.thetaChar, ThetaConstantWeber.thetaConst, zero_add]
  congr 2
  ring

lemma wp_shift (τ : UpperHalfPlane) (z : ℂ) (p q : ℤ) :
    ThetaConstantWeber.wp τ (z + ((p : ℂ) + (q : ℂ) * (τ : ℂ))) = ThetaConstantWeber.wp τ z := by
  have h : (((p : ℂ) + (q : ℂ) * (τ : ℂ))) ∈ (GlobalTheory.periodPairOfTau τ).lattice := by
    rw [GlobalTheory.mem_lattice_periodPairOfTau]
    exact ⟨q, p, by ring⟩
  exact (GlobalTheory.periodPairOfTau τ).weierstrassP_add_coe z ⟨_, h⟩

lemma alg {A B C η W P Y σ : ℂ} (hW : W ≠ 0) (hη : η ≠ 0) (hσ : σ = 1 ∨ σ = -1)
    (hABC : A * B * C = 2 * η ^ 3) (hD : (2 * P / W) ^ 12 * η ^ 24 = 1)
    (hY : Y = σ * (P ^ 4 * A ^ 4 * B ^ 4) / W ^ 4) :
    Y ≠ 0 ∧ 1 / Y ^ 3 = σ * (C / η) ^ 12 := by
  have hσ4 : σ ^ 4 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hk : Y ^ 3 * (σ * (C / η) ^ 12) = 1 := by
    have h1 : Y ^ 3 * (σ * (C / η) ^ 12) = σ ^ 4 * (A * B * C) ^ 12 * P ^ 12 / (W ^ 12 * η ^ 12) := by
      rw [hY]
      field_simp
    have h2 : σ ^ 4 * (A * B * C) ^ 12 * P ^ 12 / (W ^ 12 * η ^ 12) = (2 * P / W) ^ 12 * η ^ 24 := by
      rw [hσ4, hABC]
      field_simp
    rw [h1, h2, hD]
  have hY0 : Y ≠ 0 := by
    rintro rfl
    simp at hk
  refine ⟨hY0, ?_⟩
  rw [div_eq_iff (pow_ne_zero _ hY0)]
  linear_combination -hk

lemma half_coords {Λ : AddSubgroup ℂ} {ω₁ : ℂ} {τ : UpperHalfPlane} {t : ℂ} (hω : ω₁ ≠ 0)
    (hΛ : JacobiThetaHalfCharacteristic.IsPeriodLattice Λ ω₁ (τ : ℂ)) (h2 : 2 * t ∈ Λ) :
    ∃ m n : ℤ, t / ω₁ = ((m : ℂ) + (n : ℂ) * (τ : ℂ)) / 2 := by
  obtain ⟨m, n, h⟩ := (hΛ _).1 h2
  refine ⟨m, n, ?_⟩
  field_simp
  linear_combination h

lemma discr_eta (hL : PeriodLatticeAgreement.LatticePeriodEta) {Λ : AddSubgroup ℂ} {ω₁ : ℂ} {τ : UpperHalfPlane}
    (hω : ω₁ ≠ 0) (hΛ : JacobiThetaHalfCharacteristic.IsPeriodLattice Λ ω₁ (τ : ℂ)) (hd : discr Λ = 1) :
    (2 * (Real.pi : ℂ) / ω₁) ^ 12 * ModularForm.eta (τ : ℂ) ^ 24 = 1 := by
  have e : Λ = PeriodLatticeAgreement.latt ω₁ (τ : ℂ) := by
    ext w
    rw [hΛ w, PeriodLatticeAgreement.mem_latt]
  rw [← hL.1 ω₁ τ hω, ← e, hd]

theorem modulus (hL : PeriodLatticeAgreement.LatticePeriodEta) (hT : ThetaConstantWeber.ThetaWeberStatement)
    (Λ : AddSubgroup ℂ) (ω₁ : ℂ) (τ : UpperHalfPlane) (t : ℂ) (hω : ω₁ ≠ 0)
    (hΛ : JacobiThetaHalfCharacteristic.IsPeriodLattice Λ ω₁ (τ : ℂ)) (hd : discr Λ = 1) (h2 : 2 * t ∈ Λ) (ht : t ∉ Λ)
    (a b : Fin 2) (hab : JacobiThetaHalfCharacteristic.IsEvenChar a b) (hz : JacobiThetaHalfCharacteristic.thetaChar a b (t / ω₁) (τ : ℂ) = 0) :
    (12 * Formalism.MainNotions.StandardLatticesGL3.wpF Λ t ^ 2 - g2 Λ) / 4 ≠ 0 ∧ ∃ s : ℂ, (s = 1 ∨ s = -1) ∧
      1 / ((12 * Formalism.MainNotions.StandardLatticesGL3.wpF Λ t ^ 2 - g2 Λ) / 4) ^ 3 =
        s * (JacobiThetaHalfCharacteristic.thetaChar a b 0 (τ : ℂ) / ModularForm.eta (τ : ℂ)) ^ 12 := by
  obtain ⟨hdiff, hjac, -, -⟩ := hT τ
  obtain ⟨c1, c2, c3⟩ := cubic τ hdiff hjac
  obtain ⟨d1, d2, d3⟩ := hdiff
  obtain ⟨hg2, -, hwp⟩ := scaling Λ ω₁ τ hω hΛ
  obtain ⟨m, n, hmn⟩ := half_coords hω hΛ h2
  have hη : ModularForm.eta (τ : ℂ) ≠ 0 := ModularForm.eta_ne_zero τ.2
  have hD := discr_eta hL hω hΛ hd
  have hpar := (GlobalTheory.T.thetaChar_half_period_eq_zero_iff_odd_add_odd_add τ hjac m n a b hab).1 (by rw [← hmn]; exact hz)
  rw [hg2, hwp t ht, hmn, thetaChar_zero]
  unfold ThetaConstantWeber.JacobiProduct at hjac
  have hY : ∀ e g : ℂ, (12 * (e / ω₁ ^ 2) ^ 2 - g / ω₁ ^ 4) / 4 = (12 * e ^ 2 - g) / 4 / ω₁ ^ 4 := by
    intro e g
    field_simp
  rw [hY]
  have key : ∀ (A B C Y σ : ℂ), (σ = 1 ∨ σ = -1) → A * B * C = 2 * ModularForm.eta (τ : ℂ) ^ 3 →
      Y = σ * ((Real.pi : ℂ) ^ 4 * A ^ 4 * B ^ 4) →
      Y / ω₁ ^ 4 ≠ 0 ∧ ∃ s : ℂ, (s = 1 ∨ s = -1) ∧
        1 / (Y / ω₁ ^ 4) ^ 3 = s * (C / ModularForm.eta (τ : ℂ)) ^ 12 := fun A B C Y σ hσ hABC hY' => by
    have h := alg hω hη hσ hABC hD (Y := Y / ω₁ ^ 4) (by rw [hY'])
    exact ⟨h.1, σ, hσ, h.2⟩
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := hpar
  have hcases : (a = 0 ∧ b = 0) ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
    unfold JacobiThetaHalfCharacteristic.IsEvenChar at hab
    fin_cases a <;> fin_cases b <;> simp_all
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  ·
    have hm : m = 2 * p + 1 := by simpa using hp
    have hn : n = 2 * q + 1 := by simpa using hq
    have e : ((m : ℂ) + (n : ℂ) * (τ : ℂ)) / 2 = (1 + (τ : ℂ)) / 2 + ((p : ℂ) + (q : ℂ) * (τ : ℂ)) := by
      rw [hm, hn]; push_cast; ring
    rw [e, wp_shift]
    refine key (ThetaConstantWeber.thetaConst 0 1 τ) (ThetaConstantWeber.thetaConst 1 0 τ) (ThetaConstantWeber.thetaConst 0 0 τ) _ (-1)
      (Or.inr rfl) (by linear_combination hjac) ?_
    rw [c3]
    linear_combination (-(ThetaConstantWeber.wp τ ((1 + (τ : ℂ)) / 2) - ThetaConstantWeber.wp τ ((τ : ℂ) / 2))) * d2 +
      (-(Real.pi : ℂ) ^ 2 * ThetaConstantWeber.thetaConst 0 1 τ ^ 4) * d3
  ·
    have hm : m = 2 * p := by simp at hp; omega
    have hn : n = 2 * q + 1 := by simpa using hq
    have e : ((m : ℂ) + (n : ℂ) * (τ : ℂ)) / 2 = (τ : ℂ) / 2 + ((p : ℂ) + (q : ℂ) * (τ : ℂ)) := by
      rw [hm, hn]; push_cast; ring
    rw [e, wp_shift]
    refine key (ThetaConstantWeber.thetaConst 0 0 τ) (ThetaConstantWeber.thetaConst 1 0 τ) (ThetaConstantWeber.thetaConst 0 1 τ) _ 1
      (Or.inl rfl) (by linear_combination hjac) ?_
    rw [c2]
    linear_combination (-(ThetaConstantWeber.wp τ ((τ : ℂ) / 2) - ThetaConstantWeber.wp τ ((1 + (τ : ℂ)) / 2))) * d1 +
      ((Real.pi : ℂ) ^ 2 * ThetaConstantWeber.thetaConst 0 0 τ ^ 4) * d3
  ·
    have hm : m = 2 * p + 1 := by simpa using hp
    have hn : n = 2 * q := by simp at hq; omega
    have e : ((m : ℂ) + (n : ℂ) * (τ : ℂ)) / 2 = 1 / 2 + ((p : ℂ) + (q : ℂ) * (τ : ℂ)) := by
      rw [hm, hn]; push_cast; ring
    rw [e, wp_shift]
    refine key (ThetaConstantWeber.thetaConst 0 0 τ) (ThetaConstantWeber.thetaConst 0 1 τ) (ThetaConstantWeber.thetaConst 1 0 τ) _ 1
      (Or.inl rfl) (by linear_combination hjac) ?_
    rw [c1]
    linear_combination (ThetaConstantWeber.wp τ (1 / 2) - ThetaConstantWeber.wp τ ((1 + (τ : ℂ)) / 2)) * d1 +
      ((Real.pi : ℂ) ^ 2 * ThetaConstantWeber.thetaConst 0 0 τ ^ 4) * d2

theorem integral (hT : ThetaConstantWeber.ThetaWeberStatement) (Λ : AddSubgroup ℂ) (ω₁ : ℂ) (τ : UpperHalfPlane)
    (hω : ω₁ ≠ 0) (hΛ : JacobiThetaHalfCharacteristic.IsPeriodLattice Λ ω₁ (τ : ℂ)) (hd : discr Λ = 1)
    (hj : IsIntegral ℤ (1728 * g2 Λ ^ 3)) (a b : Fin 2) (hab : JacobiThetaHalfCharacteristic.IsEvenChar a b) (s : ℂ)
    (hs : s = 1 ∨ s = -1) :
    IsIntegral ℤ (s * (JacobiThetaHalfCharacteristic.thetaChar a b 0 (τ : ℂ) / ModularForm.eta (τ : ℂ)) ^ 12) := by
  obtain ⟨-, -, hW, hC⟩ := hT τ
  obtain ⟨hg2, hg3, -⟩ := scaling Λ ω₁ τ hω hΛ
  have hjj : ThetaConstantWeber.jLat τ = 1728 * g2 Λ ^ 3 := by
    have hdd : (GlobalTheory.periodPairOfTau τ).g₂ ^ 3 - 27 * (GlobalTheory.periodPairOfTau τ).g₃ ^ 2 = ω₁ ^ 12 := by
      have h := hd
      rw [Formalism.MainNotions.TaylorLogMetric.discr, hg2, hg3] at h
      field_simp at h
      linear_combination h
    rw [ThetaConstantWeber.jLat_eq, hdd, hg2]
    field_simp
  obtain ⟨p0, p1, p2⟩ := hW.pow_twelve
  have root : ∀ x : ℂ, (x = ThetaConstantWeber.weberF τ ^ 24 ∨ x = -ThetaConstantWeber.weberF₁ τ ^ 24 ∨ x = -ThetaConstantWeber.weberF₂ τ ^ 24) →
      IsIntegral ℤ x := by
    intro x hx
    have h := congrArg (Polynomial.eval x) hC
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C] at h
    have h0 : (x - 16) ^ 3 - ThetaConstantWeber.jLat τ * x = 0 := by
      rw [h]
      rcases hx with rfl | rfl | rfl <;> simp
    refine (Formalism.HermitianLattices.IntegralLatticeDensity.weber_function_root x (ThetaConstantWeber.jLat τ) 16 (Or.inl rfl) (hjj ▸ hj) ?_).1
    push_cast
    linear_combination h0
  have hx : IsIntegral ℤ ((JacobiThetaHalfCharacteristic.thetaChar a b 0 (τ : ℂ) / ModularForm.eta (τ : ℂ)) ^ 12) := by
    rw [thetaChar_zero]
    have hcases : (a = 0 ∧ b = 0) ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
      unfold JacobiThetaHalfCharacteristic.IsEvenChar at hab
      fin_cases a <;> fin_cases b <;> simp_all
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact p0 ▸ root _ (Or.inl rfl)
    · have := (root _ (Or.inr (Or.inl rfl))).neg
      rw [neg_neg] at this
      exact p1 ▸ this
    · have := (root _ (Or.inr (Or.inr rfl))).neg
      rw [neg_neg] at this
      exact p2 ▸ this
  rcases hs with rfl | rfl
  · simpa using hx
  · simpa using hx.neg

theorem exists_char {Λ : AddSubgroup ℂ} {ω₁ : ℂ} {τ : UpperHalfPlane} {t : ℂ} (hω : ω₁ ≠ 0)
    (hΛ : JacobiThetaHalfCharacteristic.IsPeriodLattice Λ ω₁ (τ : ℂ)) (hj : ThetaConstantWeber.JacobiProduct τ) (h2 : 2 * t ∈ Λ)
    (ht : t ∉ Λ) : ∃ a b : Fin 2, JacobiThetaHalfCharacteristic.IsEvenChar a b ∧ JacobiThetaHalfCharacteristic.thetaChar a b (t / ω₁) (τ : ℂ) = 0 := by
  obtain ⟨m, n, hmn⟩ := half_coords hω hΛ h2
  rw [show t / ω₁ = _ from hmn]
  rcases Int.even_or_odd m with hm | hm <;> rcases Int.even_or_odd n with hn | hn
  · exfalso
    obtain ⟨p, rfl⟩ := hm
    obtain ⟨q, rfl⟩ := hn
    refine ht ((hΛ t).2 ⟨p, q, ?_⟩)
    have : t = ω₁ * (t / ω₁) := by field_simp
    rw [this, hmn]
    push_cast
    ring
  · exact ⟨0, 1, by simp [JacobiThetaHalfCharacteristic.IsEvenChar], (GlobalTheory.T.thetaChar_half_period_eq_zero_iff_odd_add_odd_add τ hj m n 0 1 (by simp [JacobiThetaHalfCharacteristic.IsEvenChar])).2
      ⟨by simpa using hm.add_one, by simpa using hn⟩⟩
  · exact ⟨1, 0, by simp [JacobiThetaHalfCharacteristic.IsEvenChar], (GlobalTheory.T.thetaChar_half_period_eq_zero_iff_odd_add_odd_add τ hj m n 1 0 (by simp [JacobiThetaHalfCharacteristic.IsEvenChar])).2
      ⟨by simpa using hm, by simpa using hn.add_one⟩⟩
  · exact ⟨0, 0, by simp [JacobiThetaHalfCharacteristic.IsEvenChar], (GlobalTheory.T.thetaChar_half_period_eq_zero_iff_odd_add_odd_add τ hj m n 0 0 (by simp [JacobiThetaHalfCharacteristic.IsEvenChar])).2
      ⟨by simpa using hm, by simpa using hn⟩⟩

theorem exists_integral_theta_ratio : EquidistributedConjugates.ConjugatesEquidistributed → PeriodLatticeAgreement.LatticePeriodEta → ThetaConstantWeber.ThetaWeberStatement →
    ∀ (D : D7), Formalism.MainNotions.GL3Theta.admJ D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ)
      [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t →
      ∃ X : M, X ≠ 0 ∧ IsIntegral ℤ (X : ℂ) ∧ ∀ (ρ : M →ₐ[ℚ] ℂ) (ω₁ τ : ℂ), ω₁ ≠ 0 → 0 < τ.im →
        JacobiThetaHalfCharacteristic.IsPeriodLattice (lamConj M ρ (lamOf D cc δ)) ω₁ τ → ∀ a b : Fin 2, JacobiThetaHalfCharacteristic.IsEvenChar a b →
        JacobiThetaHalfCharacteristic.thetaChar a b (t ρ / ω₁) τ = 0 →
        ‖ρ X‖ = (‖JacobiThetaHalfCharacteristic.thetaChar a b 0 τ‖ / ‖ModularForm.eta τ‖) ^ 12 := by
  intro _ hL hT D hJ cc δ M _ t hS
  obtain ⟨e, g, hg, hval, hρ⟩ := GlobalTheory.T.halfPeriod_weierstrassValue_mem_conj D cc δ M t hS
  have crv : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ := ⟨hS.1, hS.2.1⟩
  have hYρ : ∀ ρ : M →ₐ[ℚ] ℂ, ρ ((12 * e ^ 2 - g) / 4) =
      (12 * Formalism.MainNotions.StandardLatticesGL3.wpF (lamConj M ρ (lamOf D cc δ)) (t ρ) ^ 2 - g2 (lamConj M ρ (lamOf D cc δ))) / 4 := by
    intro ρ
    obtain ⟨-, h2, -, h4⟩ := hρ ρ
    rw [h2, h4]
    simp only [map_div₀, map_sub, map_mul, map_pow, map_ofNat]
  obtain ⟨d0, -, n0, -⟩ := hρ M.val
  have h20 := (hS.2.2.2 M.val).1
  have hY0 : (((12 * e ^ 2 - g) / 4 : M) : ℂ) =
      (12 * Formalism.MainNotions.StandardLatticesGL3.wpF (lamOf D cc δ) (t M.val) ^ 2 - g2 (lamOf D cc δ)) / 4 := by
    have h := hYρ M.val
    rw [hval] at h
    exact h
  rw [hval] at d0 n0 h20
  obtain ⟨L, hLL⟩ := (GlobalTheory.ThetaConj.isLat_lamOf crv).exists_periodPair
  obtain ⟨ω, τ, hω, hτ⟩ := GlobalTheory.exists_lattice_eq_mul_tau L
  have hP : JacobiThetaHalfCharacteristic.IsPeriodLattice (lamOf D cc δ) ω (τ : ℂ) := fun x => by
    rw [hLL, hτ]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨n, m, by ring⟩
    · rintro ⟨m, n, rfl⟩
      exact ⟨n, m, by ring⟩
  obtain ⟨a, b, hab, hz⟩ := exists_char hω hP (hT τ).2.1 h20 n0
  obtain ⟨hne, s, hs, hX⟩ := modulus hL hT _ ω τ _ hω hP d0 h20 n0 a b hab hz
  rw [← hY0] at hne hX
  have hYne : ((12 * e ^ 2 - g) / 4 : M) ≠ 0 := fun h => hne (by rw [h]; simp)
  refine ⟨1 / ((12 * e ^ 2 - g) / 4) ^ 3, one_div_ne_zero (pow_ne_zero _ hYne), ?_, ?_⟩
  · have e1 : ((1 / ((12 * e ^ 2 - g) / 4) ^ 3 : M) : ℂ) = 1 / (((12 * e ^ 2 - g) / 4 : M) : ℂ) ^ 3 := by
      push_cast
      rfl
    rw [e1, hX]
    exact integral hT _ ω τ hω hP d0 (hJ cc δ hS.1 hS.2.1) a b hab s hs
  · intro ρ ω₁ τ' hω₁ hτ' hP' a' b' hab' hz'
    obtain ⟨dρ, -, nρ, -⟩ := hρ ρ
    obtain ⟨-, s', hs', hX'⟩ := modulus hL hT _ ω₁ ⟨τ', hτ'⟩ (t ρ) hω₁ hP' dρ (hS.2.2.2 ρ).1 nρ a' b' hab' hz'
    rw [map_div₀, map_one, map_pow, hYρ, hX']
    have hs1 : ‖s'‖ = 1 := by rcases hs' with rfl | rfl <;> simp
    rw [norm_mul, hs1, one_mul, norm_pow, norm_div]

end GlobalTheory.IntegralX
