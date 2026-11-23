import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanCoefficientNonzero.Development

open MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace PI.BICNZ

open Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.MainNotions.S.Pv.BetaCut

theorem sf_of_haar {k r : ℕ} {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) : SigmaFinite μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  infer_instance

theorem itD_const_mul (a : ℂ) (f : ℝ → ℂ) (n : ℕ) :
    iteratedDeriv n (fun y => a * f y) = fun y => a * iteratedDeriv n f y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    exact deriv_const_mul_field' a

theorem oneMinusDD_prod (c : ℂ) (f g : ℝ → ℂ) (t₁ t₂ : ℝ) :
    oneMinusDD (fun a b => c * f a * g b) t₁ t₂ =
      c * (f t₁ - iteratedDeriv 2 f t₁) * (g t₂ - iteratedDeriv 2 g t₂) := by
  have e3 : ∀ (K : ℂ) (u : ℝ → ℂ) (t : ℝ), iteratedDeriv 2 (fun x => K * u x) t = K * iteratedDeriv 2 u t := by
    intro K u t
    rw [itD_const_mul]
  have e1 : ∀ x, iteratedDeriv 2 (fun y => c * f x * g y) t₂ = c * f x * iteratedDeriv 2 g t₂ := fun x =>
    e3 (c * f x) g t₂
  have e2 : (fun x => c * f x * g t₂ - iteratedDeriv 2 (fun y => c * f x * g y) t₂) =
      fun x => (c * (g t₂ - iteratedDeriv 2 g t₂)) * f x := by
    funext x
    rw [e1]
    ring
  show (c * f t₁ * g t₂ - iteratedDeriv 2 (fun y => c * f t₁ * g y) t₂) -
    iteratedDeriv 2 (fun x => c * f x * g t₂ - iteratedDeriv 2 (fun y => c * f x * g y) t₂) t₁ = _
  rw [e2, e3, e3]
  ring

theorem chi_eq_zero {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) {t : ℝ} (ht : t ≤ 0) : D.χ t = 0 := by
  by_contra hne
  have hs : t ∈ tsupport D.χ := subset_tsupport _ hne
  have := (D.χ_supp hs).1
  linarith

theorem chi_hasCompactSupport {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) : HasCompactSupport D.χ :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) (D.χ_supp.trans Set.Ioo_subset_Icc_self)

theorem regBracket_eq {k r : ℕ} {Wp Wq H : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (D : RealPlaceData k r Wp Wq) (σ : Mat k r → (H →L[ℂ] H)) (v v' : H) (ξ : Wp) (ξ' : Wq)
    (d : ℝ) (p : SS k r)
    (hΦ : ∀ t : ℝ × ℝ, 0 < t.1 → 0 < t.2 →
      Ph D (coefM σ v v' ξ ξ') (coefM σ v v' ξ ξ') (dilation₂ t p) =
        (d : ℂ)⁻¹ * Lf D σ v ξ (p.1.1, conjM (aDil k r t.1) p.1.2) *
          Rf D σ v' ξ' (p.2.1, conjM (aDil k r t.2) p.2.2)) :
    regBracket D (coefM σ v v' ξ ξ') (coefM σ v v' ξ ξ') p =
      fun a b => (d : ℂ)⁻¹ * H1 D σ v ξ p.1 a * H2 D σ v' ξ' p.2 b := by
  funext a b
  simp only [regBracket, H1, H2]
  by_cases ha : 0 < a
  · by_cases hb : 0 < b
    · have h := hΦ (a, b) ha hb
      dsimp only at h
      rw [h]
      have hk : (a * b) ^ kap k r = a ^ kap k r * b ^ kap k r := by
        first
        | exact mul_pow a b _
        | exact Real.mul_rpow ha.le hb.le
      rw [hk]
      simp only [Complex.ofReal_mul]
      ring
    · have h0 : D.χ b = 0 := chi_eq_zero D (not_lt.mp hb)
      simp [h0]
  · have h0 : D.χ a = 0 := chi_eq_zero D (not_lt.mp ha)
    simp [h0]

theorem hasCompactSupport_left_profile {k r : ℕ} {Wp Wq H : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (D : RealPlaceData k r Wp Wq) (σ : Mat k r → (H →L[ℂ] H)) (v : H) (ξ : Wp) (x : Mt k r × Mt k r) :
    HasCompactSupport (H1 D σ v ξ x) := by
  have h1 : HasCompactSupport (fun t : ℝ => D.χ t * t ^ kap k r) := (chi_hasCompactSupport D).mul_right
  have h2 : HasCompactSupport (fun t : ℝ => ((D.χ t * t ^ kap k r : ℝ) : ℂ)) := h1.comp_left Complex.ofReal_zero
  exact h2.mul_right (f' := fun t : ℝ => Lf D σ v ξ (x.1, conjM (aDil k r t) x.2))

theorem hasCompactSupport_right_profile {k r : ℕ} {Wp Wq H : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (D : RealPlaceData k r Wp Wq) (σ : Mat k r → (H →L[ℂ] H)) (v' : H) (ξ' : Wq) (x : Mt k r × Mt k r) :
    HasCompactSupport (H2 D σ v' ξ' x) := by
  have h1 : HasCompactSupport (fun t : ℝ => D.χ t * t ^ kap k r) := (chi_hasCompactSupport D).mul_right
  have h2 : HasCompactSupport (fun t : ℝ => ((D.χ t * t ^ kap k r : ℝ) : ℂ)) := h1.comp_left Complex.ofReal_zero
  exact h2.mul_right (f' := fun t : ℝ => Rf D σ v' ξ' (x.1, conjM (aDil k r t) x.2))

theorem ae_inSS {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) :
    ∀ᵐ p ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)), D.inSS p := by
  haveI := sf_of_haar D.haarW
  haveI := sf_of_haar D.haarN
  haveI := sf_of_haar D.haarW'
  have hW : ∀ᵐ x ∂D.μW, Matrix.of x ∈ UWset k r D.z := by
    rw [ae_iff]
    exact D.haarW.conc
  have hN : ∀ᵐ x ∂D.μN, Matrix.of x ∈ Nset k r := by
    rw [ae_iff]
    exact D.haarN.conc
  have hW' : ∀ᵐ x ∂D.μW', Matrix.of x ∈ UWset k r D.z' := by
    rw [ae_iff]
    exact D.haarW'.conc
  have h1 : ∀ᵐ q ∂(D.μW.prod D.μN), Matrix.of q.1 ∈ UWset k r D.z ∧ Matrix.of q.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hW).and (Measure.quasiMeasurePreserving_snd.ae hN)
  have h2 : ∀ᵐ q ∂(D.μW'.prod D.μN), Matrix.of q.1 ∈ UWset k r D.z' ∧ Matrix.of q.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hW').and (Measure.quasiMeasurePreserving_snd.ae hN)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae h1, Measure.quasiMeasurePreserving_snd.ae h2]
    with p hp1 hp2
  exact ⟨hp1.1, hp1.2, hp2.1, hp2.2⟩

theorem exp_split (t₁ t₂ a b : ℝ) :
    Complex.exp (Complex.I * (((1 : ℝ) * t₁ * a - (1 : ℝ) * t₂ * b : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((a * t₁ : ℝ) : ℂ)) * Complex.exp (Complex.I * ((-b * t₂ : ℝ) : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem betaFactor_of (hP : PhiAt) (hL : LeftProfileContDiffTwo) (hR : RightProfileContDiffTwo) : BetaFactor := by
  intro k r Wp Wq _ _ _ _ _ _ D ε lm H _ _ _ σ hHC hDS
  obtain ⟨d, hd, hΦ⟩ := hP k r Wp Wq D ε lm H σ hHC hDS
  refine ⟨d, hd, fun v v' ξ ξ' hv hv' => ?_⟩
  haveI := sf_of_haar D.haarW
  haveI := sf_of_haar D.haarN
  haveI := sf_of_haar D.haarW'
  have hpt : ∀ p : SS k r, D.inSS p →
      ((((1 + (1 : ℝ) ^ 2 * lam k r D.z (Matrix.of p.1.2) ^ 2)⁻¹ *
        (1 + (1 : ℝ) ^ 2 * lam k r D.z' (Matrix.of p.2.2) ^ 2)⁻¹ : ℝ) : ℂ) *
      ∫ t : ℝ × ℝ, oneMinusDD (regBracket D (coefM σ v v' ξ ξ') (coefM σ v v' ξ ξ') p) t.1 t.2 *
        Complex.exp (Complex.I * (((1 : ℝ) * t.1 * lam k r D.z (Matrix.of p.1.2) -
          (1 : ℝ) * t.2 * lam k r D.z' (Matrix.of p.2.2) : ℝ) : ℂ))) =
      (d : ℂ)⁻¹ * I1 D σ v ξ p.1 * I2 D σ v' ξ' p.2 := by
    intro p hp
    set a := lam k r D.z (Matrix.of p.1.2) with ha
    set b := lam k r D.z' (Matrix.of p.2.2) with hb
    have hreg := regBracket_eq D σ v v' ξ ξ' d p (fun t h1 h2 => hΦ v v' ξ ξ' p hp t h1 h2)
    have hA : ContDiff ℝ 2 (H1 D σ v ξ p.1) := hL k r Wp Wq D ε lm H σ hHC hDS v ξ hv p.1 hp.1 hp.2.1
    have hB : ContDiff ℝ 2 (H2 D σ v' ξ' p.2) := hR k r Wp Wq D ε lm H σ hHC hDS v' ξ' hv' p.2 hp.2.2.1 hp.2.2.2
    have iA := Formalism.FourierDecayAlt.P.integration_by_parts_regularised (H1 D σ v ξ p.1) hA (hasCompactSupport_left_profile D σ v ξ p.1) a
    have iB := Formalism.FourierDecayAlt.P.integration_by_parts_regularised (H2 D σ v' ξ' p.2) hB (hasCompactSupport_right_profile D σ v' ξ' p.2) (-b)
    have hsplit : (∫ t : ℝ × ℝ, oneMinusDD (regBracket D (coefM σ v v' ξ ξ') (coefM σ v v' ξ ξ') p) t.1 t.2 *
        Complex.exp (Complex.I * (((1 : ℝ) * t.1 * a - (1 : ℝ) * t.2 * b : ℝ) : ℂ))) =
        (d : ℂ)⁻¹ * ((∫ s : ℝ, (H1 D σ v ξ p.1 s - iteratedDeriv 2 (H1 D σ v ξ p.1) s) *
            Complex.exp (Complex.I * ((a * s : ℝ) : ℂ))) *
          (∫ s : ℝ, (H2 D σ v' ξ' p.2 s - iteratedDeriv 2 (H2 D σ v' ξ' p.2) s) *
            Complex.exp (Complex.I * ((-b * s : ℝ) : ℂ)))) := by
      rw [hreg]
      have e : ∀ t : ℝ × ℝ, oneMinusDD (fun a' b' => (d : ℂ)⁻¹ * H1 D σ v ξ p.1 a' * H2 D σ v' ξ' p.2 b') t.1 t.2 *
          Complex.exp (Complex.I * (((1 : ℝ) * t.1 * a - (1 : ℝ) * t.2 * b : ℝ) : ℂ)) =
          (d : ℂ)⁻¹ * (((H1 D σ v ξ p.1 t.1 - iteratedDeriv 2 (H1 D σ v ξ p.1) t.1) *
              Complex.exp (Complex.I * ((a * t.1 : ℝ) : ℂ))) *
            ((H2 D σ v' ξ' p.2 t.2 - iteratedDeriv 2 (H2 D σ v' ξ' p.2) t.2) *
              Complex.exp (Complex.I * ((-b * t.2 : ℝ) : ℂ)))) := by
        intro t
        rw [oneMinusDD_prod, exp_split]
        ring
      simp_rw [e]
      rw [integral_const_mul, Measure.volume_eq_prod]
      congr 1
      exact integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (fun s => (H1 D σ v ξ p.1 s - iteratedDeriv 2 (H1 D σ v ξ p.1) s) *
            Complex.exp (Complex.I * ((a * s : ℝ) : ℂ)))
        (fun s => (H2 D σ v' ξ' p.2 s - iteratedDeriv 2 (H2 D σ v' ξ' p.2) s) *
            Complex.exp (Complex.I * ((-b * s : ℝ) : ℂ)))
    rw [hsplit, iA, iB]
    unfold I1 I2
    rw [← ha, ← hb]
    have h1 : (1 + a ^ 2 : ℝ) ≠ 0 := by positivity
    have h2 : (1 + b ^ 2 : ℝ) ≠ 0 := by positivity
    have hw : ((1 + (1 : ℝ) ^ 2 * a ^ 2)⁻¹ * (1 + (1 : ℝ) ^ 2 * b ^ 2)⁻¹) * ((1 + a ^ 2) * (1 + (-b) ^ 2)) = (1 : ℝ) := by
      rw [neg_sq, one_pow, one_mul, one_mul]
      field_simp
    have hw' : ((((1 + (1 : ℝ) ^ 2 * a ^ 2)⁻¹ * (1 + (1 : ℝ) ^ 2 * b ^ 2)⁻¹ : ℝ) : ℂ)) *
        (((1 + a ^ 2 : ℝ) : ℂ) * ((1 + (-b) ^ 2 : ℝ) : ℂ)) = 1 := by
      exact_mod_cast hw
    linear_combination ((d : ℂ)⁻¹ * (∫ t : ℝ, H1 D σ v ξ p.1 t * Complex.exp (Complex.I * ((a * t : ℝ) : ℂ))) *
      (∫ t : ℝ, H2 D σ v' ξ' p.2 t * Complex.exp (Complex.I * ((-b * t : ℝ) : ℂ)))) * hw'
  unfold betaInf betaInfTau RealPlaceData.μSS
  refine (integral_congr_ae (g := fun p : SS k r => (d : ℂ)⁻¹ * (I1 D σ v ξ p.1 * I2 D σ v' ξ' p.2)) ?_).trans ?_
  · filter_upwards [ae_inSS D] with p hp
    rw [← mul_assoc]
    exact hpt p hp
  · rw [integral_const_mul, mul_assoc]
    congr 1
    exact integral_prod_mul (μ := D.μW.prod D.μN) (ν := D.μW'.prod D.μN) (I1 D σ v ξ) (I2 D σ v' ξ')

end PI.BICNZ
