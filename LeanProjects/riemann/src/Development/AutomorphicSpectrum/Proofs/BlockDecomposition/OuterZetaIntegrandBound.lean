import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Aq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTemperedBoundDetOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaIntegrandEqIteratedIntegral
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2Unfolding.PtB

section L

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

omit [MeasurableSpace F] [BorelSpace F] in

theorem norm_mp_eq (a : Fˣ) (z : ℂ) : ‖mp a z‖ = (modulus (a : F) : ℝ) ^ z.re := by
  have h0 : (0 : ℝ) < (modulus (a : F) : ℝ) := by exact_mod_cast modulus_pos a.ne_zero
  rw [mp]
  exact Complex.norm_cpow_eq_rpow_re_of_pos h0 z

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in

theorem diag_torus_factor_scalar (a b : Fˣ) : (dg2 (a * b) b : GL (Fin 2) F) = dg2 b b * dg2 a 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in

theorem hI_central (p : Fˣ × Fˣ × GL (Fin 2) F) : hI p = dg2 p.2.1 p.2.1 * (dg2 p.1 1 * p.2.2) := by
  rw [hI, diag_torus_factor_scalar, mul_assoc]

omit [MeasurableSpace F] [BorelSpace F] in

theorem sup_norm_second_vector_diag_mul (c b : Fˣ) (x : GL (Fin 2) F) :
    mx (e2r (dg2 c b * x)) = (modulus (b : F) : ℝ) * mx (e2r x) := by
  have e0 : (dg2 c b * x).val 1 0 = (b : F) * x.val 1 0 := by
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have e1 : (dg2 c b * x).val 1 1 = (b : F) * x.val 1 1 := by
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have hb : (0 : ℝ) ≤ (modulus (b : F) : ℝ) := NNReal.coe_nonneg _
  simp only [mx, e2r, Matrix.cons_val_zero, Matrix.cons_val_one, e0, e1, modulus_mul, NNReal.coe_mul]
  exact (mul_max_of_nonneg _ _ hb).symm

theorem sup_norm_second_vector_maxCompact {k : GL (Fin 2) F} (hk : k ∈ K2 F) : mx (e2r k) = 1 := by
  have := GlobalTheory.CompanionTheory.GJTwo.WhB.mx_bottom_integral hk
  simpa [mx, e2r] using this

theorem modulus_det_hI_mul (p : Fˣ × Fˣ × GL (Fin 2) F) (hp : p.2.2 ∈ K2 F) (g : GL (Fin 2) F) :
    (modulus ((hI p * g).val).det : ℝ) =
      (modulus (p.1 : F) : ℝ) * (modulus (p.2.1 : F) : ℝ) ^ 2 * (modulus (g.val).det : ℝ) := by
  have hk : modulus ((p.2.2).val).det = 1 := GlobalTheory.CompanionTheory.GJTwo.WhB.modulus_det_integral hp
  have hd : ((dg2 (p.1 * p.2.1) p.2.1 : GL (Fin 2) F).val).det = (p.1 : F) * p.2.1 * p.2.1 := by
    simp [dg2, Matrix.det_fin_two]
  rw [hI, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hd, modulus_mul, modulus_mul,
    modulus_mul, modulus_mul, hk]
  push_cast
  ring

end L

theorem main : ForS fun F _ _ _ _ _ _ ψ => ∀ (W₀ W' : GL (Fin 2) F → ℂ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (s : ℂ) (C₀ C₁ C₂ B R ε : ℝ),
  0 ≤ C₀ → 0 ≤ C₁ → 0 ≤ C₂ → 0 < ε → ε < 1 / 2 →
  (∀ (a : Fˣ) g, W₀ (dg2 a a * g) = W₀ g) →
  (∀ (a : Fˣ), ∀ k ∈ GLnLocal.integralGL F 2, ‖W₀ (dg2 a 1 * k)‖ ≤ C₀ * (modulus (a : F) : ℝ) ^ (1 / 2 - ε) ∧
    (W₀ (dg2 a 1 * k) ≠ 0 → (modulus (a : F) : ℝ) ≤ B)) →
  (∀ h : GL (Fin 2) F, ‖W' h‖ ≤ C₁ * ((modulus (h.val).det : ℝ) / mx (e2r h) ^ 2) ^ (1 / 2 - ε)) →
  (∀ A ξ, ‖pFT ψ Φ A ξ‖ ≤ C₂ ∧ (pFT ψ Φ A ξ ≠ 0 → (∀ i j, (modulus (A i j) : ℝ) ≤ R) ∧ mx ξ ≤ R)) →
  ∀ (g : GL (Fin 2) F) (p : Fˣ × Fˣ × GL (Fin 2) F), p.2.2 ∈ K2 F →
    ‖Bq ψ W₀ W' Φ s g (hI p)‖ ≤ C₀ * C₁ * C₂ * Mj R B s.re ε g p := by
  intro F _ _ _ _ _ _ ψ _ W₀ W' Φ s C₀ C₁ C₂ B R ε h0 h1 h2 hε hε2 hcen hW₀ hW' hP g p hk
  have hW0eq : W₀ (hI p) = W₀ (dg2 p.1 1 * p.2.2) := by rw [hI_central, hcen]
  have hmx : mx (e2r (hI p)) = (modulus (p.2.1 : F) : ℝ) := by
    rw [hI, sup_norm_second_vector_diag_mul, sup_norm_second_vector_maxCompact hk, mul_one]
  have hA : (0 : ℝ) < (modulus (p.1 : F) : ℝ) := by exact_mod_cast modulus_pos p.1.ne_zero
  have hB : (0 : ℝ) < (modulus (p.2.1 : F) : ℝ) := by exact_mod_cast modulus_pos p.2.1.ne_zero
  by_cases hc : (∀ i j, (modulus (g.val i j) : ℝ) ≤ R) ∧ (modulus (p.2.1 : F) : ℝ) ≤ R ∧
      (modulus (p.1 : F) : ℝ) ≤ B
  · rw [Mj, if_pos hc]
    set A : ℝ := (modulus (p.1 : F) : ℝ) with hAdef
    set b : ℝ := (modulus (p.2.1 : F) : ℝ) with hbdef
    set Q : ℝ := (modulus (g.val).det : ℝ) / mx (e2r (p.2.2 * g)) ^ 2 with hQdef
    have hQ : 0 ≤ Q := by
      have hm : 0 ≤ mx (e2r (p.2.2 * g)) := le_max_of_le_left (NNReal.coe_nonneg _)
      exact div_nonneg (NNReal.coe_nonneg _) (by positivity)
    have e1 : ‖W₀ (hI p)‖ ≤ C₀ * A ^ (1 / 2 - ε) := by
      rw [hW0eq]; exact (hW₀ p.1 p.2.2 hk).1
    have hq : (modulus ((hI p * g).val).det : ℝ) / mx (e2r (hI p * g)) ^ 2 = A * Q := by
      have hrow : mx (e2r (hI p * g)) = b * mx (e2r (p.2.2 * g)) := by
        rw [hI, mul_assoc, sup_norm_second_vector_diag_mul]
      rw [modulus_det_hI_mul p hk, hrow, hQdef, mul_pow, ← hAdef, ← hbdef,
        show A * b ^ 2 * (modulus (g.val).det : ℝ) = b ^ 2 * (A * (modulus (g.val).det : ℝ)) by ring,
        mul_div_mul_left _ _ (pow_ne_zero 2 hB.ne'), mul_div_assoc]
    have e2 : ‖W' (hI p * g)‖ ≤ C₁ * (A * Q) ^ (1 / 2 - ε) := by
      have := hW' (hI p * g)
      rwa [hq] at this
    have e3 : ‖pFT ψ Φ g.val (e2r (hI p))‖ ≤ C₂ := (hP _ _).1
    have e4 : ‖mp (GeneralLinearGroup.det (hI p)) s‖ = A ^ s.re * b ^ (2 * s.re) := by
      have h2s : (2 * s).re = 2 * s.re := by simp
      rw [GlobalTheory.CompanionTheory.DampedZetaMajorant.Iter.mp_det_hI p hk, norm_mul, norm_mp_eq, norm_mp_eq, h2s]
    have hexp : A ^ (s.re + 1 - 2 * ε) = A ^ (1 / 2 - ε) * A ^ (1 / 2 - ε) * A ^ s.re := by
      rw [← Real.rpow_add hA, ← Real.rpow_add hA]
      congr 1; ring
    have hsplit : (A * Q) ^ (1 / 2 - ε) = A ^ (1 / 2 - ε) * Q ^ (1 / 2 - ε) :=
      Real.mul_rpow hA.le hQ
    have n1 : 0 ≤ A ^ (1 / 2 - ε) := Real.rpow_nonneg hA.le _
    have n2 : 0 ≤ (A * Q) ^ (1 / 2 - ε) := Real.rpow_nonneg (mul_nonneg hA.le hQ) _
    calc ‖Bq ψ W₀ W' Φ s g (hI p)‖
        = ‖W₀ (hI p)‖ * ‖W' (hI p * g)‖ * ‖pFT ψ Φ g.val (e2r (hI p))‖ *
            ‖mp (GeneralLinearGroup.det (hI p)) s‖ := by simp only [Bq, norm_mul]
      _ ≤ (C₀ * A ^ (1 / 2 - ε)) * (C₁ * (A * Q) ^ (1 / 2 - ε)) * C₂ * (A ^ s.re * b ^ (2 * s.re)) := by
          rw [e4]
          have n3 : 0 ≤ A ^ s.re * b ^ (2 * s.re) :=
            mul_nonneg (Real.rpow_nonneg hA.le _) (Real.rpow_nonneg hB.le _)
          gcongr
      _ = C₀ * C₁ * C₂ * (A ^ (s.re + 1 - 2 * ε) * b ^ (2 * s.re) * Q ^ (1 / 2 - ε)) := by
          rw [hexp, hsplit]; ring
  · rw [Mj, if_neg hc, mul_zero]
    have hz : Bq ψ W₀ W' Φ s g (hI p) = 0 := by
      by_contra hne
      have hw : W₀ (hI p) ≠ 0 := fun e => hne (by simp [Bq, e])
      have hf : pFT ψ Φ g.val (e2r (hI p)) ≠ 0 := fun e => hne (by simp [Bq, e])
      obtain ⟨r1, r2⟩ := (hP _ _).2 hf
      rw [hmx] at r2
      rw [hW0eq] at hw
      exact hc ⟨r1, r2, (hW₀ p.1 p.2.2 hk).2 hw⟩
    rw [hz, norm_zero]

end GlobalTheory.CompanionTheory.GL2Unfolding.PtB
