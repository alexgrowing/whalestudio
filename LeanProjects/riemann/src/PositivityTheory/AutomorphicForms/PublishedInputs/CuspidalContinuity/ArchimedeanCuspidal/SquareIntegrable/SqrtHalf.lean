import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SumIccTelescope
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.IndicatorIntegersEq

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel NNReal

namespace Ad3.SchwartzSpaceL2.UnramifiedWhittakerGL2

theorem sqrt_half (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℤ) :
    ((((residueCard F : ℝ≥0) ^ (-n) : ℝ≥0) : ℝ) : ℂ) ^ (1 / 2 : ℂ) = Spherical.sqrtQ F ^ (-n) := by
  set s := NNReal.sqrt (residueCard F : ℝ≥0) with hs
  have hs2 : (residueCard F : ℝ≥0) = s ^ 2 := (NNReal.sq_sqrt _).symm
  have hpow : ((residueCard F : ℝ≥0)) ^ (-n) = (s ^ (-n)) ^ 2 := by
    rw [hs2, ← zpow_natCast, ← _root_.zpow_mul, ← zpow_natCast, ← _root_.zpow_mul, mul_comm]
  have key : ∀ r : ℝ, 0 ≤ r → ((r ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) = (r : ℂ) := by
    intro r hr
    have : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, ← Complex.ofReal_cpow (sq_nonneg r), ← Real.sqrt_eq_rpow, Real.sqrt_sq hr]
  rw [hpow, NNReal.coe_pow, key _ (NNReal.coe_nonneg _), NNReal.coe_zpow, Complex.ofReal_zpow]
  rfl

theorem alg (X Y S P : ℂ) (hX : X ≠ 0) (hY : Y ≠ 0) (hS : S ≠ 0) (a b j : ℤ) :
    Y ^ (a + b) * S ^ (-(a + b)) * (P * (S ^ 2) ^ b * (X⁻¹ * Y) ^ j) =
      P * S ^ (-(a - b)) * (X ^ (-j) * Y ^ (a + b + j)) := by
  have hS2 : (S ^ 2) ^ b = (S ^ b) ^ 2 := by
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast]
  rw [mul_zpow, _root_.inv_zpow, hS2]
  simp only [zpow_add₀ hY, zpow_add₀ hS, _root_.zpow_neg, zpow_sub₀ hS]
  field_simp

end Ad3.SchwartzSpaceL2.UnramifiedWhittakerGL2

namespace Ad3.SchwartzSpaceL2

theorem punr : SUnr := by
  intro F _ _ _ _ _ _ ψ hψ μ₁ μ₂ _ _ hr₁ hr₂
  funext g
  obtain ⟨⟨u, k⟩, hu, hk, hg⟩ := Spherical.exists_iwasawa_decomp g
  have hψ₀ : ∀ x ∈ 𝒪[F], (Circle.coeHom.compAddChar ψ) x = 1 := by
    intro x hx
    have := (isTrivialOn_iff hψ.1 hψ.2.1 0).2 (le_of_eq hψ.2.2) x (mem_valBall_zero_iff.2 hx)
    simp [this]
  rw [hg]
  generalize Iwasawa.iwasawaExponent F 2 g = l
  rw [Spherical.sphericalWhittaker_apply hψ₀ _ hu hk l]
  rw [UnramifiedWhittakerGL2.W_formula ψ hψ μ₁ μ₂ hr₁ hr₂ hu hk l, UnramifiedWhittakerGL2.sqrt_half]
  have hpsi : Whittaker.psiN (Circle.coeHom.compAddChar ψ) u =
      (ψ ((u : Matrix (Fin 2) (Fin 2) F) 0 1) : ℂ) := by
    simp [Whittaker.psiN, Whittaker.superdiagSum, Fin.sum_univ_two]
    rfl
  rw [hpsi]
  have hanti : Antitone l ↔ l 1 ≤ l 0 := by
    refine ⟨fun h => h (Fin.zero_le 1), fun h i j hij => ?_⟩
    fin_cases i <;> fin_cases j <;> simp_all
  by_cases hl : l 1 ≤ l 0
  · rw [if_pos (hanti.2 hl), UnramifiedWhittakerGL2.evalAt_schur_two _ l hl, Spherical.halfModulus_eq]
    have hrho : Spherical.rhoPair l = l 0 - l 1 := by
      simp [Spherical.rhoPair, Fin.sum_univ_two]
      ring
    have hq : (residueCard F : ℂ) = Spherical.sqrtQ F ^ 2 := (Spherical.sqrtQ_sq).symm
    rw [hrho, hq, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Units.val_mul,
      Units.val_inv_eq_inv_val]
    exact UnramifiedWhittakerGL2.alg _ _ _ _ (Units.ne_zero _) (Units.ne_zero _) Spherical.sqrtQ_ne_zero _ _ _
  · rw [if_neg (mt hanti.1 hl), Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    simp

end Ad3.SchwartzSpaceL2
