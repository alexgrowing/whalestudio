import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixVariablesDeterminantPowMonomialShapeStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LegendreBoundsFactorialMultiIndexCapelli
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuation

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.DetPowContent

theorem rpow_digitSum_le (p : ℕ) (hp : 2 ≤ p) (n : ℕ) :
    (p : ℝ) ^ ((((Nat.digits p n).sum : ℕ) : ℝ) / ((p : ℝ) - 1)) ≤ (n : ℝ) + 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hdig : ∀ d : ℕ, d < p → (p : ℝ) ^ ((d : ℝ) / ((p : ℝ) - 1)) ≤ (d : ℝ) + 1 := by
    intro d hd
    have hd' : (d : ℝ) ≤ (p : ℝ) - 1 := by
      have h1 : d + 1 ≤ p := hd
      have h2 : (d : ℝ) + 1 ≤ p := by exact_mod_cast h1
      linarith
    have ht0 : 0 ≤ (d : ℝ) / ((p : ℝ) - 1) := div_nonneg (Nat.cast_nonneg _) hpos.le
    have ht1 : (d : ℝ) / ((p : ℝ) - 1) ≤ 1 := (div_le_one hpos).mpr hd'
    have h := Real.geom_mean_le_arith_mean2_weighted ht0 (sub_nonneg.mpr ht1)
      (by linarith : (0 : ℝ) ≤ p) zero_le_one (add_sub_cancel _ _)
    rw [Real.one_rpow, mul_one] at h
    have e : (d : ℝ) / ((p : ℝ) - 1) * p + (1 - (d : ℝ) / ((p : ℝ) - 1)) * 1 = (d : ℝ) + 1 := by
      field_simp
      ring
    linarith
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [Nat.digits_def' (by omega) hn, List.sum_cons, Nat.cast_add, add_div,
        Real.rpow_add (by linarith)]
      have h1 := ih (n / p) (Nat.div_lt_self hn (by omega))
      have h2 := hdig (n % p) (Nat.mod_lt _ (by omega))
      have hmod : ((n % p : ℕ) : ℝ) + (p : ℝ) * ((n / p : ℕ) : ℝ) = n := by
        exact_mod_cast Nat.mod_add_div n p
      have hlt : ((n % p : ℕ) : ℝ) + 1 ≤ p := by
        exact_mod_cast (Nat.mod_lt n (by omega : 0 < p))
      have hm0 : (0 : ℝ) ≤ ((n / p : ℕ) : ℝ) := Nat.cast_nonneg _
      calc (p : ℝ) ^ (((n % p : ℕ) : ℝ) / ((p : ℝ) - 1)) *
            (p : ℝ) ^ ((((Nat.digits p (n / p)).sum : ℕ) : ℝ) / ((p : ℝ) - 1))
          ≤ (((n % p : ℕ) : ℝ) + 1) * (((n / p : ℕ) : ℝ) + 1) :=
            mul_le_mul h2 h1 (Real.rpow_nonneg (by linarith) _) (by positivity)
        _ ≤ (n : ℝ) + 1 := by nlinarith

theorem digitSum_le_logb (p : ℕ) (hp : 2 ≤ p) (n : ℕ) :
    (((Nat.digits p n).sum : ℕ) : ℝ) ≤ ((p : ℝ) - 1) * Real.logb p ((n : ℝ) + 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have h2 : (((Nat.digits p n).sum : ℕ) : ℝ) / ((p : ℝ) - 1) ≤ Real.logb p ((n : ℝ) + 1) :=
    (Real.le_logb_iff_rpow_le hp1 (by positivity)).mpr (rpow_digitSum_le p hp n)
  rw [div_le_iff₀ hpos] at h2
  linarith [mul_comm (Real.logb p ((n : ℝ) + 1)) ((p : ℝ) - 1)]

theorem padicValNat_factorial_ge (p : ℕ) (hp : p.Prime) (N : ℕ) :
    (N : ℝ) / ((p : ℝ) - 1) - Real.logb p ((N : ℝ) + 1) ≤ (padicValNat p N.factorial : ℝ) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have h := digitSum_le_logb p hp.two_le N
  have h3 : (((Nat.digits p N).sum : ℕ) : ℝ) / ((p : ℝ) - 1) ≤ Real.logb p ((N : ℝ) + 1) := by
    rw [div_le_iff₀ hpos]
    linarith [mul_comm (Real.logb p ((N : ℝ) + 1)) ((p : ℝ) - 1)]
  rw [GlobalTheory.LegendreBounds.legendre_real p hp N, sub_div]
  linarith

theorem toE_coe (r : ℝ) : toE (r : WithTop ℝ) = (r : EReal) := rfl

theorem toE_mono {x y : WithTop ℝ} (h : x ≤ y) : toE x ≤ toE y := by
  unfold toE
  exact WithBot.coe_le_coe.mpr h

theorem val_mfact {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {p : ℕ} (hp : p.Prime)
    (hv : v (p : C) = 1) {σ : Type} [Fintype σ] (α : σ →₀ ℕ) :
    v (mfact α : C) = ((∑ k, (padicValNat p (α k).factorial : ℝ) : ℝ) : WithTop ℝ) := by
  classical
  have hne : (∏ k, (α k).factorial) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k _ => Nat.factorial_ne_zero _)
  have e : (mfact α : C) = ((∏ k, (α k).factorial : ℕ) : C) := by
    unfold mfact
    rw [Finsupp.prod_fintype _ _ (fun k => by simp), Nat.cast_prod]
  rw [e, ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.natCast_eq_factorization v hp hv hne, Nat.factorization_def _ hp,
    GlobalTheory.LegendreBounds.padicValNat_prod_factorial p hp Finset.univ α]

theorem content_detPow_bounds : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (i c : ℕ), content v (detPow C i c) ≤ (((i * c : ℝ) / (p - 1) : ℝ) : EReal) ∧ ((((i * c : ℝ) / (p - 1) - (i : ℝ) ^ 2 * Real.logb p (c + 1) : ℝ)) : EReal) ≤ content v (detPow C i c) := by
  intro C _ _ v p hp hv i c
  classical
  obtain ⟨-, hint, hdiag, hrows⟩ := GlobalTheory.T.matrixVariablesDeterminantPow_monomial_shape C i c
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have key : ∀ α ∈ (detPow C i c).support,
      (∑ k, ((α k : ℕ) : ℝ)) = (i : ℝ) * c ∧ ∀ k, α k ≤ c := by
    intro α hα
    obtain ⟨-, hb⟩ := hrows α hα
    refine ⟨?_, ?_⟩
    · rw [Fintype.sum_sigma]
      have hb' : ∀ b : Fin i, (∑ a : Fin i, ((α ⟨b, a⟩ : ℕ) : ℝ)) = c := by
        intro b
        exact_mod_cast hb b
      simp only [hb', Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    · rintro ⟨b, a⟩
      rw [← hb b]
      exact Finset.single_le_sum (f := fun a' => α ⟨b, a'⟩) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ a)
  have upS : ∀ α ∈ (detPow C i c).support,
      (∑ k, (padicValNat p (α k).factorial : ℝ)) ≤ (i * c : ℝ) / (p - 1) := by
    intro α hα
    calc (∑ k, (padicValNat p (α k).factorial : ℝ))
        ≤ ∑ k, ((α k : ℕ) : ℝ) / ((p : ℝ) - 1) :=
          Finset.sum_le_sum (fun k _ => GlobalTheory.LegendreBounds.upper p hp (α k))
      _ = (i * c : ℝ) / (p - 1) := by rw [← Finset.sum_div, (key α hα).1]
  have loS : ∀ α ∈ (detPow C i c).support,
      (i * c : ℝ) / (p - 1) - (i : ℝ) ^ 2 * Real.logb p (c + 1)
        ≤ ∑ k, (padicValNat p (α k).factorial : ℝ) := by
    intro α hα
    obtain ⟨hsum, hle⟩ := key α hα
    have h1 : ∀ k, ((α k : ℕ) : ℝ) / ((p : ℝ) - 1) - Real.logb p ((c : ℝ) + 1)
        ≤ (padicValNat p (α k).factorial : ℝ) := by
      intro k
      have hl : Real.logb p (((α k : ℕ) : ℝ) + 1) ≤ Real.logb p ((c : ℝ) + 1) :=
        Real.logb_le_logb_of_le hp1 (by positivity) (by exact_mod_cast Nat.add_le_add_right (hle k) 1)
      have := padicValNat_factorial_ge p hp (α k)
      linarith
    calc (i * c : ℝ) / (p - 1) - (i : ℝ) ^ 2 * Real.logb p (c + 1)
        = ∑ k, (((α k : ℕ) : ℝ) / ((p : ℝ) - 1) - Real.logb p ((c : ℝ) + 1)) := by
          rw [Finset.sum_sub_distrib, ← Finset.sum_div, hsum]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_sigma, Fintype.card_fin,
            smul_eq_mul, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ ∑ k, (padicValNat p (α k).factorial : ℝ) := Finset.sum_le_sum (fun k _ => h1 k)
  constructor
  · set α0 : (Σ _ : Fin i, Fin i) →₀ ℕ := ∑ a : Fin i, Finsupp.single ⟨a, a⟩ c with hα0
    have hmem : α0 ∈ (detPow C i c).support := by
      rw [MvPolynomial.mem_support_iff, hdiag]
      exact one_ne_zero
    calc content v (detPow C i c) ≤ toE (v ((detPow C i c).coeff α0 * mfact α0)) := by
          unfold content
          exact iInf₂_le α0 hmem
      _ = (((∑ k, (padicValNat p (α0 k).factorial : ℝ)) : ℝ) : EReal) := by
          rw [hdiag, one_mul, val_mfact v hp hv α0, toE_coe]
      _ ≤ _ := EReal.coe_le_coe_iff.mpr (upS α0 hmem)
  · unfold content
    refine le_iInf₂ (fun α hα => ?_)
    obtain ⟨n, hn⟩ := hint α
    rw [← toE_coe]
    apply toE_mono
    rw [AddValuation.map_mul, val_mfact v hp hv α, hn]
    exact le_trans (WithTop.coe_le_coe.mpr (loS α hα))
      (le_add_of_nonneg_left (ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.intCast_nonneg v n))

end GlobalTheory.DetPowContent
