import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FirstDeriv
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TopsChoicePartA
import Formalism.FormalGroupLog.FormalGroupLogProofs.HomPsSubstMvSubst
import Formalism.TorsionNormIteration.LubinTateExample
import Formalism.FormalGroupWitt.FormalGroupWittProofs.FrobSqV

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp)

namespace FormalGroupLaws

section Alg

variable {K : Type} [Field K]

theorem constantCoeff_lgF (p : ℕ) (hp : 2 ≤ p) : PowerSeries.constantCoeff (lgF K p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, lgF, PowerSeries.coeff_mk]
  simp

theorem coeff_one_lgF (p : ℕ) (hp : 2 ≤ p) : PowerSeries.coeff 1 (lgF K p) = 1 := by
  have h1 : (1 : ℕ) ≠ p ^ 2 := by nlinarith
  rw [lgF, PowerSeries.coeff_mk]
  simp [Finset.sum_range_succ, h1]

theorem map_lgF {L : Type} [Field L] (φ : K →+* L) (p : ℕ) :
    PowerSeries.map φ (lgF K p) = lgF L p := by
  ext n
  simp only [lgF, PowerSeries.coeff_map, PowerSeries.coeff_mk, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs <;> simp

theorem cob_eq_zero_iff (F : MvPowerSeries (Fin 2) K) (f : PowerSeries K) :
    cob F f = 0 ↔ PowerSeries.subst F f = at1 0 f + at1 1 f := by
  rw [cob, sub_sub, sub_eq_zero]

theorem constantCoeff_inVar {ι : Type} (x : ι) (f : PowerSeries K)
    (hf : PowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (at1 x f) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (by simp) f hf

theorem lgF_subst_inj {ι : Type} (p : ℕ) (hp : 2 ≤ p) (a b : MvPowerSeries ι K)
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0)
    (h : PowerSeries.subst a (lgF K p) = PowerSeries.subst b (lgF K p)) : a = b :=
  Formalism.G.substInjective K ι (lgF K p) a b (constantCoeff_lgF p hp) (coeff_one_lgF p hp) ha hb h

theorem law_exists (p : ℕ) (hp : 2 ≤ p) :
    ∃ F : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff F = 0 ∧ cob F (lgF K p) = 0 := by
  have h0 : MvPowerSeries.constantCoeff (at1 (0 : Fin 2) (lgF K p) + at1 1 (lgF K p)) = 0 := by
    rw [map_add, constantCoeff_inVar _ _ (constantCoeff_lgF p hp),
      constantCoeff_inVar _ _ (constantCoeff_lgF p hp), add_zero]
  obtain ⟨F, hF0, hF⟩ := Formalism.LT.SolveExists_proof K (Fin 2) (lgF K p) _
    (constantCoeff_lgF p hp) (coeff_one_lgF p hp) h0
  exact ⟨F, hF0, (cob_eq_zero_iff F _).mpr hF⟩

theorem law_unique (p : ℕ) (hp : 2 ≤ p) (F F' : MvPowerSeries (Fin 2) K)
    (h0 : MvPowerSeries.constantCoeff F = 0) (h0' : MvPowerSeries.constantCoeff F' = 0)
    (h : cob F (lgF K p) = 0) (h' : cob F' (lgF K p) = 0) : F = F' :=
  lgF_subst_inj p hp F F' h0 h0'
    (by rw [(cob_eq_zero_iff F _).mp h, (cob_eq_zero_iff F' _).mp h'])

theorem map_inVar {L ι : Type} [Field L] (φ : K →+* L) (x : ι) (f : PowerSeries K) :
    MvPowerSeries.map φ (at1 x f) = at1 x (PowerSeries.map φ f) := by
  rw [at1, at1, PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)),
    MvPowerSeries.map_X]

theorem map_cob {L : Type} [Field L] (φ : K →+* L) (F : MvPowerSeries (Fin 2) K)
    (hF : MvPowerSeries.constantCoeff F = 0) (f : PowerSeries K) :
    MvPowerSeries.map φ (cob F f) = cob (MvPowerSeries.map φ F) (PowerSeries.map φ f) := by
  rw [cob, cob, map_sub, map_sub, map_inVar, map_inVar,
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hF)]

theorem map_law {L : Type} [Field L] (φ : K →+* L) (p : ℕ) (F : MvPowerSeries (Fin 2) K)
    (hF : MvPowerSeries.constantCoeff F = 0) (h : cob F (lgF K p) = 0) :
    MvPowerSeries.constantCoeff (MvPowerSeries.map φ F) = 0 ∧
      cob (MvPowerSeries.map φ F) (lgF L p) = 0 := by
  refine ⟨by rw [MvPowerSeries.constantCoeff_map, hF, map_zero], ?_⟩
  rw [← map_lgF φ p, ← map_cob φ F hF, h, map_zero]

private theorem coeff_lgF_pow_sq_pow_eq_inv_pow (p : ℕ) (hp : 2 ≤ p) (j : ℕ) :
    PowerSeries.coeff ((p ^ 2) ^ j) (lgF K p) = ((p : K) ^ j)⁻¹ := by
  have hq : 2 ≤ p ^ 2 := by nlinarith
  rw [lgF, PowerSeries.coeff_mk, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [if_neg]
    intro h
    exact hij (Nat.pow_right_injective hq h).symm
  · intro hj
    exfalso
    apply hj
    rw [Finset.mem_range]
    have : j < (p ^ 2) ^ j := Nat.lt_pow_self (by omega)
    omega

private theorem coeff_lgF_eq_zero_of_ne_pow_sq_pow (p n : ℕ) (h : ∀ j, n ≠ (p ^ 2) ^ j) :
    PowerSeries.coeff n (lgF K p) = 0 := by
  rw [lgF, PowerSeries.coeff_mk]
  exact Finset.sum_eq_zero (fun i _ => if_neg (h i))

theorem lgF_funEq (p : ℕ) (hp : 2 ≤ p) (hpK : (p : K) ≠ 0) :
    lgF K p - (p : K)⁻¹ • PowerSeries.subst ((PowerSeries.X : PowerSeries K) ^ (p ^ 2)) (lgF K p) =
      PowerSeries.X := by
  have hq0 : p ^ 2 ≠ 0 := by positivity
  have hq : 2 ≤ p ^ 2 := by nlinarith
  ext n
  rw [map_sub, PowerSeries.coeff_smul, PowerSeries.coeff_subst_X_pow hq0, PowerSeries.coeff_X]
  by_cases hn : ∃ j, n = (p ^ 2) ^ j
  · obtain ⟨j, rfl⟩ := hn
    cases j with
    | zero =>
      have hnd : ¬ p ^ 2 ∣ 1 := fun h => by have := Nat.le_of_dvd one_pos h; omega
      simp only [pow_zero]
      rw [if_neg hnd, coeff_one_lgF p hp]
      simp
    | succ j =>
      have hd : p ^ 2 ∣ (p ^ 2) ^ (j + 1) := dvd_pow_self _ (Nat.succ_ne_zero j)
      have hdiv : (p ^ 2) ^ (j + 1) / p ^ 2 = (p ^ 2) ^ j := by
        rw [pow_succ, Nat.mul_div_cancel _ (by positivity)]
      have hne1 : (p ^ 2) ^ (j + 1) ≠ 1 := ne_of_gt (Nat.one_lt_pow (Nat.succ_ne_zero j) (by omega))
      rw [if_pos hd, hdiv, coeff_lgF_pow_sq_pow_eq_inv_pow p hp, coeff_lgF_pow_sq_pow_eq_inv_pow p hp, if_neg hne1]
      simp [pow_succ, mul_inv, mul_comm]
  · push_neg at hn
    rw [coeff_lgF_eq_zero_of_ne_pow_sq_pow p n hn]
    have hn1 : n ≠ 1 := fun h => hn 0 (by simp [h])
    rw [if_neg hn1]
    split_ifs with hd
    · have hn' : ∀ j, n / p ^ 2 ≠ (p ^ 2) ^ j := by
        intro j hj
        apply hn (j + 1)
        rw [pow_succ, ← hj, Nat.div_mul_cancel hd]
      simp [coeff_lgF_eq_zero_of_ne_pow_sq_pow p _ hn']
    · simp

theorem subst_subst {ι κ : Type} {b : ι → MvPowerSeries κ K} (hb : MvPowerSeries.HasSubst b)
    {a : MvPowerSeries ι K} (ha : PowerSeries.HasSubst a) (f : PowerSeries K) :
    MvPowerSeries.subst b (PowerSeries.subst a f) =
      PowerSeries.subst (MvPowerSeries.subst b a) f := by
  unfold PowerSeries.subst
  rw [MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.const ha) hb]

theorem subst_single_var {ι κ : Type} {b : ι → MvPowerSeries κ K} (hb : MvPowerSeries.HasSubst b)
    (x : ι) (f : PowerSeries K) :
    MvPowerSeries.subst b (at1 x f) = PowerSeries.subst (b x) f := by
  rw [at1, subst_subst hb (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)),
    MvPowerSeries.subst_X hb]

theorem zeta_pow {ζ : K} {p : ℕ} (hζ : ζ ^ (p ^ 2 - 1) = 1) (hp : 2 ≤ p) (j : ℕ) :
    ζ ^ ((p ^ 2) ^ j) = ζ := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hq : p ^ 2 - 1 + 1 = p ^ 2 := Nat.sub_add_cancel (by nlinarith)
    rw [pow_succ, pow_mul, ih, ← hq, pow_succ, hζ, one_mul]

theorem rescale_lgF {ζ : K} {p : ℕ} (hζ : ζ ^ (p ^ 2 - 1) = 1) (hp : 2 ≤ p) :
    PowerSeries.rescale ζ (lgF K p) = PowerSeries.C ζ * lgF K p := by
  ext n
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C_mul]
  by_cases hn : ∃ j, n = (p ^ 2) ^ j
  · obtain ⟨j, rfl⟩ := hn
    rw [zeta_pow hζ hp j]
  · push_neg at hn
    rw [coeff_lgF_eq_zero_of_ne_pow_sq_pow p n hn]
    simp

theorem lgF_subst_C_mul {ι : Type} {ζ : K} {p : ℕ} (hζ : ζ ^ (p ^ 2 - 1) = 1) (hp : 2 ≤ p)
    (G : MvPowerSeries ι K) (hG : MvPowerSeries.constantCoeff G = 0) :
    PowerSeries.subst (MvPowerSeries.C ζ * G) (lgF K p) =
      MvPowerSeries.C ζ * PowerSeries.subst G (lgF K p) := by
  have hG' : PowerSeries.HasSubst G := PowerSeries.HasSubst.of_constantCoeff_zero hG
  have hX : PowerSeries.HasSubst (ζ • PowerSeries.X : PowerSeries K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp; exact Or.inr PowerSeries.constantCoeff_X)
  have h1 : PowerSeries.subst G (ζ • PowerSeries.X : PowerSeries K) = MvPowerSeries.C ζ * G := by
    rw [PowerSeries.subst_smul hG', PowerSeries.subst_X hG', MvPowerSeries.smul_eq_C_mul]
  rw [← h1, ← PowerSeries.subst_comp_subst_apply hX hG', ← PowerSeries.rescale_eq_subst,
    rescale_lgF hζ hp, ← PowerSeries.smul_eq_C_mul, PowerSeries.subst_smul hG',
    MvPowerSeries.smul_eq_C_mul]

theorem coeff_subst_lgF_of_degree_one {ι : Type} (p : ℕ) (hp : 2 ≤ p) (F : MvPowerSeries ι K)
    (hF : MvPowerSeries.constantCoeff F = 0) (n : ι →₀ ℕ) (hn : n.degree = 1) :
    MvPowerSeries.coeff n (PowerSeries.subst F (lgF K p)) = MvPowerSeries.coeff n F := by
  classical
  have hdvd : (PowerSeries.X : PowerSeries K) ^ 2 ∣ lgF K p - PowerSeries.X := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    interval_cases m
    · simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_lgF p hp]
    · simp [coeff_one_lgF p hp]
  obtain ⟨r, hr⟩ := hdvd
  have hF' : PowerSeries.HasSubst F := PowerSeries.HasSubst.of_constantCoeff_zero hF
  have hl : lgF K p = PowerSeries.X + PowerSeries.X ^ 2 * r := by rw [← hr]; ring
  rw [hl, PowerSeries.subst_add hF', PowerSeries.subst_mul hF', PowerSeries.subst_pow hF',
    PowerSeries.subst_X hF', map_add]
  suffices h : MvPowerSeries.coeff n (F ^ 2 * PowerSeries.subst F r) = 0 by rw [h, add_zero]
  rw [pow_two, mul_assoc, MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  by_cases hi : i = 0
  · subst hi
    simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hF]
  · have hj : j = 0 := by
      have h1 := congrArg Finsupp.degree hij
      rw [map_add, hn] at h1
      have h2 : i.degree ≠ 0 := fun h => hi ((Finsupp.degree_eq_zero_iff i).mp h)
      exact (Finsupp.degree_eq_zero_iff j).mp (by omega)
    subst hj
    simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hF]

end Alg

theorem not_dvd_den {p : ℕ} [Fact p.Prime] (r : ℚ) (h : ‖(r : ℚ_[p])‖ ≤ 1) : ¬ p ∣ r.den := by
  intro hd
  have hp := Fact.out (p := p.Prime)
  rw [Padic.eq_padicNorm] at h
  have hden : padicNorm p ((r.den : ℤ) : ℚ) < 1 :=
    (padicNorm.int_lt_one_iff _).mpr (by exact_mod_cast hd)
  have hnum : padicNorm p ((r.num : ℤ) : ℚ) < 1 := by
    have hc : ((r.num : ℤ) : ℚ) = r * ((r.den : ℤ) : ℚ) := by
      push_cast
      exact (Rat.mul_den_eq_num r).symm
    rw [hc, padicNorm.mul]
    calc padicNorm p r * padicNorm p ((r.den : ℤ) : ℚ) ≤ 1 * padicNorm p ((r.den : ℤ) : ℚ) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast h) (padicNorm.nonneg _)
      _ < 1 := by rw [one_mul]; exact hden
  have h1 : (p : ℤ) ∣ r.num := (padicNorm.int_lt_one_iff _).mp hnum
  have h2 : p ∣ r.num.natAbs := Int.natCast_dvd.mp h1
  have h3 := Nat.dvd_gcd h2 hd
  rw [Nat.Coprime.gcd_eq_one r.reduced] at h3
  exact hp.one_lt.ne' (Nat.dvd_one.mp h3)

theorem norm_ratCast_le_one {K : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ}
    (hp : p.Prime) (hnp : ‖(p : K)‖ < 1) (r : ℚ) (hr : ¬ p ∣ r.den) : ‖(r : K)‖ ≤ 1 := by
  have hden : 1 ≤ ‖(r.den : K)‖ := by
    have hcop : Nat.Coprime r.den p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hr).symm
    have hab : (r.den : ℤ) * Nat.gcdA r.den p + (p : ℤ) * Nat.gcdB r.den p = 1 := by
      rw [← Nat.gcd_eq_gcd_ab, Nat.Coprime.gcd_eq_one hcop, Nat.cast_one]
    have h1 : (1 : K) = (r.den : K) * ((Nat.gcdA r.den p : ℤ) : K) + (p : K) * ((Nat.gcdB r.den p : ℤ) : K) := by
      have h1' := congrArg (Int.cast : ℤ → K) hab
      push_cast at h1'
      exact h1'.symm
    by_contra hlt
    push_neg at hlt
    have hm := IsUltrametricDist.norm_add_le_max ((r.den : K) * ((Nat.gcdA r.den p : ℤ) : K))
      ((p : K) * ((Nat.gcdB r.den p : ℤ) : K))
    rw [← h1, norm_one, norm_mul, norm_mul] at hm
    have ha := IsUltrametricDist.norm_intCast_le_one K (Nat.gcdA r.den p)
    have hb := IsUltrametricDist.norm_intCast_le_one K (Nat.gcdB r.den p)
    have e1 : ‖(r.den : K)‖ * ‖((Nat.gcdA r.den p : ℤ) : K)‖ < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) ha) hlt
    have e2 : ‖(p : K)‖ * ‖((Nat.gcdB r.den p : ℤ) : K)‖ < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) hb) hnp
    exact absurd hm (not_le.mpr (max_lt e1 e2))
  have hnum : ‖(r.num : K)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one K r.num
  rw [Rat.cast_def, norm_div]
  exact div_le_one_of_le₀ (hnum.trans hden) (norm_nonneg _)

theorem funEqType_lgF (p : ℕ) [hp : Fact p.Prime] :
    Formalism.G.IsFunEqType p (p ^ 2) (RingHom.id ℚ_[p]) (lgF ℚ_[p] p) := by
  have hp2 : 2 ≤ p := hp.out.two_le
  have hpK : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  unfold Formalism.G.IsFunEqType
  simp only [PowerSeries.map_id, id]
  rw [lgF_funEq p hp2 hpK]
  intro n
  rw [PowerSeries.coeff_X]
  split_ifs <;> simp

theorem law_integral {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ)
    (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) (F : MvPowerSeries (Fin 2) K)
    (hF0 : MvPowerSeries.constantCoeff F = 0) (hF : cob F (lgF K p) = 0) : Integral F := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 := hp.two_le
  obtain ⟨FQ, hFQ0, hFQ⟩ := law_exists (K := ℚ) p hp2
  obtain ⟨G, hG0, hGint, hGlog⟩ := Formalism.LT.funEqGroup ℚ_[p] p (p ^ 2) (RingHom.id ℚ_[p])
    (Formalism.FG.frobenius_lift_padic_square p) (lgF ℚ_[p] p) (constantCoeff_lgF p hp2)
    (coeff_one_lgF p hp2) (funEqType_lgF p)
  have hGcob : cob G (lgF ℚ_[p] p) = 0 := (cob_eq_zero_iff G _).mpr hGlog
  obtain ⟨h0p, hcp⟩ := map_law (Rat.castHom ℚ_[p]) p FQ hFQ0 hFQ
  have hEq := law_unique p hp2 _ G h0p hG0 hcp hGcob
  have hQp : ∀ n, ‖((MvPowerSeries.coeff n FQ : ℚ) : ℚ_[p])‖ ≤ 1 := by
    intro n
    have h1 := hGint n
    rw [← hEq, MvPowerSeries.coeff_map] at h1
    simpa using h1
  obtain ⟨h0K, hcK⟩ := map_law (Rat.castHom K) p FQ hFQ0 hFQ
  have hEqK := law_unique p hp2 _ F h0K hF0 hcK hF
  have hnp' : ‖(p : K)‖ < 1 := by
    rw [hnp]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  intro n
  rw [← hEqK, MvPowerSeries.coeff_map]
  have h2 := norm_ratCast_le_one hp hnp' (MvPowerSeries.coeff n FQ) (not_dvd_den _ (hQp n))
  simpa using h2

end FormalGroupLaws

open FormalGroupLaws

theorem formal_law_exists : LawExists := by
  intro K _ _ _ p hp hnp
  refine ⟨?_, fun F F' h0 h0' h h' => law_unique p hp.two_le F F' h0 h0' h h'⟩
  obtain ⟨F, hF0, hF⟩ := law_exists (K := K) p hp.two_le
  exact ⟨F, hF0, law_integral p hp hnp F hF0 hF, hF⟩

theorem formal_law_symmetric : LawSymm := by
  intro K _ _ _ p hp hnp F hF
  obtain ⟨hF0, _, hFc⟩ := hF
  have hp2 := hp.two_le
  have hFl : PowerSeries.subst F (lgF K p) =
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) (lgF K p) +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) (lgF K p) :=
    (cob_eq_zero_iff F _).mp hFc
  have hFlA : PowerSeries.subst F (lgF K p) = at1 0 (lgF K p) + at1 1 (lgF K p) :=
    (cob_eq_zero_iff F _).mp hFc
  have hl0 := constantCoeff_lgF (K := K) p hp2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro σ
    obtain ⟨h0, hc⟩ := map_law σ p F hF0 hFc
    exact law_unique p hp2 _ F h0 hF0 hc hFc
  · intro ζ hζ
    have hb : MvPowerSeries.HasSubst
        (fun a : Fin 2 => MvPowerSeries.C ζ * (MvPowerSeries.X a : MvPowerSeries (Fin 2) K)) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (fun a => by simp)
    apply lgF_subst_inj p hp2
    · exact MvPowerSeries.constantCoeff_subst_eq_zero hb (fun a => by simp) hF0
    · simp [hF0]
    · rw [← subst_subst hb (PowerSeries.HasSubst.of_constantCoeff_zero hF0), hFlA,
        MvPowerSeries.subst_add hb, subst_single_var hb, subst_single_var hb]
      beta_reduce
      rw [lgF_subst_C_mul hζ hp2 (MvPowerSeries.X (0 : Fin 2)) (by simp),
        lgF_subst_C_mul hζ hp2 (MvPowerSeries.X (1 : Fin 2)) (by simp),
        lgF_subst_C_mul hζ hp2 F hF0, hFl, mul_add]
  · intro n hn
    rw [← coeff_subst_lgF_of_degree_one p hp2 F hF0 n hn, hFl, map_add,
      coeff_subst_lgF_of_degree_one p hp2 (MvPowerSeries.X (0 : Fin 2)) (by simp) n hn,
      coeff_subst_lgF_of_degree_one p hp2 (MvPowerSeries.X (1 : Fin 2)) (by simp) n hn]
    have hsum : n 0 + n 1 = 1 := by
      have h1 := hn
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at h1
      exact h1
    have hne : Finsupp.single (1 : Fin 2) 1 ≠ Finsupp.single 0 1 := by
      rw [Ne, Finsupp.single_left_inj one_ne_zero]
      decide
    rcases Nat.eq_zero_or_pos (n 0) with h0 | h0
    · have hn' : n = Finsupp.single 1 1 := by
        ext i
        fin_cases i <;> simp [h0] <;> omega
      rw [hn', MvPowerSeries.coeff_X, MvPowerSeries.coeff_X, if_neg hne, if_pos rfl, zero_add]
    · have hn' : n = Finsupp.single 0 1 := by
        ext i
        fin_cases i <;> simp <;> omega
      rw [hn', MvPowerSeries.coeff_X, MvPowerSeries.coeff_X, if_pos rfl, if_neg hne.symm, add_zero]
  · have hb : MvPowerSeries.HasSubst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0] :=
      Formalism.G.LogP.hs2 (by simp) (by simp)
    have hz : PowerSeries.subst (0 : MvPowerSeries (Fin 2) K) (lgF K p) = 0 := by
      obtain ⟨u, hu⟩ := PowerSeries.X_dvd_iff.mpr hl0
      have h0s : PowerSeries.HasSubst (0 : MvPowerSeries (Fin 2) K) :=
        PowerSeries.HasSubst.of_constantCoeff_zero (map_zero _)
      rw [hu, PowerSeries.subst_mul h0s, PowerSeries.subst_X h0s, zero_mul]
    apply lgF_subst_inj p hp2
    · exact MvPowerSeries.constantCoeff_subst_eq_zero hb (fun a => by fin_cases a <;> simp) hF0
    · simp
    · rw [← subst_subst hb (PowerSeries.HasSubst.of_constantCoeff_zero hF0), hFlA,
        MvPowerSeries.subst_add hb, subst_single_var hb, subst_single_var hb]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [hz, add_zero]

end Formalism.InvariantFactorPaths.G7
