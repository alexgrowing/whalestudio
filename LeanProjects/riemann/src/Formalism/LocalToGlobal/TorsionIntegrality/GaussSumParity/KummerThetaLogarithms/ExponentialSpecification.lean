import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.LetterShift
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.CoeffSubstLgFOfDegreeOne
import Formalism.GaussJetBounds.GaussJetProofs.NormNatCastEqPowPadicValNat

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp torus)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 UnrOK IsLawOfLog BetaHyp frobVar)
open Formalism.InvariantFactorPaths.G7.FormalGroupLaws (constantCoeff_lgF coeff_one_lgF lgF_subst_inj lgF_funEq map_lgF
  rescale_lgF)

namespace FormalExponential

section Alg

variable {K : Type} [Field K]

theorem isUnit_coeff_one (l : ℕ) (hl : 2 ≤ l) : IsUnit (PowerSeries.coeff 1 (lgF K l)) := by
  rw [coeff_one_lgF l hl]
  exact isUnit_one

theorem expF_eq (l : ℕ) (hl : 2 ≤ l) :
    expF K l = PowerSeries.substInvOfIsUnit (lgF K l) (isUnit_coeff_one l hl) := by
  unfold expF
  rw [dif_pos (isUnit_coeff_one l hl)]

theorem inj (l : ℕ) (hl : 2 ≤ l) (a b : PowerSeries K) (ha : PowerSeries.constantCoeff a = 0)
    (hb : PowerSeries.constantCoeff b = 0)
    (h : PowerSeries.subst a (lgF K l) = PowerSeries.subst b (lgF K l)) : a = b :=
  lgF_subst_inj (ι := Unit) l hl a b ha hb h

theorem isMul_root {ζ : K} {l : ℕ} (hl : 2 ≤ l) (hζ : ζ ^ (l ^ 2 - 1) = 1) :
    IsMul l ζ (PowerSeries.C ζ * PowerSeries.X) := by
  refine ⟨by simp, ?_⟩
  rw [← rescale_lgF hζ hl, PowerSeries.rescale_eq_subst, PowerSeries.smul_eq_C_mul]

theorem at_variable_C_mul_X {ι : Type} (x : ι) (ζ : K) :
    at1 x (PowerSeries.C ζ * PowerSeries.X) =
      MvPowerSeries.C ζ * (MvPowerSeries.X x : MvPowerSeries ι K) := by
  unfold at1
  rw [PowerSeries.subst_mul (PowerSeries.HasSubst.X x), PowerSeries.subst_C,
    PowerSeries.subst_X (PowerSeries.HasSubst.X x)]

end Alg

section Normed

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_eq_one_of_pow {a : K} {n : ℕ} (hn : n ≠ 0) (h : a ^ n = 1) : ‖a‖ = 1 := by
  have h1 : ‖a‖ ^ n = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg a) hn).1 h1

theorem norm_pow_sub_pow_le {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (i : ℕ) :
    ‖a ^ i - b ^ i‖ ≤ ‖a - b‖ := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : a ^ (i + 1) - b ^ (i + 1) = a * (a ^ i - b ^ i) + (a - b) * b ^ i := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖a‖ * ‖a ^ i - b ^ i‖ ≤ 1 * ‖a - b‖ :=
            mul_le_mul ha ih (norm_nonneg _) zero_le_one
        _ = ‖a - b‖ := one_mul _
    · rw [norm_mul, norm_pow]
      calc ‖a - b‖ * ‖b‖ ^ i ≤ ‖a - b‖ * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hb) (norm_nonneg _)
        _ = ‖a - b‖ := mul_one _

theorem root_eq_of_norm_lt {a b : K} {N : ℕ} (hN : ‖(N : K)‖ = 1) (ha : a ^ N = 1)
    (hb : b ^ N = 1) (hab : ‖a - b‖ < 1) : a = b := by
  by_contra hne
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp at hN
  have na : ‖a‖ = 1 := norm_eq_one_of_pow hN0 ha
  have nb : ‖b‖ = 1 := norm_eq_one_of_pow hN0 hb
  have hS : (∑ i ∈ Finset.range N, a ^ i * b ^ (N - 1 - i)) = 0 := by
    have h := geom_sum₂_mul a b N
    rw [ha, hb, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hne)
  have hT : (∑ i ∈ Finset.range N, b ^ i * b ^ (N - 1 - i)) = (N : K) * b ^ (N - 1) := by
    rw [Finset.sum_congr rfl (g := fun _ => b ^ (N - 1))]
    · simp
    · intro i hi
      have : i < N := Finset.mem_range.1 hi
      rw [← pow_add]
      congr 1
      omega
  have hD : (N : K) * b ^ (N - 1) =
      - ∑ i ∈ Finset.range N, (a ^ i - b ^ i) * b ^ (N - 1 - i) := by
    simp only [sub_mul, Finset.sum_sub_distrib, hS, hT]
    ring
  have h1 : ‖(N : K) * b ^ (N - 1)‖ = 1 := by
    rw [norm_mul, norm_pow, hN, nb, one_pow, one_mul]
  have h2 : ‖(N : K) * b ^ (N - 1)‖ ≤ ‖a - b‖ := by
    rw [hD, norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
    rw [norm_mul, norm_pow, nb, one_pow, mul_one]
    exact norm_pow_sub_pow_le na.le nb.le i
  rw [h1] at h2
  exact absurd hab (not_lt.2 h2)

theorem integral_X : Integral (PowerSeries.X : MvPowerSeries Unit K) := by
  intro n
  change ‖MvPowerSeries.coeff n (MvPowerSeries.X () : MvPowerSeries Unit K)‖ ≤ 1
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

theorem ip_lgF (l : ℕ) (σ : K →+* K) (hl : 2 ≤ l) (hlK : (l : K) ≠ 0) :
    IP l σ (lgF K l : MvPowerSeries Unit K) := by
  refine ⟨constantCoeff_lgF l hl, ?_⟩
  have h1 : MvPowerSeries.map (σ.comp σ) (lgF K l : MvPowerSeries Unit K) = lgF K l :=
    map_lgF (σ.comp σ) l
  have h2 : (lgF K l : MvPowerSeries Unit K) - MvPowerSeries.C ((l : K)⁻¹) *
      frobVar (l ^ 2) (lgF K l : MvPowerSeries Unit K) = (PowerSeries.X : PowerSeries K) := by
    have h := lgF_funEq (K := K) l hl hlK
    rw [PowerSeries.smul_eq_C_mul] at h
    exact h
  rw [h1, h2]
  exact integral_X

end Normed

end FormalExponential

open FormalExponential

theorem exponential_specification : ExpSpec := by
  intro K _ l hl
  have h0 := constantCoeff_lgF (K := K) l hl
  have hc : PowerSeries.constantCoeff (expF K l) = 0 := by
    rw [expF_eq l hl]
    exact PowerSeries.constantCoeff_substInvOfIsUnit _ _
  have h1 : PowerSeries.subst (expF K l) (lgF K l) = (PowerSeries.X : PowerSeries K) := by
    rw [expF_eq l hl]
    exact PowerSeries.subst_substInvOfIsUnit_right _ h0 _
  refine ⟨hc, h1, ?_, ?_⟩
  · rw [expF_eq l hl]
    exact PowerSeries.subst_substInvOfIsUnit_left _ h0 _
  · intro ex hex h
    exact inj l hl ex _ hex hc (h.trans h1.symm)

theorem teichmuller_sigma : TeichSigma := by
  intro K _ _ _ l d σ hU hd ζ hζ
  obtain ⟨hp, _, hnl, _, hσ⟩ := hU
  have hlt : ‖(l : K)‖ < 1 := by
    rw [hnl]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hpos : 1 ≤ l ^ d := Nat.one_le_pow _ _ hp.pos
  have hnd : ¬ l ∣ l ^ d - 1 := by
    intro h
    have h1 : l ∣ l ^ d := dvd_pow_self l (by omega)
    have h2 : l ∣ 1 := by
      have := (Nat.dvd_sub h1 h)
      rwa [Nat.sub_sub_self hpos] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  have hN : ‖((l ^ d - 1 : ℕ) : K)‖ = 1 := Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd hp hlt hnd
  have hN0 : l ^ d - 1 ≠ 0 := by
    intro h
    rw [h] at hnd
    exact hnd (dvd_zero l)
  have nζ : ‖ζ‖ = 1 := norm_eq_one_of_pow hN0 hζ
  refine root_eq_of_norm_lt hN ?_ ?_ ?_
  · rw [← map_pow, hζ, map_one]
  · rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  · refine lt_of_le_of_lt (hσ ζ nζ.le) ?_
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

theorem MulSpec_of : ExpSpec → IPLemma → IPClosure → MulSpec := by
  intro hE hL hC K _ _ _ l σ hU c
  have hp : l.Prime := hU.1
  have hl : 2 ≤ l := hp.two_le
  have hlK : (l : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨hc, h1, _, _⟩ := hE K l hl
  have h0 := constantCoeff_lgF (K := K) l hl
  have huniq : ∀ e e' : PowerSeries K, IsMul l c e → IsMul l c e' → e = e' := fun e e' he he' =>
    inj l hl e e' he.1 he'.1 (he.2.trans he'.2.symm)
  refine ⟨?_, huniq, ?_⟩
  · have hg0 : PowerSeries.constantCoeff (PowerSeries.C c * lgF K l) = 0 := by
      rw [map_mul, h0, mul_zero]
    refine ⟨PowerSeries.subst (PowerSeries.C c * lgF K l) (expF K l),
      PowerSeries.constantCoeff_subst_eq_zero hg0 _ hc, ?_⟩
    rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hc)
      (PowerSeries.HasSubst.of_constantCoeff_zero' hg0), h1,
      PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' hg0)]
  · intro hc1 hσc e he n
    have hip : IP l σ (MvPowerSeries.C c * (lgF K l : MvPowerSeries Unit K)) :=
      (hC K l σ Unit).2.2 c _ hc1 hσc (ip_lgF l σ hl hlK)
    obtain ⟨h, hh0, hhI, hh⟩ := hL K l σ hU Unit _ hip
    have : e = h := huniq e h he ⟨hh0, hh⟩
    rw [this]
    exact hhI (Finsupp.single () n)

theorem BetaHypOfF_of : TeichSigma → BetaHypOfF := by
  intro hT K _ _ _ l σ hU F be0 hF1 hF2
  have hp : l.Prime := hU.1
  have hl : 2 ≤ l := hp.two_le
  refine ⟨hF1.1, hF1.2.1, hF1.2.2, ?_⟩
  intro ζ hζ
  have hN0 : l ^ 2 - 1 ≠ 0 := by
    have : 2 ^ 2 ≤ l ^ 2 := Nat.pow_le_pow_left hl 2
    omega
  have nζ : ‖ζ‖ = 1 := norm_eq_one_of_pow hN0 hζ
  have hσ : σ ζ = ζ ^ l := hT K l 2 σ hU (by norm_num) ζ hζ
  have hζl : (ζ ^ l) ^ (l ^ 2 - 1) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have hσσ : σ (σ ζ) = ζ := by
    rw [hσ, map_pow, hσ, ← pow_mul, ← sq]
    have : l ^ 2 = (l ^ 2 - 1) + 1 := by omega
    rw [this, pow_succ, hζ, one_mul]
  have h := hF2 ζ nζ.le hσσ (PowerSeries.C ζ * PowerSeries.X)
    (PowerSeries.C (ζ ^ l) * PowerSeries.X) (isMul_root hl hζ) (by rw [hσ]; exact isMul_root hl hζl)
  rw [at_variable_C_mul_X, at_variable_C_mul_X] at h
  exact h

end Formalism.L2.Th1.D
