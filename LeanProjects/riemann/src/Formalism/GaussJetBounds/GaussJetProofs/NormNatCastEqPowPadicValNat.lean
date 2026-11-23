import Formalism.GaussJetBounds.GenLogInverse
import Formalism.GaussJetBounds.GaussJetProofs.SubstitutionWeightBound
import Formalism.IncomingBounds.FlowDegreeBounds.ProdRangeEqFactorialMulProdIco
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormNatCastEqOneOfNotDvd

noncomputable section
open scoped BigOperators

universe u v

namespace Formalism.DworkPowerSeriesWeights

section Norms

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem norm_natCast_eq_one_of_not_dvd {l m : ℕ} (hl : l.Prime) (hlt : ‖(l : K)‖ < 1)
    (hm : ¬ l ∣ m) : ‖(m : K)‖ = 1 := by
  first | exact GlobalTheory.NatCastUnitNorm.norm_natCast_eq_one_of_not_dvd .. | (apply GlobalTheory.NatCastUnitNorm.norm_natCast_eq_one_of_not_dvd <;> assumption) | (intros; apply GlobalTheory.NatCastUnitNorm.norm_natCast_eq_one_of_not_dvd <;> assumption) | (apply @GlobalTheory.NatCastUnitNorm.norm_natCast_eq_one_of_not_dvd <;> assumption) | (intros; apply @GlobalTheory.NatCastUnitNorm.norm_natCast_eq_one_of_not_dvd <;> assumption) | (apply @GlobalTheory.NatCastUnitNorm.norm_natCast_eq_one_of_not_dvd <;> first | assumption | infer_instance) | exact @GlobalTheory.NatCastUnitNorm.norm_natCast_eq_one_of_not_dvd K ‹_› ‹_› l m hl hlt hm | exact @GlobalTheory.NatCastUnitNorm.norm_natCast_eq_one_of_not_dvd K ‹_› ‹_› l m hl hlt | exact @GlobalTheory.NatCastUnitNorm.norm_natCast_eq_one_of_not_dvd K ‹_› ‹_› l m hl | exact @GlobalTheory.NatCastUnitNorm.norm_natCast_eq_one_of_not_dvd K ‹_› ‹_› l m | exact @GlobalTheory.NatCastUnitNorm.norm_natCast_eq_one_of_not_dvd K ‹_› ‹_› l | exact @GlobalTheory.NatCastUnitNorm.norm_natCast_eq_one_of_not_dvd K ‹_› ‹_› | exact @GlobalTheory.NatCastUnitNorm.norm_natCast_eq_one_of_not_dvd K ‹_› | exact @GlobalTheory.NatCastUnitNorm.norm_natCast_eq_one_of_not_dvd K

theorem norm_natCast_eq_pow_padicValNat {l n : ℕ} (hl : l.Prime) (hlt : ‖(l : K)‖ < 1)
    (hn : n ≠ 0) : ‖(n : K)‖ = ‖(l : K)‖ ^ padicValNat l n := by
  have hfac := Nat.ordProj_mul_ordCompl_eq_self n l
  have hnd := Nat.not_dvd_ordCompl hl hn
  rw [Nat.factorization_def n hl] at hfac hnd
  conv_lhs => rw [← hfac]
  rw [Nat.cast_mul, norm_mul, Nat.cast_pow, norm_pow, norm_natCast_eq_one_of_not_dvd hl hlt hnd,
    mul_one]

end Norms

theorem multiplicative_weight_le : MulWtLe.{u, v} := by
  intro K _ _ pi h0 ι r w1 w2 κ f g hf hg
  classical
  intro n hn
  rw [monoWtGe_iff, MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg h0.le _)
    fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have h1 : x.1 ≤ κ := le_trans (hx ▸ le_self_add) hn
  have h2 : x.2 ≤ κ := le_trans (hx ▸ le_add_self) hn
  rw [norm_mul, ← hx, dot_add]
  calc ‖MvPowerSeries.coeff x.1 f‖ * ‖MvPowerSeries.coeff x.2 g‖
      ≤ pi ^ (w1 - dot x.1 r) * pi ^ (w2 - dot x.2 r) :=
        mul_le_mul (hf x.1 h1) (hg x.2 h2) (norm_nonneg _) (Real.rpow_nonneg h0.le _)
    _ = pi ^ (w1 + w2 - (dot x.1 r + dot x.2 r)) := by
        rw [← Real.rpow_add h0]; congr 1; ring

theorem wtGeLe_pow {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type v} {pi : ℝ}
    (h0 : 0 < pi) {r : ι → ℝ} {wt : ℝ} {κ : ι →₀ ℕ} {f : MvPowerSeries ι K}
    (hf : WtGeLe pi r wt κ f) (k : ℕ) : WtGeLe pi r (k * wt) κ (f ^ k) := by
  induction k with
  | zero =>
    intro n _
    simpa using wtGe_one (K := K) h0 r n
  | succ k ih =>
    rw [pow_succ]
    have := multiplicative_weight_le K pi h0 ι r _ _ κ _ _ ih hf
    push_cast
    rwa [add_mul, one_mul]

theorem exponential_weight_le : ExpWtLe.{u, v} := by
  intro K _ _ _ l hl hlt ι r κ B hB0 hB
  classical
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hpi0 : 0 < ‖(l : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.ne_zero)
  have hs : PowerSeries.HasSubst B := PowerSeries.HasSubst.of_constantCoeff_zero hB0
  intro n hn
  rw [monoWtGe_iff]
  unfold mvExp
  rw [PowerSeries.coeff_subst hs]
  refine norm_finsum_le_of (Real.rpow_nonneg hpi0.le _) fun k => ?_
  rw [PowerSeries.coeff_exp, smul_eq_mul, norm_mul]
  have hk := wtGeLe_pow hpi0 hB k n hn
  rw [monoWtGe_iff] at hk
  have hfk : (k.factorial : ℕ) ≠ 0 := Nat.factorial_ne_zero k
  have hnorm : ‖(algebraMap ℚ K) (1 / (k.factorial : ℚ))‖ =
      ‖(l : K)‖ ^ (-(padicValNat l k.factorial : ℝ)) := by
    rw [map_div₀, map_one, map_natCast, norm_div, norm_one,
      norm_natCast_eq_pow_padicValNat hl hlt hfk, Real.rpow_neg hpi0.le, Real.rpow_natCast,
      one_div]
  rw [hnorm]

  have hv : (padicValNat l k.factorial : ℝ) ≤ (k : ℝ) * (1 / ((l : ℝ) - 1)) := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0; simp
    · have := (Formalism.IncomingBounds.padicValFactorialBounds l hl k hk0).2
      have hl0 : (0 : ℝ) < (l : ℝ) - 1 := by linarith
      calc (padicValNat l k.factorial : ℝ) ≤ ((k : ℝ) - 1) / ((l : ℝ) - 1) := this
        _ ≤ (k : ℝ) / ((l : ℝ) - 1) := by
          apply div_le_div_of_nonneg_right _ hl0.le; linarith
        _ = (k : ℝ) * (1 / ((l : ℝ) - 1)) := by ring
  calc ‖(l : K)‖ ^ (-(padicValNat l k.factorial : ℝ)) * ‖MvPowerSeries.coeff n (B ^ k)‖
      ≤ ‖(l : K)‖ ^ (-(padicValNat l k.factorial : ℝ)) *
          ‖(l : K)‖ ^ ((k : ℝ) * (1 / ((l : ℝ) - 1)) - dot n r) :=
        mul_le_mul_of_nonneg_left hk (Real.rpow_nonneg hpi0.le _)
    _ = ‖(l : K)‖ ^ (-(padicValNat l k.factorial : ℝ) +
          ((k : ℝ) * (1 / ((l : ℝ) - 1)) - dot n r)) := by rw [← Real.rpow_add hpi0]
    _ ≤ ‖(l : K)‖ ^ (0 - dot n r) :=
        Real.rpow_le_rpow_of_exponent_ge hpi0 hlt.le (by linarith)

theorem factorial_valuation_bound : FactVal.{u, v} := by
  intro K _ _ _ l hl hlt ι _ κ
  classical
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hl0 : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  have hpi0 : 0 < ‖(l : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.ne_zero)
  set L : ℝ := Real.logb l (κ.degree : ℝ) + 1 with hL
  have hL0 : 0 ≤ L := by
    rcases Nat.eq_zero_or_pos κ.degree with h | h
    · rw [hL, h]; simp
    · have : 0 ≤ Real.logb l (κ.degree : ℝ) :=
        Real.logb_nonneg hl1 (by exact_mod_cast h)
      linarith

  have hcoord : ∀ i ∈ κ.support, ‖(((κ i).factorial : ℕ) : K)‖ ≤
      ‖(l : K)‖ ^ ((κ i : ℝ) / ((l : ℝ) - 1) - L) := by
    intro i hi
    have hki : 1 ≤ κ i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    have hb := (Formalism.IncomingBounds.padicValFactorialBounds l hl (κ i) hki).1
    have hdeg : (κ i : ℝ) ≤ (κ.degree : ℝ) := by
      have : κ i ≤ κ.degree := by
        rw [Finsupp.degree_apply]
        exact Finset.single_le_sum (f := fun j => κ j) (fun j _ => Nat.zero_le _) hi
      exact_mod_cast this
    have hlog : Real.logb l (κ i : ℝ) ≤ Real.logb l (κ.degree : ℝ) :=
      Real.logb_le_logb_of_le hl1 (by exact_mod_cast hki) hdeg
    rw [norm_natCast_eq_pow_padicValNat hl hlt (Nat.factorial_ne_zero _), ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hpi0 hlt.le (by rw [hL]; linarith)
  have hmf : ((mfact κ : ℕ) : K) = ∏ i ∈ κ.support, (((κ i).factorial : ℕ) : K) := by
    rw [mfact, Finsupp.prod, Nat.cast_prod]
  rw [hmf, norm_prod]
  calc ∏ i ∈ κ.support, ‖(((κ i).factorial : ℕ) : K)‖
      ≤ ∏ i ∈ κ.support, ‖(l : K)‖ ^ ((κ i : ℝ) / ((l : ℝ) - 1) - L) :=
        Finset.prod_le_prod (fun i _ => norm_nonneg _) hcoord
    _ = ‖(l : K)‖ ^ (∑ i ∈ κ.support, ((κ i : ℝ) / ((l : ℝ) - 1) - L)) :=
        (Real.rpow_sum_of_pos hpi0 _ _).symm
    _ ≤ ‖(l : K)‖ ^ ((∑ i, (κ i : ℝ) / ((l : ℝ) - 1)) - (Fintype.card ι : ℝ) * L) := by
        apply Real.rpow_le_rpow_of_exponent_ge hpi0 hlt.le
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
        have hsum : ∑ i ∈ κ.support, (κ i : ℝ) / ((l : ℝ) - 1) =
            ∑ i, (κ i : ℝ) / ((l : ℝ) - 1) := by
          apply Finset.sum_subset (Finset.subset_univ _)
          intro i _ hi
          rw [Finsupp.notMem_support_iff.mp hi]; simp
        have hcard : (κ.support.card : ℝ) ≤ (Fintype.card ι : ℝ) := by
          exact_mod_cast Finset.card_le_univ _
        rw [hsum]
        nlinarith

end Formalism.DworkPowerSeriesWeights
