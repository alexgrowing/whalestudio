import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.CyclicPowerClassOfExpEquiv
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TopsChoicePartA
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TopsChoicePartB

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.FG.SolveVAux (Low low_zero low_mono low_add low_sub low_neg low_mul low_pow low_one_iff)

namespace DworkIntegrality

section Bd

variable {K ι : Type} [NormedField K] [IsUltrametricDist K]

def Bd (c : ℝ) (f : MvPowerSeries ι K) : Prop := ∀ n, ‖MvPowerSeries.coeff n f‖ ≤ c

theorem bd_add {c : ℝ} {f g : MvPowerSeries ι K} (hf : Bd c f) (hg : Bd c g) : Bd c (f + g) :=
  fun n => by
    rw [map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf n) (hg n))

theorem bd_neg {c : ℝ} {f : MvPowerSeries ι K} (hf : Bd c f) : Bd c (-f) := fun n => by
  rw [map_neg, norm_neg]; exact hf n

theorem bd_sub {c : ℝ} {f g : MvPowerSeries ι K} (hf : Bd c f) (hg : Bd c g) : Bd c (f - g) := by
  rw [sub_eq_add_neg]; exact bd_add hf (bd_neg hg)

theorem bd_mul {a b : ℝ} {f g : MvPowerSeries ι K} (ha : 0 ≤ a) (hb : 0 ≤ b) (hf : Bd a f)
    (hg : Bd b g) : Bd (a * b) (f * g) := fun n => by
  classical
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb) fun x _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hf _) (hg _) (norm_nonneg _) ha

theorem bd_C {c : ℝ} (hc : 0 ≤ c) {a : K} (ha : ‖a‖ ≤ c) :
    Bd c (MvPowerSeries.C a : MvPowerSeries ι K) := fun n => by
  classical
  rw [MvPowerSeries.coeff_C]
  split_ifs
  · exact ha
  · simpa using hc

theorem bd_one : Bd 1 (1 : MvPowerSeries ι K) := by
  have := bd_C (ι := ι) (K := K) zero_le_one (a := 1) (by simp)
  simpa using this

theorem bd_pow {a : ℝ} {f : MvPowerSeries ι K} (ha : 0 ≤ a) (hf : Bd a f) (k : ℕ) :
    Bd (a ^ k) (f ^ k) := by
  induction k with
  | zero => simpa using bd_one
  | succ k ih => rw [pow_succ, pow_succ]; exact bd_mul (pow_nonneg ha k) ha ih hf

theorem bd_sum {α : Type} {c : ℝ} (hc : 0 ≤ c) (s : Finset α) (F : α → MvPowerSeries ι K)
    (h : ∀ a ∈ s, Bd c (F a)) : Bd c (∑ a ∈ s, F a) := fun n => by
  rw [map_sum]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hc fun a ha => h a ha n

theorem bd_natCast (k : ℕ) : Bd 1 ((k : ℕ) : MvPowerSeries ι K) := by
  rw [← map_natCast (MvPowerSeries.C : K →+* MvPowerSeries ι K)]
  exact bd_C zero_le_one (IsUltrametricDist.norm_natCast_le_one K k)

theorem int_mul {f g : MvPowerSeries ι K} (hf : Bd 1 f) (hg : Bd 1 g) : Bd 1 (f * g) := by
  simpa using bd_mul zero_le_one zero_le_one hf hg

theorem int_pow {f : MvPowerSeries ι K} (hf : Bd 1 f) (k : ℕ) : Bd 1 (f ^ k) := by
  simpa using bd_pow zero_le_one hf k

theorem sm_mul {c : ℝ} (hc : 0 ≤ c) {f g : MvPowerSeries ι K} (hf : Bd c f) (hg : Bd 1 g) :
    Bd c (f * g) := by
  simpa using bd_mul hc zero_le_one hf hg

end Bd

section Trunc

variable {K ι : Type} [Field K] [Finite ι]

def truncD (d : ℕ) (f : MvPowerSeries ι K) : MvPowerSeries ι K :=
  ∑ m ∈ (Finsupp.finite_of_degree_lt (σ := ι) d).toFinset,
    MvPowerSeries.monomial m (MvPowerSeries.coeff m f)

theorem coeff_truncD (d : ℕ) (f : MvPowerSeries ι K) (n : ι →₀ ℕ) :
    MvPowerSeries.coeff n (truncD d f) = if n.degree < d then MvPowerSeries.coeff n f else 0 := by
  classical
  unfold truncD
  rw [map_sum]
  simp only [MvPowerSeries.coeff_monomial]
  rw [Finset.sum_ite_eq]
  simp

theorem low_sub_truncD (d : ℕ) (f : MvPowerSeries ι K) : Low d (f - truncD d f) := by
  intro n hn
  rw [map_sub, coeff_truncD, if_pos hn, sub_self]

theorem coeff_truncD_self {d : ℕ} (f : MvPowerSeries ι K) {n : ι →₀ ℕ} (hn : n.degree = d) :
    MvPowerSeries.coeff n (truncD d f) = 0 := by
  rw [coeff_truncD, if_neg (by omega)]

theorem constantCoeff_truncD {d : ℕ} (hd : 0 < d) (f : MvPowerSeries ι K) :
    MvPowerSeries.constantCoeff (truncD d f) = MvPowerSeries.constantCoeff f := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_truncD, if_pos (by simpa using hd),
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply]

omit [Finite ι] in
theorem coeff_eq_of_low {X Y : MvPowerSeries ι K} {d : ℕ} (h : Low (d + 1) (X - Y))
    {m : ι →₀ ℕ} (hm : m.degree = d) : MvPowerSeries.coeff m X = MvPowerSeries.coeff m Y := by
  have := h m (by omega)
  rwa [map_sub, sub_eq_zero] at this

end Trunc

section Induct

variable {K ι : Type} [NormedField K] [Finite ι]

theorem bd_induct {c : ℝ} (hc : 0 ≤ c) (X : MvPowerSeries ι K)
    (h : ∀ d, Bd c (truncD d X) → ∀ m : ι →₀ ℕ, m.degree = d → ‖MvPowerSeries.coeff m X‖ ≤ c) :
    Bd c X := by
  have key : ∀ d, ∀ m : ι →₀ ℕ, m.degree = d → ‖MvPowerSeries.coeff m X‖ ≤ c := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      refine h d ?_
      intro n
      rw [coeff_truncD]
      split_ifs with hn
      · exact ih _ hn n rfl
      · simpa using hc
  exact fun n => key _ n rfl

variable [IsUltrametricDist K]

theorem bd_of_mul {c : ℝ} (hc : 0 ≤ c) {X U : MvPowerSeries ι K} (hU : Bd 1 U)
    (hU1 : MvPowerSeries.constantCoeff U = 1) (h : Bd c (X * U)) : Bd c X := by
  refine bd_induct hc X fun d hl m hm => ?_
  have hXh := low_sub_truncD d X
  have hU' : Low 1 (U - 1) := (low_one_iff _).2 (by simp [hU1])
  have hlow : Low (d + 1) (X - (X * U - truncD d X * U + truncD d X)) := by
    have e : X - (X * U - truncD d X * U + truncD d X) = -((X - truncD d X) * (U - 1)) := by ring
    rw [e]
    exact low_neg (low_mul hXh hU')
  rw [coeff_eq_of_low hlow hm, map_add, coeff_truncD_self X hm, add_zero]
  exact bd_sub h (sm_mul hc hl hU) m

end Induct

section Frob

variable {K ι : Type} [Field K]

def PhiH {p : ℕ} (hp : p ≠ 0) (σ : K →+* K) : MvPowerSeries ι K →+* MvPowerSeries ι K :=
  ((MvPowerSeries.expand p hp : MvPowerSeries ι K →ₐ[K] MvPowerSeries ι K) :
    MvPowerSeries ι K →+* MvPowerSeries ι K).comp (MvPowerSeries.map σ)

theorem PhiH_apply {p : ℕ} (hp : p ≠ 0) (σ : K →+* K) (f : MvPowerSeries ι K) :
    PhiH hp σ f = frobVar p (MvPowerSeries.map σ f) := by
  rw [frobVar_eq_expand hp]
  rfl

theorem low_PhiH {p : ℕ} (hp : p ≠ 0) (σ : K →+* K) {d : ℕ} {h : MvPowerSeries ι K}
    (hh : Low d h) : Low (p * d) (PhiH hp σ h) := by
  intro n hn
  by_contra hne
  rw [PhiH_apply] at hne
  obtain ⟨m, rfl, hm⟩ := coeff_frobVar_ne_zero hp hne
  apply hm
  have hdeg : (p • m).degree = p * m.degree := by
    rw [map_nsmul, smul_eq_mul]
  rw [hdeg] at hn
  rw [MvPowerSeries.coeff_map, hh m (lt_of_mul_lt_mul_left hn (Nat.zero_le _)), map_zero]

end Frob

section Congr

variable {K ι : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ} {σ : K →+* K}

theorem frob_monomial (hp : p ≠ 0) (hσ : ∀ a : K, ‖a‖ ≤ 1 → ‖σ a - a ^ p‖ ≤ (p : ℝ)⁻¹)
    (a : ι →₀ ℕ) {c : K} (hc : ‖c‖ ≤ 1) :
    Bd (p : ℝ)⁻¹ ((MvPowerSeries.monomial a c) ^ p - PhiH hp σ (MvPowerSeries.monomial a c)) := by
  classical
  have e : (MvPowerSeries.monomial a c) ^ p - PhiH hp σ (MvPowerSeries.monomial a c) =
      MvPowerSeries.monomial (p • a) (c ^ p - σ c) := by
    rw [MvPowerSeries.monomial_pow, PhiH_apply, frobVar_eq_expand hp, MvPowerSeries.map_monomial,
      MvPowerSeries.expand_monomial, map_sub]
  rw [e]
  intro n
  rw [MvPowerSeries.coeff_monomial]
  split_ifs
  · rw [norm_sub_rev]; exact hσ c hc
  · simp

theorem frob_add (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) {x y : MvPowerSeries ι K}
    (hx : Bd 1 x) (hy : Bd 1 y) (hx' : Bd (p : ℝ)⁻¹ (x ^ p - PhiH hp.ne_zero σ x))
    (hy' : Bd (p : ℝ)⁻¹ (y ^ p - PhiH hp.ne_zero σ y)) :
    Bd (p : ℝ)⁻¹ ((x + y) ^ p - PhiH hp.ne_zero σ (x + y)) := by
  have hpos : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have e : (x + y) ^ p - PhiH hp.ne_zero σ (x + y) =
      (x ^ p - PhiH hp.ne_zero σ x) + (y ^ p - PhiH hp.ne_zero σ y) +
        MvPowerSeries.C (p : K) * (x * y *
          ∑ k ∈ Ioo 0 p, x ^ (k - 1) * y ^ (p - k - 1) * ((p.choose k / p : ℕ) : MvPowerSeries ι K)) := by
    rw [add_pow_prime_eq hp, map_add, map_natCast]
    ring
  rw [e]
  refine bd_add (bd_add hx' hy') (sm_mul hpos (bd_C hpos hnp.le) (int_mul (int_mul hx hy) ?_))
  exact bd_sum zero_le_one _ _ fun k _ =>
    int_mul (int_mul (int_pow hx _) (int_pow hy _)) (bd_natCast _)

theorem frob_finset (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹)
    (hσ : ∀ a : K, ‖a‖ ≤ 1 → ‖σ a - a ^ p‖ ≤ (p : ℝ)⁻¹) (c : (ι →₀ ℕ) → K) (hc : ∀ m, ‖c m‖ ≤ 1)
    (s : Finset (ι →₀ ℕ)) :
    Bd 1 (∑ m ∈ s, MvPowerSeries.monomial m (c m)) ∧
    Bd (p : ℝ)⁻¹ ((∑ m ∈ s, MvPowerSeries.monomial m (c m)) ^ p -
      PhiH hp.ne_zero σ (∑ m ∈ s, MvPowerSeries.monomial m (c m))) := by
  classical
  have hmon : ∀ a, Bd 1 (MvPowerSeries.monomial a (c a) : MvPowerSeries ι K) := by
    intro a n
    rw [MvPowerSeries.coeff_monomial]
    split_ifs
    · exact hc a
    · simp
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun n => by simp, fun n => ?_⟩
    simp [zero_pow hp.ne_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact ⟨bd_add (hmon a) ih.1,
      frob_add hp hnp (hmon a) ih.1 (frob_monomial hp.ne_zero hσ a (hc a)) ih.2⟩

theorem frob_congr [Finite ι] (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹)
    (hσ : ∀ a : K, ‖a‖ ≤ 1 → ‖σ a - a ^ p‖ ≤ (p : ℝ)⁻¹) {f : MvPowerSeries ι K} (hf : Bd 1 f) :
    Bd (p : ℝ)⁻¹ (f ^ p - PhiH hp.ne_zero σ f) := by
  intro n
  have hg : Bd (p : ℝ)⁻¹ ((truncD (n.degree + 1) f) ^ p -
      PhiH hp.ne_zero σ (truncD (n.degree + 1) f)) :=
    (frob_finset hp hnp hσ (fun m => MvPowerSeries.coeff m f) hf _).2
  have hl := low_sub_truncD (n.degree + 1) f
  have h1 : Low (n.degree + 1) (f ^ p - (truncD (n.degree + 1) f) ^ p) := by
    obtain ⟨r, hr⟩ := sub_dvd_pow_sub_pow f (truncD (n.degree + 1) f) p
    rw [hr]
    simpa using low_mul hl (low_zero r)
  have h2 : Low (n.degree + 1) (PhiH hp.ne_zero σ (f - truncD (n.degree + 1) f)) :=
    low_mono (Nat.le_mul_of_pos_left _ hp.pos) (low_PhiH hp.ne_zero σ hl)
  have e : f ^ p - PhiH hp.ne_zero σ f =
      ((truncD (n.degree + 1) f) ^ p - PhiH hp.ne_zero σ (truncD (n.degree + 1) f)) +
        (f ^ p - (truncD (n.degree + 1) f) ^ p) -
        PhiH hp.ne_zero σ (f - truncD (n.degree + 1) f) := by
    rw [map_sub]; ring
  rw [e, map_sub, map_add, h1 n (by omega), h2 n (by omega), add_zero, sub_zero]
  exact hg n

end Congr

section ExpS

variable {K ι : Type} [NormedField K] [CharZero K]

theorem constantCoeff_mvExp {f : MvPowerSeries ι K} (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (mvExp f) = 1 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_mvExp hf]
  simp

theorem low_exp_sub {f : MvPowerSeries ι K} {d : ℕ} (hd : 1 ≤ d) (hf : Low d f) :
    Low (d + 1) (mvExp f - 1 - f) := by
  have hf0 : MvPowerSeries.constantCoeff f = 0 := (low_one_iff _).1 (low_mono hd hf)
  have h1 := low_mvExp_sub hf0 (d + 1)
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have h2 : expSum f (e + 1 + 1) =
      (∑ k ∈ range e, MvPowerSeries.C (((k + 1 + 1).factorial : K)⁻¹) * f ^ (k + 1 + 1)) + f + 1 := by
    unfold expSum
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp
  have h3 : Low (e + 1 + 1)
      (∑ k ∈ range e, MvPowerSeries.C (((k + 1 + 1).factorial : K)⁻¹) * f ^ (k + 1 + 1)) :=
    low_sum _ _ _ fun k _ => by
      have := low_mul (low_zero (MvPowerSeries.C (((k + 1 + 1).factorial : K)⁻¹)))
        (low_mul (low_mul hf hf) (low_zero (f ^ k)))
      rw [show f ^ (k + 1 + 1) = f * f * f ^ k by ring]
      exact low_mono (by omega) this
  have e' : mvExp f - 1 - f = (mvExp f - expSum f (e + 1 + 1)) +
      ∑ k ∈ range e, MvPowerSeries.C (((k + 1 + 1).factorial : K)⁻¹) * f ^ (k + 1 + 1) := by
    rw [h2]; ring
  rw [e']
  exact low_add h1 h3

variable [IsUltrametricDist K] {p : ℕ}

theorem norm_fact_bound (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) (k : ℕ) :
    ‖(((k + 1).factorial : ℕ) : K)⁻¹‖ * ((p : ℝ)⁻¹) ^ (k + 1) ≤ (p : ℝ)⁻¹ := by
  have := Fact.mk hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlt : ‖(p : K)‖ < 1 := by rw [hnp]; exact inv_lt_one_of_one_lt₀ hp1
  have hv : padicValNat p (k + 1).factorial ≤ k := by
    have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero (p := p) (n := k + 1) (by omega)
    have h2 : 1 ≤ p - 1 := by have := hp.two_le; omega
    have h3 : 1 * padicValNat p (k + 1).factorial ≤ (p - 1) * padicValNat p (k + 1).factorial :=
      Nat.mul_le_mul_right _ h2
    omega
  rw [norm_inv, Formalism.DworkPowerSeriesWeights.norm_natCast_eq_pow_padicValNat hp hlt (Nat.factorial_ne_zero _), hnp]
  generalize padicValNat p (k + 1).factorial = v at hv
  obtain ⟨j, rfl⟩ : ∃ j, k = v + j := ⟨k - v, by omega⟩
  have hpos : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
  rw [add_assoc, pow_add, ← mul_assoc, inv_mul_cancel₀ (pow_pos hpos v).ne', one_mul, pow_succ]
  exact mul_le_of_le_one_left hpos.le (pow_le_one₀ hpos.le (inv_le_one_of_one_le₀ hp1.le))

theorem exp_small (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) {u : MvPowerSeries ι K}
    (hu0 : MvPowerSeries.constantCoeff u = 0) (hu : Bd (p : ℝ)⁻¹ u) :
    Bd (p : ℝ)⁻¹ (mvExp u - 1) := by
  have hpos : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  intro n
  rw [map_sub, coeff_mvExp hu0, Finset.sum_range_succ']
  have e0 : ((Nat.factorial 0 : ℕ) : K)⁻¹ * MvPowerSeries.coeff n (u ^ 0) =
      MvPowerSeries.coeff n (1 : MvPowerSeries ι K) := by simp
  rw [e0, add_sub_cancel_right]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hpos fun k _ => ?_
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (bd_pow hpos hu (k + 1) n) (norm_nonneg _)).trans
    (norm_fact_bound hp hnp k)

theorem small_of_exp [Finite ι] (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹)
    {D : MvPowerSeries ι K} (hD0 : MvPowerSeries.constantCoeff D = 0)
    (hD : Bd (p : ℝ)⁻¹ (mvExp D - 1)) : Bd (p : ℝ)⁻¹ D := by
  have hpos : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  refine bd_induct hpos D fun d hl m hm => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).1 hm
    rw [hm0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hD0]
    simp
  have hDh : Low d (D - truncD d D) := low_sub_truncD d D
  have hDl0 : MvPowerSeries.constantCoeff (truncD d D) = 0 := by
    rw [constantCoeff_truncD hd, hD0]
  have hDh0 : MvPowerSeries.constantCoeff (D - truncD d D) = 0 := by
    rw [map_sub, hD0, hDl0, sub_zero]
  have hEl := exp_small hp hnp hDl0 hl
  have hEl1 : Low 1 (mvExp (truncD d D) - 1) :=
    (low_one_iff _).2 (by rw [map_sub, constantCoeff_mvExp hDl0]; simp)
  have hEh := low_exp_sub hd hDh
  have hadd : mvExp D = mvExp (truncD d D) * mvExp (D - truncD d D) := by
    rw [← mvExp_add hDl0 hDh0]; congr 1; ring
  have hlow : Low (d + 1) (D - ((mvExp D - 1) - (mvExp (truncD d D) - 1) + truncD d D)) := by
    have e : D - ((mvExp D - 1) - (mvExp (truncD d D) - 1) + truncD d D) =
        -((mvExp (D - truncD d D) - 1 - (D - truncD d D)) * mvExp (truncD d D) +
          (mvExp (truncD d D) - 1) * (D - truncD d D)) := by
      rw [hadd]; ring
    rw [e]
    refine low_neg (low_add ?_ ?_)
    · simpa using low_mul hEh (low_zero (mvExp (truncD d D)))
    · have := low_mul hEl1 hDh
      rwa [add_comm] at this
  rw [coeff_eq_of_low hlow hm, map_add, coeff_truncD_self D hm, add_zero]
  exact bd_sub hD hEl m

end ExpS

section Mult

variable {K ι : Type} [NormedField K] [IsUltrametricDist K] [Finite ι] {p : ℕ} {σ : K →+* K}

theorem int_of_frob (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹)
    (hσ : ∀ a : K, ‖a‖ ≤ 1 → ‖σ a - a ^ p‖ ≤ (p : ℝ)⁻¹) {Fo Ga : MvPowerSeries ι K}
    (hF : MvPowerSeries.constantCoeff Fo = 1) (hG0 : MvPowerSeries.constantCoeff Ga = 1)
    (hG : Bd (p : ℝ)⁻¹ (Ga - 1)) (hrel : PhiH hp.ne_zero σ Fo = Fo ^ p * Ga) : Bd 1 Fo := by
  have hpos : (0 : ℝ) < (p : ℝ)⁻¹ := by have := hp.pos; positivity
  refine bd_induct zero_le_one Fo fun d hl m hm => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).1 hm
    rw [hm0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hF]
    simp
  have hFh : Low d (Fo - truncD d Fo) := low_sub_truncD d Fo
  have hFl1 : MvPowerSeries.constantCoeff (truncD d Fo) = 1 := by
    rw [constantCoeff_truncD hd, hF]
  have hFlm : MvPowerSeries.coeff m (truncD d Fo) = 0 := coeff_truncD_self Fo hm
  generalize truncD d Fo = Fl at hl hFh hFl1 hFlm
  obtain ⟨k, hk⟩ := Polynomial.powAddExpansion Fl (Fo - Fl) p
  rw [add_sub_cancel] at hk
  obtain ⟨r, hr⟩ := sub_dvd_pow_sub_pow Fo Fl p
  have hB := frob_congr hp hnp hσ hl
  have hY : Bd (p : ℝ)⁻¹ (-(Fl ^ p - PhiH hp.ne_zero σ Fl) - (Ga - 1) * Fl ^ p) :=
    bd_sub (bd_neg hB) (sm_mul hpos.le hG (int_pow hl p))
  have hG1 : Low 1 (Ga - 1) := (low_one_iff _).2 (by rw [map_sub, hG0]; simp)
  have hFp : Low 1 (Fl ^ (p - 1) - 1) := (low_one_iff _).2 (by rw [map_sub, map_pow, hFl1]; simp)
  have hlow : Low (d + 1) (MvPowerSeries.C (p : K) * Fo -
      (-(Fl ^ p - PhiH hp.ne_zero σ Fl) - (Ga - 1) * Fl ^ p + MvPowerSeries.C (p : K) * Fl)) := by
    have e : MvPowerSeries.C (p : K) * Fo -
        (-(Fl ^ p - PhiH hp.ne_zero σ Fl) - (Ga - 1) * Fl ^ p + MvPowerSeries.C (p : K) * Fl) =
        PhiH hp.ne_zero σ (Fo - Fl) - MvPowerSeries.C (p : K) * ((Fl ^ (p - 1) - 1) * (Fo - Fl)) -
          k * ((Fo - Fl) * (Fo - Fl)) - (Fo - Fl) * r * (Ga - 1) := by
      rw [map_sub, map_natCast]
      linear_combination -hrel - hk - (Ga - 1) * hr
    rw [e]
    have h2 := hp.two_le
    refine low_sub (low_sub (low_sub ?_ ?_) ?_) ?_
    · exact low_mono (by nlinarith) (low_PhiH hp.ne_zero σ hFh)
    · exact low_mono (by omega) (low_mul (low_zero (MvPowerSeries.C (p : K))) (low_mul hFp hFh))
    · exact low_mono (by omega) (low_mul (low_zero k) (low_mul hFh hFh))
    · exact low_mono (by omega) (low_mul (low_mul hFh (low_zero r)) hG1)
  have h1 := coeff_eq_of_low hlow hm
  rw [map_add, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul, hFlm, mul_zero, add_zero] at h1
  have h2 := hY m
  rw [← h1, norm_mul, hnp] at h2
  exact le_of_mul_le_mul_left (by simpa using h2) hpos

end Mult

section Rel

variable {K ι : Type} [NormedField K] [CharZero K]

theorem mvExp_natMul {Ψ : MvPowerSeries ι K} (h0 : MvPowerSeries.constantCoeff Ψ = 0) (n : ℕ) :
    mvExp (MvPowerSeries.C ((n + 1 : ℕ) : K) * Ψ) = (mvExp Ψ) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : MvPowerSeries.C ((n + 1 + 1 : ℕ) : K) * Ψ =
        MvPowerSeries.C ((n + 1 : ℕ) : K) * Ψ + Ψ := by
      rw [Nat.cast_succ (n + 1), map_add, map_one]; ring
    rw [e, mvExp_add (by simp [h0]) h0, ih, pow_succ (mvExp Ψ) (n + 1)]

theorem PhiH_mvExp {p : ℕ} (hp : p ≠ 0) (σ : K →+* K) {Ψ : MvPowerSeries ι K}
    (h0 : MvPowerSeries.constantCoeff Ψ = 0) :
    PhiH hp σ (mvExp Ψ) = mvExp (PhiH hp σ Ψ) := by
  have h1 : MvPowerSeries.map σ (mvExp Ψ) = mvExp (MvPowerSeries.map σ Ψ) := by
    unfold mvExp
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero h0), PowerSeries.map_exp]
  have h0' : MvPowerSeries.constantCoeff (MvPowerSeries.map σ Ψ) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, h0, map_zero]
  rw [PhiH_apply, PhiH_apply, h1]
  unfold frobVar mvExp
  rw [PowerSeries.subst_def, PowerSeries.subst_def,
    MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero h0').const
      (MvPowerSeries.HasSubst.X_pow hp)]

end Rel

end DworkIntegrality

open DworkIntegrality in

theorem dwork_multivariable : DworkMv := by
  intro K ι _ _ _ _ p σ hp hnp hσ Ψ h0
  have hpos : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  rw [← PhiH_apply hp.ne_zero]
  have hΦ0 : MvPowerSeries.constantCoeff (PhiH hp.ne_zero σ Ψ) = 0 := by
    rw [PhiH_apply, frobVar_eq_expand hp.ne_zero, MvPowerSeries.constantCoeff_expand,
      MvPowerSeries.constantCoeff_map, h0, map_zero]
  have hpΨ0 : MvPowerSeries.constantCoeff (MvPowerSeries.C (p : K) * Ψ) = 0 := by simp [h0]
  have hDe0 : MvPowerSeries.constantCoeff (PhiH hp.ne_zero σ Ψ - MvPowerSeries.C (p : K) * Ψ) = 0 := by
    rw [map_sub, hΦ0, hpΨ0, sub_zero]
  have hpow : mvExp (MvPowerSeries.C (p : K) * Ψ) = (mvExp Ψ) ^ p := by
    obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := hp.pos; omega⟩
    exact mvExp_natMul h0 n
  have hid : PhiH hp.ne_zero σ (mvExp Ψ) =
      (mvExp Ψ) ^ p * mvExp (PhiH hp.ne_zero σ Ψ - MvPowerSeries.C (p : K) * Ψ) := by
    rw [PhiH_mvExp hp.ne_zero σ h0, ← hpow, ← mvExp_add hpΨ0 hDe0]
    congr 1
    ring
  have hF1 := constantCoeff_mvExp h0
  have hG1 := constantCoeff_mvExp hDe0
  constructor
  · intro hint
    have hB := frob_congr hp hnp hσ (f := mvExp Ψ) hint
    refine small_of_exp hp hnp hDe0 (bd_of_mul hpos (U := (mvExp Ψ) ^ p) (int_pow hint p)
      (by rw [map_pow, hF1, one_pow]) ?_)
    have e : (mvExp (PhiH hp.ne_zero σ Ψ - MvPowerSeries.C (p : K) * Ψ) - 1) * (mvExp Ψ) ^ p =
        -((mvExp Ψ) ^ p - PhiH hp.ne_zero σ (mvExp Ψ)) := by
      rw [hid]; ring
    rw [e]
    exact bd_neg hB
  · intro hsm
    exact int_of_frob hp hnp hσ hF1 hG1 (exp_small hp hnp hDe0 hsm) hid

end Formalism.InvariantFactorPaths.G7
