import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.CyclicPowerClassOfExpEquiv
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TopsChoicePartB
import Lemmata.GeneralBFactRightExtra.Imports

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp low_subst_of_low norm_finsum_le_of)
open Formalism.FG.SolveVAux (Low low_pow low_one_iff)
open Formalism.FG.IntegralSubstitution (integral_mul integral_pow integral_one integralSubstV)

namespace TwoS

section Cong

variable {K ι : Type} [NormedField K] [IsUltrametricDist K]

def Cg (p : ℕ) (f g : MvPowerSeries ι K) : Prop :=
  ∀ n, ‖MvPowerSeries.coeff n (f - g)‖ ≤ (p : ℝ)⁻¹

theorem pinv_nonneg (p : ℕ) : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity

theorem pinv_le_one (p : ℕ) : (p : ℝ)⁻¹ ≤ 1 := Nat.cast_inv_le_one p

theorem integral_add {f g : MvPowerSeries ι K} (hf : Integral f) (hg : Integral g) :
    Integral (f + g) := fun n => by
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf n) (hg n))

theorem integral_neg {f : MvPowerSeries ι K} (hf : Integral f) : Integral (-f) := fun n => by
  rw [map_neg, norm_neg]; exact hf n

theorem integral_sub {f g : MvPowerSeries ι K} (hf : Integral f) (hg : Integral g) :
    Integral (f - g) := by
  rw [sub_eq_add_neg]; exact integral_add hf (integral_neg hg)

theorem integral_sum {α : Type} (s : Finset α) (F : α → MvPowerSeries ι K)
    (h : ∀ a ∈ s, Integral (F a)) : Integral (∑ a ∈ s, F a) := fun n => by
  rw [map_sum]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun a ha => h a ha n

theorem integral_C {a : K} (ha : ‖a‖ ≤ 1) : Integral (MvPowerSeries.C a : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_C]
  split_ifs
  · exact ha
  · simp

theorem integral_X (x : ι) : Integral (MvPowerSeries.X x : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

theorem integral_zero : Integral (0 : MvPowerSeries ι K) := fun n => by simp

theorem integral_natCast (k : ℕ) : Integral ((k : ℕ) : MvPowerSeries ι K) := by
  rw [← map_natCast (MvPowerSeries.C : K →+* MvPowerSeries ι K)]
  exact integral_C (IsUltrametricDist.norm_natCast_le_one K k)

theorem small_mul {c : ℝ} (hc : 0 ≤ c) {a h : MvPowerSeries ι K} (ha : Integral a)
    (hh : ∀ n, ‖MvPowerSeries.coeff n h‖ ≤ c) (n : ι →₀ ℕ) :
    ‖MvPowerSeries.coeff n (a * h)‖ ≤ c := by
  classical
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hc fun x _ => ?_
  rw [norm_mul]
  calc ‖MvPowerSeries.coeff x.1 a‖ * ‖MvPowerSeries.coeff x.2 h‖ ≤ 1 * c :=
        mul_le_mul (ha _) (hh _) (norm_nonneg _) zero_le_one
    _ = c := one_mul c

theorem cg_refl (p : ℕ) (f : MvPowerSeries ι K) : Cg p f f := fun n => by
  rw [sub_self, map_zero, norm_zero]; exact pinv_nonneg p

theorem cg_of_eq {p : ℕ} {f g : MvPowerSeries ι K} (h : f = g) : Cg p f g := h ▸ cg_refl p f

theorem cg_symm {p : ℕ} {f g : MvPowerSeries ι K} (h : Cg p f g) : Cg p g f := fun n => by
  rw [← neg_sub, map_neg, norm_neg]; exact h n

theorem cg_trans {p : ℕ} {f g k : MvPowerSeries ι K} (h1 : Cg p f g) (h2 : Cg p g k) :
    Cg p f k := fun n => by
  rw [← sub_add_sub_cancel f g k, map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h1 n) (h2 n))

theorem cg_add {p : ℕ} {f g f' g' : MvPowerSeries ι K} (h1 : Cg p f g) (h2 : Cg p f' g') :
    Cg p (f + f') (g + g') := fun n => by
  rw [add_sub_add_comm, map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h1 n) (h2 n))

theorem cg_sub {p : ℕ} {f g f' g' : MvPowerSeries ι K} (h1 : Cg p f g) (h2 : Cg p f' g') :
    Cg p (f - f') (g - g') := fun n => by
  rw [sub_sub_sub_comm, map_sub, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h1 n) ?_)
  rw [norm_neg]; exact h2 n

theorem cg_sum {p : ℕ} {α : Type} (s : Finset α) (F G : α → MvPowerSeries ι K)
    (h : ∀ a ∈ s, Cg p (F a) (G a)) : Cg p (∑ a ∈ s, F a) (∑ a ∈ s, G a) := fun n => by
  rw [← Finset.sum_sub_distrib, map_sum]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pinv_nonneg p) fun a ha => h a ha n

theorem integral_of_cg {p : ℕ} {f g : MvPowerSeries ι K} (h : Cg p f g) (hg : Integral g) :
    Integral f := fun n => by
  have e : f = (f - g) + g := by ring
  rw [e, map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le ((h n).trans (pinv_le_one p)) (hg n))

theorem cg_mul {p : ℕ} {f g f' g' : MvPowerSeries ι K} (hf : Integral f) (hg' : Integral g')
    (h1 : Cg p f g) (h2 : Cg p f' g') : Cg p (f * f') (g * g') := fun n => by
  have e : f * f' - g * g' = f * (f' - g') + g' * (f - g) := by ring
  rw [e, map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le (small_mul (pinv_nonneg p) hf h2 n) (small_mul (pinv_nonneg p) hg' h1 n))

theorem cg_pow {p : ℕ} {f g : MvPowerSeries ι K} (hf : Integral f) (hg : Integral g)
    (h : Cg p f g) (k : ℕ) : Cg p (f ^ k) (g ^ k) := by
  induction k with
  | zero => simpa using cg_refl p (1 : MvPowerSeries ι K)
  | succ k ih => rw [pow_succ, pow_succ]; exact cg_mul (integral_pow hf k) hg ih h

theorem cg_C {p : ℕ} {a b : K} (h : ‖a - b‖ ≤ (p : ℝ)⁻¹) :
    Cg p (MvPowerSeries.C a : MvPowerSeries ι K) (MvPowerSeries.C b) := by
  classical
  intro n
  rw [← map_sub, MvPowerSeries.coeff_C]
  split_ifs
  · exact h
  · rw [norm_zero]; exact pinv_nonneg p

theorem cg_frob_add {p : ℕ} (hp : p.Prime) (hn : ‖(p : K)‖ = (p : ℝ)⁻¹) {f g : MvPowerSeries ι K}
    (hf : Integral f) (hg : Integral g) : Cg p ((f + g) ^ p) (f ^ p + g ^ p) := by
  intro n
  rw [add_pow_prime_eq hp, add_sub_cancel_left, mul_assoc, mul_assoc,
    ← map_natCast (MvPowerSeries.C : K →+* MvPowerSeries ι K) p, MvPowerSeries.coeff_C_mul,
    norm_mul, hn]
  refine mul_le_of_le_one_right (pinv_nonneg p) ?_
  refine integral_mul hf (integral_mul hg (integral_sum _ _ fun k _ => ?_)) n
  exact integral_mul (integral_mul (integral_pow hf _) (integral_pow hg _)) (integral_natCast _)

theorem cg_frob_sum {p : ℕ} (hp : p.Prime) (hn : ‖(p : K)‖ = (p : ℝ)⁻¹) {α : Type} (s : Finset α)
    (F : α → MvPowerSeries ι K) (h : ∀ a ∈ s, Integral (F a)) :
    Cg p ((∑ a ∈ s, F a) ^ p) (∑ a ∈ s, F a ^ p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [zero_pow hp.ne_zero] using cg_refl p (0 : MvPowerSeries ι K)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hs : ∀ b ∈ s, Integral (F b) := fun b hb => h b (Finset.mem_insert_of_mem hb)
    exact cg_trans (cg_frob_add hp hn (h a (Finset.mem_insert_self a s)) (integral_sum _ _ hs))
      (cg_add (cg_refl p _) (ih hs))

theorem cg_frob2_sum {p : ℕ} (hp : p.Prime) (hn : ‖(p : K)‖ = (p : ℝ)⁻¹) {α : Type} (s : Finset α)
    (F : α → MvPowerSeries ι K) (h : ∀ a ∈ s, Integral (F a)) :
    Cg p ((∑ a ∈ s, F a) ^ (p ^ 2)) (∑ a ∈ s, F a ^ (p ^ 2)) := by
  have h1 := cg_frob_sum hp hn s F h
  have h2 := cg_frob_sum hp hn s (fun a => F a ^ p) fun a ha => integral_pow (h a ha) p
  have h3 := cg_pow (integral_pow (integral_sum _ _ h) p)
    (integral_sum _ _ fun a ha => integral_pow (h a ha) p) h1 p
  simp only [← pow_mul, ← sq] at h2 h3
  exact cg_trans h3 h2

theorem norm_pow_sub_pow {p : ℕ} {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (h : ‖a - b‖ ≤ (p : ℝ)⁻¹) (k : ℕ) : ‖a ^ k - b ^ k‖ ≤ (p : ℝ)⁻¹ := by
  first | exact Bl.general_b_fact_right'''.goal1 .. | (apply Bl.general_b_fact_right'''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right'''.goal1 <;> assumption) | (apply @Bl.general_b_fact_right'''.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_right'''.goal1 <;> assumption) | (apply @Bl.general_b_fact_right'''.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_right'''.goal1 K ‹_› ‹_› p a b ha hb h k | exact @Bl.general_b_fact_right'''.goal1 K ‹_› ‹_› p a b ha hb h | exact @Bl.general_b_fact_right'''.goal1 K ‹_› ‹_› p a b ha hb | exact @Bl.general_b_fact_right'''.goal1 K ‹_› ‹_› p a b ha | exact @Bl.general_b_fact_right'''.goal1 K ‹_› ‹_› p a b | exact @Bl.general_b_fact_right'''.goal1 K ‹_› ‹_› p a | exact @Bl.general_b_fact_right'''.goal1 K ‹_› ‹_› p | exact @Bl.general_b_fact_right'''.goal1 K ‹_› ‹_› | exact @Bl.general_b_fact_right'''.goal1 K ‹_› | exact @Bl.general_b_fact_right'''.goal1 K

end Cong

section Alt

variable {K : Type} [Field K]

theorem coeff_altF_pow {p : ℕ} (hp : 2 ≤ p) (l : ℕ) :
    PowerSeries.coeff ((p ^ 2) ^ l) (altF K p) = (-1) ^ l := by
  rw [altF, PowerSeries.coeff_mk, Finset.sum_eq_single l]
  · simp
  · intro j _ hj
    rw [if_neg]
    intro h
    exact hj (powq_inj hp h).symm
  · intro h
    exact absurd (mem_range.2 (lt_powq hp l)) h

theorem coeff_altF_ne_zero {p d : ℕ} (h : PowerSeries.coeff d (altF K p) ≠ 0) :
    ∃ l, d = (p ^ 2) ^ l := by
  rw [altF, PowerSeries.coeff_mk] at h
  obtain ⟨l, _, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  by_cases e : d = (p ^ 2) ^ l
  · exact ⟨l, e⟩
  · rw [if_neg e] at hl; exact absurd rfl hl

theorem coeff_subst_altF {ι : Type} {p : ℕ} (hp : 2 ≤ p) {L : MvPowerSeries ι K}
    (hL : MvPowerSeries.constantCoeff L = 0) (n : ι →₀ ℕ) :
    MvPowerSeries.coeff n (PowerSeries.subst L (altF K p)) =
      ∑ l ∈ range (n.degree + 1), (-1) ^ l * MvPowerSeries.coeff n (L ^ ((p ^ 2) ^ l)) := by
  classical
  have hs : PowerSeries.HasSubst L := PowerSeries.HasSubst.of_constantCoeff_zero hL
  rw [PowerSeries.coeff_subst hs,
    finsum_eq_sum_of_support_subset (s := (range (n.degree + 1)).image fun l => (p ^ 2) ^ l)]
  · rw [Finset.sum_image fun a _ b _ h => powq_inj hp h]
    exact Finset.sum_congr rfl fun l _ => by rw [coeff_altF_pow hp, smul_eq_mul]
  · intro d hd
    simp only [Function.mem_support] at hd
    have h1 : PowerSeries.coeff d (altF K p) ≠ 0 := fun h => hd (by rw [h, zero_smul])
    have h2 : MvPowerSeries.coeff n (L ^ d) ≠ 0 := fun h => hd (by rw [h, smul_zero])
    obtain ⟨l, rfl⟩ := coeff_altF_ne_zero h1
    have h3 : (p ^ 2) ^ l ≤ n.degree := by
      by_contra hlt
      exact h2 (low_pow ((low_one_iff _).2 hL) _ n (by omega))
    simp only [Finset.coe_image, Set.mem_image, Finset.coe_range, Set.mem_Iio]
    exact ⟨l, by have := lt_powq hp l; omega, rfl⟩

variable {ν r0 r1 : ℕ}

theorem coeff_sPos (p : ℕ) (s : ZMod (2 * ν)) (ab : Fin r0 × Fin r1) (n : ZV ν r0 r1 →₀ ℕ) :
    MvPowerSeries.coeff n (sPos (K := K) p s ab) = ∑ l ∈ range (n.degree + 1),
      if n = Finsupp.single (s - 2 * (l : ZMod (2 * ν)), ab) ((p ^ 2) ^ l) then (-1 : K) ^ l
      else 0 := rfl

theorem constantCoeff_sPos {p : ℕ} (hp : p ≠ 0) (s : ZMod (2 * ν)) (ab : Fin r0 × Fin r1) :
    MvPowerSeries.constantCoeff (sPos (K := K) p s ab) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_sPos]
  refine Finset.sum_eq_zero fun l _ => if_neg fun h => ?_
  have := Finsupp.single_eq_zero.1 h.symm
  exact (pow_ne_zero l (pow_ne_zero 2 hp)) this

def linW [NeZero ν] (w : ZMod (2 * ν) → K) (ab : Fin r0 × Fin r1) : MvPowerSeries (ZV ν r0 r1) K :=
  ∑ s : ZMod (2 * ν), MvPowerSeries.C (w s) * MvPowerSeries.X (s, ab)

def posW [NeZero ν] (p : ℕ) (w : ZMod (2 * ν) → K) (ab : Fin r0 × Fin r1) :
    MvPowerSeries (ZV ν r0 r1) K :=
  ∑ s : ZMod (2 * ν), MvPowerSeries.C (w s) * sPos p s ab

theorem constantCoeff_linW [NeZero ν] (w : ZMod (2 * ν) → K) (ab : Fin r0 × Fin r1) :
    MvPowerSeries.constantCoeff (linW w ab) = 0 := by
  simp [linW, map_sum]

theorem coeff_posW [NeZero ν] (p : ℕ) (w : ZMod (2 * ν) → K) (ab : Fin r0 × Fin r1)
    (n : ZV ν r0 r1 →₀ ℕ) :
    MvPowerSeries.coeff n (posW p w ab) = ∑ l ∈ range (n.degree + 1), (-1) ^ l *
      MvPowerSeries.coeff n (∑ s : ZMod (2 * ν), MvPowerSeries.C (w (s + 2 * (l : ZMod (2 * ν)))) *
        (MvPowerSeries.X (s, ab) : MvPowerSeries (ZV ν r0 r1) K) ^ ((p ^ 2) ^ l)) := by
  simp only [posW, map_sum, MvPowerSeries.coeff_C_mul, coeff_sPos, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Equiv.sum_comp (Equiv.addRight (2 * (l : ZMod (2 * ν))))]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Equiv.coe_addRight, add_sub_cancel_right, MvPowerSeries.coeff_X_pow]
  split_ifs <;> ring

end Alt

section AltN

variable {K : Type} [NormedField K] [IsUltrametricDist K] {ν r0 r1 : ℕ}

theorem integral_sPos (p : ℕ) (s : ZMod (2 * ν)) (ab : Fin r0 × Fin r1) :
    Integral (sPos (K := K) p s ab) := fun n => by
  rw [coeff_sPos]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun l _ => ?_
  split_ifs <;> simp

theorem integral_linW [NeZero ν] {w : ZMod (2 * ν) → K} (hw : ∀ s, ‖w s‖ ≤ 1)
    (ab : Fin r0 × Fin r1) : Integral (linW w ab) :=
  integral_sum _ _ fun s _ => integral_mul (integral_C (hw s)) (integral_X _)

theorem integral_posW [NeZero ν] (p : ℕ) {w : ZMod (2 * ν) → K} (hw : ∀ s, ‖w s‖ ≤ 1)
    (ab : Fin r0 × Fin r1) : Integral (posW p w ab) :=
  integral_sum _ _ fun s _ => integral_mul (integral_C (hw s)) (integral_sPos p s ab)

theorem cg_lin_pow [NeZero ν] {p : ℕ} (hp : p.Prime) (hn : ‖(p : K)‖ = (p : ℝ)⁻¹)
    {w : ZMod (2 * ν) → K} (hw1 : ∀ s, ‖w s‖ ≤ 1)
    (hw2 : ∀ s, ‖w (s + 2) - w s ^ (p ^ 2)‖ ≤ (p : ℝ)⁻¹) (ab : Fin r0 × Fin r1) (l : ℕ) :
    Cg p (linW w ab ^ ((p ^ 2) ^ l))
      (∑ s : ZMod (2 * ν), MvPowerSeries.C (w (s + 2 * (l : ZMod (2 * ν)))) *
        (MvPowerSeries.X (s, ab) : MvPowerSeries (ZV ν r0 r1) K) ^ ((p ^ 2) ^ l)) := by
  induction l with
  | zero => simpa [linW] using cg_refl p _
  | succ l ih =>
    have hI : ∀ s ∈ (Finset.univ : Finset (ZMod (2 * ν))),
        Integral (MvPowerSeries.C (w (s + 2 * (l : ZMod (2 * ν)))) *
          (MvPowerSeries.X (s, ab) : MvPowerSeries (ZV ν r0 r1) K) ^ ((p ^ 2) ^ l)) := fun s _ =>
      integral_mul (integral_C (hw1 _)) (integral_pow (integral_X _) _)
    rw [pow_succ, pow_mul]
    refine cg_trans (cg_pow (integral_pow (integral_linW hw1 ab) _) (integral_sum _ _ hI) ih
      (p ^ 2)) ?_
    refine cg_trans (cg_frob2_sum hp hn _ _ hI) ?_
    refine cg_sum _ _ _ fun s _ => ?_
    rw [mul_pow, ← pow_mul, ← map_pow]
    refine cg_mul (integral_C ?_) (integral_pow (integral_X _) _) (cg_C ?_) (cg_refl _ _)
    · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hw1 _)
    · have := hw2 (s + 2 * (l : ZMod (2 * ν)))
      have e : s + 2 * ((l + 1 : ℕ) : ZMod (2 * ν)) = s + 2 * (l : ZMod (2 * ν)) + 2 := by
        push_cast; ring
      rw [norm_sub_rev, e]
      exact this

theorem cg_altF_lin [NeZero ν] {p : ℕ} (hp : p.Prime) (hn : ‖(p : K)‖ = (p : ℝ)⁻¹)
    {w : ZMod (2 * ν) → K} (hw1 : ∀ s, ‖w s‖ ≤ 1)
    (hw2 : ∀ s, ‖w (s + 2) - w s ^ (p ^ 2)‖ ≤ (p : ℝ)⁻¹) (ab : Fin r0 × Fin r1) :
    Cg p (PowerSeries.subst (linW w ab) (altF K p)) (posW p w ab) := by
  intro n
  rw [map_sub, coeff_subst_altF hp.two_le (constantCoeff_linW w ab), coeff_posW,
    ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pinv_nonneg p) fun l _ => ?_
  rw [← mul_sub, ← map_sub, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact cg_lin_pow hp hn hw1 hw2 ab l n

theorem cg_subst_of_small {ι : Type} {p : ℕ} {L : MvPowerSeries ι K}
    (hL0 : MvPowerSeries.constantCoeff L = 0) (hL : Integral L) {μ μ' : PowerSeries K}
    (h : ∀ n, ‖PowerSeries.coeff n (μ - μ')‖ ≤ (p : ℝ)⁻¹) :
    Cg p (PowerSeries.subst L μ) (PowerSeries.subst L μ') := by
  intro n
  have hs : PowerSeries.HasSubst L := PowerSeries.HasSubst.of_constantCoeff_zero hL0
  rw [← PowerSeries.subst_sub hs, PowerSeries.coeff_subst hs]
  refine norm_finsum_le_of (pinv_nonneg p) fun d => ?_
  rw [smul_eq_mul, norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (integral_pow hL d n)).trans (h d)

end AltN

section Par

variable {ν : ℕ}

theorem val_add_one_mod_two [NeZero ν] (s : ZMod (2 * ν)) : (s + 1).val % 2 = (s.val + 1) % 2 := by
  have hν : 0 < ν := Nat.pos_of_ne_zero (NeZero.ne ν)
  rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.mod_mod_of_dvd _ (Dvd.intro _ rfl),
    Nat.mod_eq_of_lt (show 1 < 2 * ν by omega)]

theorem val_add_two_mod_two [NeZero ν] (s : ZMod (2 * ν)) : (s + 2).val % 2 = s.val % 2 := by
  have e : s + 2 = s + 1 + 1 := by ring
  have h1 := val_add_one_mod_two s
  rw [e, val_add_one_mod_two]
  omega

variable {K : Type}

def wE [Zero K] (u : ZMod (2 * ν) → K) (k : ℕ) (s : ZMod (2 * ν)) : K :=
  if s.val % 2 = k then u s else 0

def wE' [Zero K] (u : ZMod (2 * ν) → K) (k : ℕ) (s : ZMod (2 * ν)) : K :=
  if s.val % 2 = k then u (s + 1) else 0

variable [NormedField K] [IsUltrametricDist K]

theorem norm_wE {u : ZMod (2 * ν) → K} (hu : ∀ s, ‖u s‖ ≤ 1) (k : ℕ) (s : ZMod (2 * ν)) :
    ‖wE u k s‖ ≤ 1 := by
  unfold wE
  split_ifs
  · exact hu s
  · simp

theorem norm_wE' {u : ZMod (2 * ν) → K} (hu : ∀ s, ‖u s‖ ≤ 1) (k : ℕ) (s : ZMod (2 * ν)) :
    ‖wE' u k s‖ ≤ 1 := by
  unfold wE'
  split_ifs
  · exact hu _
  · simp

theorem wE_step2 [NeZero ν] {p : ℕ} (hp : p ≠ 0) {u : ZMod (2 * ν) → K} (hu : ∀ s, ‖u s‖ ≤ 1)
    (hu2 : ∀ s, ‖u (s + 1) - u s ^ p‖ ≤ (p : ℝ)⁻¹) (k : ℕ) (s : ZMod (2 * ν)) :
    ‖wE u k (s + 2) - wE u k s ^ (p ^ 2)‖ ≤ (p : ℝ)⁻¹ := by
  unfold wE
  rw [val_add_two_mod_two]
  split_ifs
  · have e : s + 2 = s + 1 + 1 := by ring
    have e2 : u (s + 2) - u s ^ (p ^ 2) =
        (u (s + 1 + 1) - u (s + 1) ^ p) + (u (s + 1) ^ p - (u s ^ p) ^ p) := by
      rw [e, ← pow_mul, ← sq]; ring
    rw [e2]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hu2 _)
      (norm_pow_sub_pow (hu _) (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hu _))
        (hu2 s) p))
  · rw [zero_pow (pow_ne_zero 2 hp), sub_zero, norm_zero]; exact pinv_nonneg p

theorem wE'_step {p : ℕ} (hp : p ≠ 0) {u : ZMod (2 * ν) → K}
    (hu2 : ∀ s, ‖u (s + 1) - u s ^ p‖ ≤ (p : ℝ)⁻¹) (k : ℕ) (s : ZMod (2 * ν)) :
    ‖wE u k s ^ p - wE' u k s‖ ≤ (p : ℝ)⁻¹ := by
  unfold wE wE'
  split_ifs
  · rw [norm_sub_rev]; exact hu2 s
  · rw [zero_pow hp, sub_zero, norm_zero]; exact pinv_nonneg p

variable {r0 r1 : ℕ}

def posW' [NeZero ν] (p : ℕ) (w : ZMod (2 * ν) → K) (ab : Fin r0 × Fin r1) :
    MvPowerSeries (ZV ν r0 r1) K :=
  ∑ s : ZMod (2 * ν), MvPowerSeries.C (w s) * sPos p s ab ^ p

theorem integral_posW' [NeZero ν] (p : ℕ) {w : ZMod (2 * ν) → K} (hw : ∀ s, ‖w s‖ ≤ 1)
    (ab : Fin r0 × Fin r1) : Integral (posW' p w ab) :=
  integral_sum _ _ fun s _ =>
    integral_mul (integral_C (hw s)) (integral_pow (integral_sPos p s ab) p)

theorem cg_mu_lin [NeZero ν] {p : ℕ} (hp : p.Prime) (hn : ‖(p : K)‖ = (p : ℝ)⁻¹)
    {u : ZMod (2 * ν) → K} (hu : ∀ s, ‖u s‖ ≤ 1)
    (hu2 : ∀ s, ‖u (s + 1) - u s ^ p‖ ≤ (p : ℝ)⁻¹) (k : ℕ) (ab : Fin r0 × Fin r1)
    {μ : PowerSeries K} (hμ : ∀ n, ‖PowerSeries.coeff n (μ - altF K p)‖ ≤ (p : ℝ)⁻¹) :
    Cg p (PowerSeries.subst (linW (wE u k) ab) μ) (posW p (wE u k) ab) :=
  cg_trans (cg_subst_of_small (constantCoeff_linW _ _) (integral_linW (norm_wE hu k) ab) hμ)
    (cg_altF_lin hp hn (norm_wE hu k) (wE_step2 hp.ne_zero hu hu2 k) ab)

theorem cg_mu_lin_pow [NeZero ν] {p : ℕ} (hp : p.Prime) (hn : ‖(p : K)‖ = (p : ℝ)⁻¹)
    {u : ZMod (2 * ν) → K} (hu : ∀ s, ‖u s‖ ≤ 1)
    (hu2 : ∀ s, ‖u (s + 1) - u s ^ p‖ ≤ (p : ℝ)⁻¹) (k : ℕ) (ab : Fin r0 × Fin r1)
    {μ : PowerSeries K} (hμ : ∀ n, ‖PowerSeries.coeff n (μ - altF K p)‖ ≤ (p : ℝ)⁻¹) :
    Cg p (PowerSeries.subst (linW (wE u k) ab) μ ^ p) (posW' p (wE' u k) ab) := by
  have hA := cg_mu_lin hp hn hu hu2 k ab hμ
  have hI := integral_posW (r0 := r0) (r1 := r1) p (norm_wE hu k) ab
  refine cg_trans (cg_pow (integral_of_cg hA hI) hI hA p) ?_
  refine cg_trans (cg_frob_sum hp hn Finset.univ _ fun s _ =>
    integral_mul (integral_C (norm_wE hu k s)) (integral_sPos p s ab)) ?_
  refine cg_sum _ _ _ fun s _ => ?_
  rw [mul_pow, ← map_pow]
  refine cg_mul (integral_C ?_) (integral_pow (integral_sPos p s ab) p)
    (cg_C (wE'_step hp.ne_zero hu2 k s)) (cg_refl _ _)
  rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_wE hu k s)

end Par

theorem sum_dual {K ι : Type} [Field K] {ν r0 r1 : ℕ} [NeZero ν] (a b : Fin ν → ZMod (2 * ν) → K)
    (par : ZMod (2 * ν) → Prop) [DecidablePred par]
    (h : ∀ s s', ∑ r, a r s * b r s' = if par s' ∧ s = s' + 1 then 1 else 0)
    (P Q : ZMod (2 * ν) → Fin r0 × Fin r1 → MvPowerSeries ι K) :
    ∑ e : EV ν r0 r1, (∑ s, MvPowerSeries.C (a e.1 s) * P s e.2) *
        (∑ s', MvPowerSeries.C (b e.1 s') * Q s' e.2) =
      ∑ s', if par s' then ∑ ab, Q s' ab * P (s' + 1) ab else 0 := by
  classical
  have key : ∀ ab : Fin r0 × Fin r1,
      ∑ r, (∑ s, MvPowerSeries.C (a r s) * P s ab) * (∑ s', MvPowerSeries.C (b r s') * Q s' ab) =
        ∑ s', if par s' then Q s' ab * P (s' + 1) ab else 0 := by
    intro ab
    simp only [Finset.sum_mul_sum]
    rw [Finset.sum_comm, Finset.sum_congr rfl fun s _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun s' _ => ?_
    have e : ∀ s, ∑ r, MvPowerSeries.C (a r s) * P s ab * (MvPowerSeries.C (b r s') * Q s' ab) =
        if par s' ∧ s = s' + 1 then Q s' ab * P s ab else 0 := by
      intro s
      have : ∑ r, MvPowerSeries.C (a r s) * P s ab * (MvPowerSeries.C (b r s') * Q s' ab) =
          MvPowerSeries.C (∑ r, a r s * b r s') * (Q s' ab * P s ab) := by
        rw [map_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun r _ => by rw [map_mul]; ring
      rw [this, h]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl fun s _ => e s]
    by_cases hp : par s'
    · simp [hp]
    · simp [hp]
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_congr rfl fun ab _ => key ab,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun s' _ => ?_
  split_ifs <;> simp

section Sub

variable {K : Type} [NormedField K] [IsUltrametricDist K] {ν r0 r1 : ℕ} [NeZero ν]

theorem zLin_false (om oms : Fin ν → ZMod (2 * ν) → K) (e : EV ν r0 r1) :
    zLin om oms (false, e) = linW (wE (oms e.1) 0) e.2 := by
  unfold zLin linW wE
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : s.val % 2 = 0 <;> simp [h]

theorem zLin_true (om oms : Fin ν → ZMod (2 * ν) → K) (e : EV ν r0 r1) :
    zLin om oms (true, e) = linW (wE (om e.1) 1) e.2 := by
  unfold zLin linW wE
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : s.val % 2 = 1 <;> simp [h]

theorem constantCoeff_zLin (om oms : Fin ν → ZMod (2 * ν) → K) (x : Bool × EV ν r0 r1) :
    MvPowerSeries.constantCoeff (zLin om oms x) = 0 := by
  obtain ⟨b, e⟩ := x
  cases b
  · rw [zLin_false]; exact constantCoeff_linW _ _
  · rw [zLin_true]; exact constantCoeff_linW _ _

theorem constantCoeff_sSub (om oms : Fin ν → ZMod (2 * ν) → K) {μ : PowerSeries K}
    (hμ0 : PowerSeries.constantCoeff μ = 0) (x : Bool × EV ν r0 r1) :
    MvPowerSeries.constantCoeff (sSub om oms μ x) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_zLin om oms x) μ hμ0

theorem integral_sSub {p : ℕ} (hp : p.Prime) (hn : ‖(p : K)‖ = (p : ℝ)⁻¹)
    {om oms : Fin ν → ZMod (2 * ν) → K} (hO : OmOK p ν om oms) {μ : PowerSeries K}
    (hμ : ∀ n, ‖PowerSeries.coeff n (μ - altF K p)‖ ≤ (p : ℝ)⁻¹) (x : Bool × EV ν r0 r1) :
    Integral (sSub om oms μ x) := by
  obtain ⟨hO1, hO2, -⟩ := hO
  obtain ⟨b, e⟩ := x
  unfold sSub
  cases b
  · rw [zLin_false]
    exact integral_of_cg (cg_mu_lin hp hn (fun s => (hO1 e.1 s).2) (fun s => (hO2 e.1 s).2) 0 e.2 hμ)
      (integral_posW p (norm_wE (fun s => (hO1 e.1 s).2) 0) e.2)
  · rw [zLin_true]
    exact integral_of_cg (cg_mu_lin hp hn (fun s => (hO1 e.1 s).1) (fun s => (hO2 e.1 s).1) 1 e.2 hμ)
      (integral_posW p (norm_wE (fun s => (hO1 e.1 s).1) 1) e.2)

theorem constantCoeff_hhS {p : ℕ} (hp : p ≠ 0) (u : ZMod (2 * ν) → K) :
    MvPowerSeries.constantCoeff (hhS (r0 := r0) (r1 := r1) p u) = 0 := by
  simp [hhS, map_sum, constantCoeff_sPos hp]

theorem subst_hh_eq_sum {τ E : Type} [Fintype E] (p : ℕ) (c c' : K)
    {φ : Bool × E → MvPowerSeries τ K} (hs : MvPowerSeries.HasSubst φ) :
    MvPowerSeries.subst φ (hh1 (E := E) p c c') =
      ∑ e : E, (MvPowerSeries.C c * φ (false, e) * φ (true, e) ^ p -
        MvPowerSeries.C c' * φ (false, e) ^ p * φ (true, e)) := by
  have hC : ∀ r : K, MvPowerSeries.substAlgHom hs (MvPowerSeries.C r) = MvPowerSeries.C r :=
    fun r => (MvPowerSeries.substAlgHom hs).commutes r
  rw [hh1, ← MvPowerSeries.coe_substAlgHom hs]
  simp only [map_sum, map_sub, map_mul, map_pow, hC, MvPowerSeries.substAlgHom_X]

theorem hhS_eq {p : ℕ} {om oms : Fin ν → ZMod (2 * ν) → K}
    (hO3 : ∀ a b : ZMod (2 * ν), a.val % 2 = b.val % 2 →
      ∑ r, oms r a * om r b = if a = b then 1 else 0) (c c' : K) :
    hhS (r0 := r0) (r1 := r1) p (uS c c') =
      ∑ e : EV ν r0 r1,
        (MvPowerSeries.C c * posW p (wE (oms e.1) 0) e.2 * posW' p (wE' (om e.1) 1) e.2 -
          MvPowerSeries.C c' * posW' p (wE' (oms e.1) 0) e.2 * posW p (wE (om e.1) 1) e.2) := by
  have h1 : ∀ s s' : ZMod (2 * ν), ∑ r, wE (oms r) 0 s * wE' (om r) 1 s' =
      if s'.val % 2 = 1 ∧ s = s' + 1 then 1 else 0 := by
    intro s s'
    have hs' := val_add_one_mod_two s'
    unfold wE wE'
    by_cases a1 : s'.val % 2 = 1
    · by_cases a2 : s.val % 2 = 0
      · simp only [a1, a2, if_true, true_and]
        exact hO3 s (s' + 1) (by omega)
      · have : s ≠ s' + 1 := fun h => a2 (by rw [h]; omega)
        simp [a2, this]
    · simp [a1]
  have h2 : ∀ s s' : ZMod (2 * ν), ∑ r, wE (om r) 1 s * wE' (oms r) 0 s' =
      if s'.val % 2 = 0 ∧ s = s' + 1 then 1 else 0 := by
    intro s s'
    have hs' := val_add_one_mod_two s'
    unfold wE wE'
    by_cases a1 : s'.val % 2 = 0
    · by_cases a2 : s.val % 2 = 1
      · simp only [a1, a2, if_true, true_and]
        rw [Finset.sum_congr rfl fun r _ => mul_comm _ _, hO3 (s' + 1) s (by omega)]
        simp only [eq_comm]
      · have : s ≠ s' + 1 := fun h => a2 (by rw [h]; omega)
        simp [a2, this]
    · simp [a1]
  have d1 := sum_dual (r0 := r0) (r1 := r1) (fun r => wE (oms r) 0) (fun r => wE' (om r) 1)
    (fun s' => s'.val % 2 = 1) h1 (fun s ab => sPos (K := K) p s ab) (fun s ab => sPos p s ab ^ p)
  have d2 := sum_dual (r0 := r0) (r1 := r1) (fun r => wE (om r) 1) (fun r => wE' (oms r) 0)
    (fun s' => s'.val % 2 = 0) h2 (fun s ab => sPos (K := K) p s ab) (fun s ab => sPos p s ab ^ p)
  have e1 : ∑ e : EV ν r0 r1,
        (MvPowerSeries.C c * posW p (wE (oms e.1) 0) e.2 * posW' p (wE' (om e.1) 1) e.2 -
          MvPowerSeries.C c' * posW' p (wE' (oms e.1) 0) e.2 * posW p (wE (om e.1) 1) e.2) =
      MvPowerSeries.C c * (∑ e : EV ν r0 r1,
          posW p (wE (oms e.1) 0) e.2 * posW' p (wE' (om e.1) 1) e.2) -
        MvPowerSeries.C c' * (∑ e : EV ν r0 r1,
          posW p (wE (om e.1) 1) e.2 * posW' p (wE' (oms e.1) 0) e.2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun e _ => by ring
  rw [e1]
  unfold posW posW'
  rw [d1, d2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  unfold hhS uS
  refine Finset.sum_congr rfl fun s _ => ?_
  rcases Nat.mod_two_eq_zero_or_one s.val with h | h
  · simp [h]
  · simp [h]

theorem cg_two_sums {p : ℕ} (hp : p.Prime) (hn : ‖(p : K)‖ = (p : ℝ)⁻¹)
    {om oms : Fin ν → ZMod (2 * ν) → K} (hO : OmOK p ν om oms) {c c' : K} (hc : ‖c‖ ≤ 1)
    (hc' : ‖c'‖ ≤ 1) {μ : PowerSeries K} (hμ0 : PowerSeries.constantCoeff μ = 0)
    (hμ : ∀ n, ‖PowerSeries.coeff n (μ - altF K p)‖ ≤ (p : ℝ)⁻¹) :
    Cg p (MvPowerSeries.subst (sSub om oms μ) (hh1 (E := EV ν r0 r1) p c c'))
      (hhS p (uS c c')) := by
  have hs : MvPowerSeries.HasSubst (sSub (r0 := r0) (r1 := r1) om oms μ) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_sSub om oms hμ0)
  have hI := integral_sSub (r0 := r0) (r1 := r1) hp hn hO hμ
  obtain ⟨hO1, hO2, hO3⟩ := hO
  rw [subst_hh_eq_sum p c c' hs, hhS_eq hO3]
  refine cg_sum _ _ _ fun e _ => ?_
  have aF := cg_mu_lin hp hn (fun s => (hO1 e.1 s).2) (fun s => (hO2 e.1 s).2) 0 e.2 hμ
  have aT := cg_mu_lin hp hn (fun s => (hO1 e.1 s).1) (fun s => (hO2 e.1 s).1) 1 e.2 hμ
  have bF := cg_mu_lin_pow hp hn (fun s => (hO1 e.1 s).2) (fun s => (hO2 e.1 s).2) 0 e.2 hμ
  have bT := cg_mu_lin_pow hp hn (fun s => (hO1 e.1 s).1) (fun s => (hO2 e.1 s).1) 1 e.2 hμ
  rw [← zLin_false om oms e] at aF bF
  rw [← zLin_true om oms e] at aT bT
  have iF := hI (false, e)
  have iT := hI (true, e)
  refine cg_sub (cg_mul (integral_mul (integral_C hc) iF)
      (integral_posW' p (norm_wE' (fun s => (hO1 e.1 s).1) 1) e.2)
      (cg_mul (integral_C hc) (integral_posW p (norm_wE (fun s => (hO1 e.1 s).2) 0) e.2)
        (cg_refl p _) aF) bT)
    (cg_mul (integral_mul (integral_C hc') (integral_pow iF p))
      (integral_posW p (norm_wE (fun s => (hO1 e.1 s).1) 1) e.2)
      (cg_mul (integral_C hc') (integral_posW' p (norm_wE' (fun s => (hO1 e.1 s).2) 0) e.2)
        (cg_refl p _) bF) aT)

end Sub

end TwoS

open TwoS

theorem two_sums : TwoSums := by
  intro K _ _ p ν r0 r1 _ om oms c c' μ hp hn hO hc hc' hμ0 hμ
  have hs : MvPowerSeries.HasSubst (sSub (r0 := r0) (r1 := r1) om oms μ) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_sSub om oms hμ0)
  have hcg := cg_two_sums (r0 := r0) (r1 := r1) hp hn hO hc hc' hμ0 hμ
  have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpK : (p : K) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    exact inv_ne_zero hpR hn.symm
  refine ⟨MvPowerSeries.C ((p : K)⁻¹) *
    (MvPowerSeries.subst (sSub om oms μ) (hh1 (E := EV ν r0 r1) p c c') - hhS p (uS c c')),
    fun n => ?_, ?_, ?_⟩
  · rw [MvPowerSeries.coeff_C_mul, norm_mul, norm_inv, hn, inv_inv]
    calc (p : ℝ) * _ ≤ (p : ℝ) * (p : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left (hcg n) (Nat.cast_nonneg p)
      _ = 1 := mul_inv_cancel₀ hpR
  · rw [map_mul, map_sub, constantCoeff_hhS hp.ne_zero,
      MvPowerSeries.constantCoeff_subst_eq_zero hs (constantCoeff_sSub om oms hμ0)
        (constant_coeff_hh_zero hp.ne_zero c c'), sub_zero, mul_zero]
  · rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hpK, map_one, one_mul, add_sub_cancel]

namespace TwoS

theorem subst_mvExp {K ι κ : Type} [NormedField K] [CharZero K] {ψ : ι → MvPowerSeries κ K}
    (hψ : MvPowerSeries.HasSubst ψ) {g : MvPowerSeries ι K}
    (hg : MvPowerSeries.constantCoeff g = 0) :
    MvPowerSeries.subst ψ (mvExp g) = mvExp (MvPowerSeries.subst ψ g) := by
  unfold mvExp
  rw [PowerSeries.subst_def, PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero hg).const hψ]

theorem constantCoeff_Gser {K : Type} [Field K] {p : ℕ} (hp : p ≠ 0) (c c' : K) :
    MvPowerSeries.constantCoeff (Gser p c c') = 0 := by
  simp [Gser, Aser_eq, Aser'_eq, constantCoeff_AA K hp]

theorem constantCoeff_Gtot {K E : Type} [Field K] [Fintype E] {p : ℕ} (hp : p ≠ 0)
    (c c' ϖ : K) : MvPowerSeries.constantCoeff (Gtot (E := E) p c c' ϖ) = 0 := by
  unfold Gtot
  rw [map_sum]
  refine Finset.sum_eq_zero fun e _ => ?_
  have h0 : ∀ a : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.C ϖ *
      (MvPowerSeries.X (if a = 0 then (false, e) else (true, e)) :
        MvPowerSeries (Bool × E) K)) = 0 := fun a => by simp
  exact MvPowerSeries.constantCoeff_subst_eq_zero
    (MvPowerSeries.hasSubst_of_constantCoeff_zero h0) h0 (constantCoeff_Gser hp c c')

theorem subst_Gtot {K E : Type} [Field K] [Fintype E] (p : ℕ) (c c' ϖ : K) :
    MvPowerSeries.subst (fun x : Bool × E => MvPowerSeries.C ϖ *
        (MvPowerSeries.X x : MvPowerSeries (Bool × E) K)) (Gtot (E := E) p c c' 1) =
      Gtot p c c' ϖ := by
  have hψ : MvPowerSeries.HasSubst (fun x : Bool × E => MvPowerSeries.C ϖ *
      (MvPowerSeries.X x : MvPowerSeries (Bool × E) K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun x => by simp
  unfold Gtot
  rw [← MvPowerSeries.coe_substAlgHom hψ, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [MvPowerSeries.coe_substAlgHom hψ, MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun a => by simp) hψ]
  congr 1
  funext a
  rw [map_one, one_mul, MvPowerSeries.subst_X hψ]

theorem subst_exp_Gtot {K E : Type} [NormedField K] [CharZero K] [Fintype E] {p : ℕ} (hp : p ≠ 0)
    (c c' ϖ : K) :
    MvPowerSeries.subst (fun x : Bool × E => MvPowerSeries.C ϖ *
        (MvPowerSeries.X x : MvPowerSeries (Bool × E) K)) (mvExp (-(Gtot (E := E) p c c' 1))) =
      mvExp (-(Gtot p c c' ϖ)) := by
  have hψ : MvPowerSeries.HasSubst (fun x : Bool × E => MvPowerSeries.C ϖ *
      (MvPowerSeries.X x : MvPowerSeries (Bool × E) K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun x => by simp
  rw [subst_mvExp hψ (by rw [map_neg, constantCoeff_Gtot hp, neg_zero]),
    ← MvPowerSeries.coe_substAlgHom hψ, map_neg, MvPowerSeries.coe_substAlgHom hψ, subst_Gtot]

end TwoS

theorem ThmSCore_of (h1 : RescaleCore) (h2 : ClassSubst) (h3 : ClassChange) (h4 : ClassMul)
    (h5 : TwoSums) (h6 : LogRescale) (h7 : LogRescaleUnique) : ThmSCore := by
  intro K _ _ _ p ν r0 r1 _ om oms c c' ϖ μ U hp hn hϖ hO hc hc' hμ0 hμ hU
  have hpK : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  obtain ⟨-, -, μ0, hμ00, -, hμ0s, -, hμa⟩ := h6 K p ϖ hp hn hϖ
  obtain rfl : μ = μ0 := h7 K p ϖ μ μ0 hp.two_le hpK hμ0 hμ00 hμ hμ0s
  have hϖ1 : ‖ϖ‖ ≤ 1 := by
    by_contra hlt
    replace hlt := not_le.1 hlt
    have hN : p ^ 2 - 1 ≠ 0 := by
      have : 4 ≤ p ^ 2 := by nlinarith [hp.two_le]
      omega
    have h := one_lt_pow₀ hlt hN
    rw [← norm_pow, hϖ, hn] at h
    exact absurd h (not_lt.2 (pinv_le_one p))
  have hφ0 := constantCoeff_sSub (r0 := r0) (r1 := r1) om oms hμ0
  have hφI := integral_sSub (r0 := r0) (r1 := r1) hp hn hO hμa
  have hsφ : MvPowerSeries.HasSubst (sSub (r0 := r0) (r1 := r1) om oms μ) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hφ0
  have hψ0 : ∀ x : Bool × EV ν r0 r1, MvPowerSeries.constantCoeff (MvPowerSeries.C ϖ *
      (MvPowerSeries.X x : MvPowerSeries (Bool × EV ν r0 r1) K)) = 0 := fun x => by simp
  have hψI : ∀ x : Bool × EV ν r0 r1, Integral (MvPowerSeries.C ϖ *
      (MvPowerSeries.X x : MvPowerSeries (Bool × EV ν r0 r1) K)) := fun x =>
    integral_mul (integral_C hϖ1) (integral_X x)
  have hsψ := MvPowerSeries.hasSubst_of_constantCoeff_zero hψ0
  have e0 : (fun x => MvPowerSeries.C ϖ * sSub (r0 := r0) (r1 := r1) om oms μ x) =
      fun x => MvPowerSeries.subst (sSub om oms μ) (MvPowerSeries.C ϖ *
        (MvPowerSeries.X x : MvPowerSeries (Bool × EV ν r0 r1) K)) := by
    funext x
    rw [MvPowerSeries.subst_mul hsφ, MvPowerSeries.subst_C, MvPowerSeries.subst_X hsφ]
  rw [e0, ← MvPowerSeries.subst_comp_subst_apply hsψ hsφ, MvPowerSeries.subst_mul hsψ,
    subst_exp_Gtot hp.ne_zero]
  have hh0 := constant_coeff_hh_zero (E := EV ν r0 r1) hp.ne_zero c c'
  have a1 := h1 K (EV ν r0 r1) p c c' ϖ hp hn hϖ hc hc'
  have a2 := h4 K _ (p : K) _ _ _ hh0 (integralSubstV U _ hU hψ0 hψI) a1
  have a3 := h2 K _ _ (p : K) _ _ _ hh0 hφ0 hφI a2
  obtain ⟨Y, hY, hY0, hYe⟩ := h5 K p ν r0 r1 om oms c c' μ hp hn hO hc hc' hμ0 hμa
  have a4 := h3 K _ (p : K) hpK (by rw [hn]; exact pinv_le_one p) _ (-Y) _
    (MvPowerSeries.constantCoeff_subst_eq_zero hsφ hφ0 hh0) (by rw [map_neg, hY0, neg_zero])
    (integral_neg hY) a3
  have e1 : MvPowerSeries.subst (sSub om oms μ) (hh1 (E := EV ν r0 r1) p c c') +
      MvPowerSeries.C (p : K) * -Y = hhS p (uS c c') := by
    rw [hYe]; ring
  rwa [e1] at a4

theorem theorem_s_from_k_one_of (h : ThmSCore) (hs : SimeqRules) : CyclicPowerClassOfExpEquiv := by
  intro K _ _ _ p ν r0 r1 _ om oms c c' ϖ μ U0 Φ be hp hn hϖ hO hc hc' hμ0 hμ hU0 hΦ0 hΦ hbe
  obtain ⟨r1', r2, r3, r4, -⟩ := hs K (Bool × EV ν r0 r1)
  obtain ⟨-, -, -, -, r5⟩ := hs K (Fin 2)
  have hsum : ∀ s : Finset (EV ν r0 r1),
      Simeq (∑ e ∈ s, MvPowerSeries.subst
        (fun a : Fin 2 => (MvPowerSeries.X (if a = 0 then (false, e) else (true, e)) :
          MvPowerSeries (Bool × EV ν r0 r1) K)) be)
        (∑ e ∈ s, MvPowerSeries.subst
        (fun a : Fin 2 => (MvPowerSeries.X (if a = 0 then (false, e) else (true, e)) :
          MvPowerSeries (Bool × EV ν r0 r1) K)) (Gser p c c')) := by
    classical
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using r1' 0
    | insert e s he ih =>
      rw [Finset.sum_insert he, Finset.sum_insert he]
      exact r4 _ _ _ _ (r5 _ _ _ _ (fun a => by simp) (fun a => integral_X _) hbe) ih
  have eG : (∑ e : EV ν r0 r1, MvPowerSeries.subst
        (fun a : Fin 2 => (MvPowerSeries.X (if a = 0 then (false, e) else (true, e)) :
          MvPowerSeries (Bool × EV ν r0 r1) K)) (Gser p c c')) = Gtot p c c' 1 := by
    unfold Gtot
    simp only [map_one, one_mul]
  have h1 : Simeq (Gtot p c c' 1) Φ := by
    rw [← eG]
    exact r2 _ _ (r3 _ _ _ hΦ (hsum Finset.univ))
  obtain ⟨h10, h1I⟩ := h1
  have e : mvExp (-Φ) * U0 = mvExp (-(Gtot (E := EV ν r0 r1) p c c' 1)) *
      (mvExp (Gtot p c c' 1 - Φ) * U0) := by
    rw [← mul_assoc, ← mvExp_add (by rw [map_neg, constantCoeff_Gtot hp.ne_zero, neg_zero]) h10]
    congr 2
    ring
  rw [e]
  exact h K p ν r0 r1 om oms c c' ϖ μ _ hp hn hϖ hO hc hc' hμ0 hμ (integral_mul h1I hU0)

end Formalism.InvariantFactorPaths.G7
