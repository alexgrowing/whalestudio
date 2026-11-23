import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementE
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TheoremSFromKOneOf

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral low_subst_of_low)
open Formalism.FG.SolveVAux (Low low_zero low_mono low_add low_sub low_mul low_pow low_one_iff low_mul_sub
  low_of_zero)
open Formalism.FG.IntegralSubstitution (integral_mul integral_pow integral_one)
open TwoS (Cg cg_refl cg_of_eq cg_symm cg_trans cg_add cg_sum cg_mul cg_pow cg_frob_add cg_frob_sum
  integral_add integral_neg integral_sum integral_C integral_X integral_zero coeff_sPos pinv_nonneg)

namespace EDec

section LowGe

variable {K Tp Lw : Type} [Field K] [Fintype Lw]

def LowGe (m : ℕ) (f : MvPowerSeries (Tp ⊕ Lw) K) : Prop :=
  ∀ n, MvPowerSeries.coeff n f ≠ 0 → m ≤ lowDeg n

theorem lowGe_zero (m : ℕ) : LowGe m (0 : MvPowerSeries (Tp ⊕ Lw) K) :=
  fun n h => absurd (by simp) h

theorem lowGe_mono {m m' : ℕ} (h : m' ≤ m) {f : MvPowerSeries (Tp ⊕ Lw) K} (hf : LowGe m f) :
    LowGe m' f := fun n hn => h.trans (hf n hn)

theorem lowGe_add {m : ℕ} {f g : MvPowerSeries (Tp ⊕ Lw) K} (hf : LowGe m f) (hg : LowGe m g) :
    LowGe m (f + g) := by
  intro n h
  by_contra hlt
  apply h
  have h1 : MvPowerSeries.coeff n f = 0 := by
    by_contra h1; exact hlt (hf n h1)
  have h2 : MvPowerSeries.coeff n g = 0 := by
    by_contra h2; exact hlt (hg n h2)
  rw [map_add, h1, h2, add_zero]

theorem lowGe_sum {α : Type} {m : ℕ} (s : Finset α) (F : α → MvPowerSeries (Tp ⊕ Lw) K)
    (h : ∀ a ∈ s, LowGe m (F a)) : LowGe m (∑ a ∈ s, F a) := by
  intro n hn
  rw [map_sum] at hn
  obtain ⟨a, ha, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  exact h a ha n hne

theorem lowGe_mul_right {m : ℕ} {f : MvPowerSeries (Tp ⊕ Lw) K} (hf : LowGe m f)
    (g : MvPowerSeries (Tp ⊕ Lw) K) : LowGe m (f * g) := by
  classical
  intro n h
  rw [MvPowerSeries.coeff_mul] at h
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have h1 : MvPowerSeries.coeff x.1 f ≠ 0 := left_ne_zero_of_mul hne
  have hx' : x.1 + x.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
  refine (hf _ h1).trans ?_
  rw [← hx']
  unfold lowDeg
  exact Finset.sum_le_sum fun y _ => by simp

theorem lowGe_mul_left {m : ℕ} {f : MvPowerSeries (Tp ⊕ Lw) K} (hf : LowGe m f)
    (g : MvPowerSeries (Tp ⊕ Lw) K) : LowGe m (g * f) := by
  rw [mul_comm]; exact lowGe_mul_right hf g

theorem lowGe_X_pow (x : Lw) (m : ℕ) :
    LowGe m ((MvPowerSeries.X (Sum.inr x) : MvPowerSeries (Tp ⊕ Lw) K) ^ m) := by
  classical
  intro n h
  rw [MvPowerSeries.coeff_X_pow] at h
  split_ifs at h with e
  · subst e
    unfold lowDeg
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun y : Lw => (Finsupp.single (Sum.inr x : Tp ⊕ Lw) m) (Sum.inr y))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ x))
    simp
  · exact absurd rfl h

end LowGe

section Cong

variable {K ι : Type} [NormedField K] [IsUltrametricDist K]

theorem integral_negOnePow (l : ℕ) : Integral ((-1 : MvPowerSeries ι K) ^ l) :=
  integral_pow (integral_neg integral_one) l

theorem cg_frob_add_pow {p : ℕ} (hp : p.Prime) (hn : ‖(p : K)‖ = (p : ℝ)⁻¹)
    {f g : MvPowerSeries ι K} (hf : Integral f) (hg : Integral g) (a : ℕ) :
    Cg p ((f + g) ^ (p ^ a)) (f ^ (p ^ a) + g ^ (p ^ a)) := by
  induction a with
  | zero => simpa using cg_refl p (f + g)
  | succ a ih =>
    rw [pow_succ, pow_mul, pow_mul, pow_mul]
    exact cg_trans
      (cg_pow (integral_pow (integral_add hf hg) _)
        (integral_add (integral_pow hf _) (integral_pow hg _)) ih p)
      (cg_frob_add hp hn (integral_pow hf _) (integral_pow hg _))

theorem cg_second {p : ℕ} (hp : p.Prime) (hn : ‖(p : K)‖ = (p : ℝ)⁻¹) (E : ℕ)
    (z t : ℕ → MvPowerSeries ι K) (hz : ∀ l, Integral (z l)) (ht : ∀ l, Integral (t l)) :
    Cg p (∑ l ∈ range E, (-1) ^ l * (z l + t l) ^ ((p ^ 2) ^ l))
      (∑ l ∈ range E, (-1) ^ l * z l ^ (p ^ (2 * l)) +
        ∑ l ∈ range E, (-1) ^ l * t l ^ (p ^ (2 * l))) := by
  rw [← Finset.sum_add_distrib]
  refine cg_sum _ _ _ fun l _ => ?_
  rw [← mul_add, ← pow_mul]
  exact cg_mul (integral_negOnePow l) (integral_add (integral_pow (hz l) _) (integral_pow (ht l) _))
    (cg_refl p _) (cg_frob_add_pow hp hn (hz l) (ht l) _)

theorem cg_first {p : ℕ} (hp : p.Prime) (h2 : 2 < p) (hn : ‖(p : K)‖ = (p : ℝ)⁻¹) (E : ℕ)
    (z t : ℕ → MvPowerSeries ι K) (hz : ∀ l, Integral (z l)) (ht : ∀ l, Integral (t l)) :
    Cg p ((∑ l ∈ range E, (-1) ^ l * (z l + t l) ^ ((p ^ 2) ^ l)) ^ p)
      (∑ l ∈ range E, (-1) ^ l * z l ^ (p ^ (1 + 2 * l)) +
        ∑ l ∈ range E, (-1) ^ l * t l ^ (p ^ (1 + 2 * l))) := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  refine cg_trans (cg_frob_sum hp hn _ _ fun l _ =>
    integral_mul (integral_negOnePow l) (integral_pow (integral_add (hz l) (ht l)) _)) ?_
  rw [← Finset.sum_add_distrib]
  refine cg_sum _ _ _ fun l _ => ?_
  have e1 : ((-1 : MvPowerSeries ι K) ^ l) ^ p = (-1) ^ l := by
    rw [← pow_mul, mul_comm, pow_mul, hodd.neg_one_pow]
  have e2 : ((z l + t l) ^ ((p ^ 2) ^ l)) ^ p = (z l + t l) ^ (p ^ (1 + 2 * l)) := by
    rw [← pow_mul, ← pow_mul, ← pow_succ, add_comm 1 (2 * l)]
  rw [mul_pow, e1, e2, ← mul_add]
  exact cg_mul (integral_negOnePow l) (integral_add (integral_pow (hz l) _) (integral_pow (ht l) _))
    (cg_refl p _) (cg_frob_add_pow hp hn (hz l) (ht l) _)

theorem exists_of_cg {p : ℕ} (hp : p.Prime) (hn : ‖(p : K)‖ = (p : ℝ)⁻¹) {f g : MvPowerSeries ι K}
    (h : Cg p f g) : ∃ Y : MvPowerSeries ι K, Integral Y ∧ f = g + MvPowerSeries.C (p : K) * Y := by
  have hp0 : (p : K) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hn
    have : (0 : ℝ) < (p : ℝ)⁻¹ := by
      have := hp.pos
      positivity
    linarith
  refine ⟨MvPowerSeries.C ((p : K)⁻¹) * (f - g), fun n => ?_, ?_⟩
  · rw [MvPowerSeries.coeff_C_mul, norm_mul, norm_inv, hn, inv_inv]
    have hpp : (0 : ℝ) < p := by exact_mod_cast hp.pos
    calc (p : ℝ) * ‖MvPowerSeries.coeff n (f - g)‖ ≤ (p : ℝ) * (p : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left (h n) hpp.le
      _ = 1 := mul_inv_cancel₀ hpp.ne'
  · rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hp0, map_one, one_mul]
    ring

end Cong

section Trunc

variable {K : Type} [Field K] {ν r0 r1 : ℕ}

def sT (p E : ℕ) (s : ZMod (2 * ν)) (ab : Fin r0 × Fin r1) : MvPowerSeries (ZV ν r0 r1) K :=
  ∑ l ∈ range E, MvPowerSeries.C ((-1 : K) ^ l) *
    MvPowerSeries.X (s - 2 * (l : ZMod (2 * ν)), ab) ^ ((p ^ 2) ^ l)

def hhT [NeZero ν] (p E : ℕ) (u : ZMod (2 * ν) → K) : MvPowerSeries (ZV ν r0 r1) K :=
  ∑ s : ZMod (2 * ν), MvPowerSeries.C (u s) *
    ∑ ab : Fin r0 × Fin r1, sT p E s ab ^ p * sT p E (s + 1) ab

theorem low_sPos_sub {p : ℕ} (hp : 2 ≤ p) (E : ℕ) (s : ZMod (2 * ν)) (ab : Fin r0 × Fin r1) :
    Low ((p ^ 2) ^ E) (sPos (K := K) p s ab - sT p E s ab) := by
  classical
  intro n hn
  have key : ∀ l : ℕ, n = Finsupp.single (s - 2 * (l : ZMod (2 * ν)), ab) ((p ^ 2) ^ l) →
      l < n.degree + 1 ∧ l < E := by
    intro l e
    have hd : n.degree = (p ^ 2) ^ l := by rw [e, Finsupp.degree_single]
    refine ⟨by rw [hd]; exact lt_powq hp l, ?_⟩
    rw [hd] at hn
    exact (Nat.pow_lt_pow_iff_right (show 1 < p ^ 2 by nlinarith)).1 hn
  rw [map_sub, coeff_sPos, sT, map_sum, sub_eq_zero]
  simp only [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X_pow]
  calc _ = ∑ l ∈ range (E + n.degree + 1),
        (if n = Finsupp.single (s - 2 * (l : ZMod (2 * ν)), ab) ((p ^ 2) ^ l) then (-1 : K) ^ l
          else 0) :=
        Finset.sum_subset (Finset.range_mono (by omega))
          fun l _ hl => if_neg fun e => hl (mem_range.2 (key l e).1)
    _ = ∑ l ∈ range E,
        (if n = Finsupp.single (s - 2 * (l : ZMod (2 * ν)), ab) ((p ^ 2) ^ l) then (-1 : K) ^ l
          else 0) :=
        (Finset.sum_subset (Finset.range_mono (by omega))
          fun l _ hl => if_neg fun e => hl (mem_range.2 (key l e).2)).symm
    _ = _ := Finset.sum_congr rfl fun l _ => by split_ifs <;> simp

theorem low_pow_sub {ι : Type} {M : ℕ} {a b : MvPowerSeries ι K} (h : Low M (a - b)) (k : ℕ) :
    Low M (a ^ k - b ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, sub_self]; exact low_of_zero _
  | succ k ih => rw [pow_succ, pow_succ]; exact low_mul_sub ih h

theorem low_hh_sub [NeZero ν] {p : ℕ} (hp : 2 ≤ p) (E : ℕ) (u : ZMod (2 * ν) → K) :
    Low ((p ^ 2) ^ E) (hhS (r0 := r0) (r1 := r1) p u - hhT p E u) := by
  rw [hhS, hhT, ← Finset.sum_sub_distrib]
  refine low_sum _ _ _ fun s _ => ?_
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  have h : Low ((p ^ 2) ^ E) (∑ ab : Fin r0 × Fin r1,
      (sPos (K := K) p s ab ^ p * sPos p (s + 1) ab - sT p E s ab ^ p * sT p E (s + 1) ab)) :=
    low_sum _ _ _ fun ab _ =>
      low_mul_sub (low_pow_sub (low_sPos_sub hp E s ab) p) (low_sPos_sub hp E (s + 1) ab)
  simpa using low_mul (low_zero (MvPowerSeries.C (u s))) h

end Trunc

section Sub

variable {K : Type} [Field K] {ν r0 r1 : ℕ}

def tpS (TT : Finset (ZMod (2 * ν))) (ξ : ZMod (2 * ν) → Fin r0 → K) (x : ZV ν r0 r1) :
    MvPowerSeries (TpV ν r1 ⊕ ZV ν r0 r1) K :=
  if x.1 ∈ TT then MvPowerSeries.C (ξ x.1 x.2.1) * MvPowerSeries.X (Sum.inl (x.1, x.2.2)) else 0

def zlS (x : ZV ν r0 r1) : MvPowerSeries (TpV ν r1 ⊕ ZV ν r0 r1) K := MvPowerSeries.X (Sum.inr x)

theorem zSub_eq (TT : Finset (ZMod (2 * ν))) (ξ : ZMod (2 * ν) → Fin r0 → K) (x : ZV ν r0 r1) :
    zSub TT ξ x = zlS x + tpS TT ξ x := rfl

theorem constantCoeff_zSub (TT : Finset (ZMod (2 * ν))) (ξ : ZMod (2 * ν) → Fin r0 → K)
    (x : ZV ν r0 r1) : MvPowerSeries.constantCoeff (zSub TT ξ x) = 0 := by
  rw [zSub, map_add, MvPowerSeries.constantCoeff_X, zero_add]
  split_ifs <;> simp

theorem subst_sT [NeZero ν] (TT : Finset (ZMod (2 * ν))) (ξ : ZMod (2 * ν) → Fin r0 → K) (p E : ℕ)
    (s : ZMod (2 * ν)) (ab : Fin r0 × Fin r1) :
    MvPowerSeries.subst (zSub TT ξ) (sT (K := K) p E s ab) =
      ∑ l ∈ range E, (-1) ^ l * (zlS (s - 2 * (l : ZMod (2 * ν)), ab) +
        tpS TT ξ (s - 2 * (l : ZMod (2 * ν)), ab)) ^ ((p ^ 2) ^ l) := by
  have hs : MvPowerSeries.HasSubst (zSub (r1 := r1) TT ξ) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_zSub TT ξ)
  rw [← MvPowerSeries.coe_substAlgHom hs, sT, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [map_mul, map_pow, MvPowerSeries.substAlgHom_X, zSub_eq, map_neg, map_one]

theorem subst_hhT [NeZero ν] (TT : Finset (ZMod (2 * ν))) (ξ : ZMod (2 * ν) → Fin r0 → K) (p E : ℕ)
    (u : ZMod (2 * ν) → K) :
    MvPowerSeries.subst (zSub TT ξ) (hhT (r0 := r0) (r1 := r1) p E u) =
      ∑ s : ZMod (2 * ν), MvPowerSeries.C (u s) * ∑ ab : Fin r0 × Fin r1,
        MvPowerSeries.subst (zSub TT ξ) (sT (K := K) p E s ab) ^ p *
          MvPowerSeries.subst (zSub TT ξ) (sT (K := K) p E (s + 1) ab) := by
  have hs : MvPowerSeries.HasSubst (zSub (r1 := r1) TT ξ) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_zSub TT ξ)
  have hC : ∀ r : K, MvPowerSeries.substAlgHom hs (MvPowerSeries.C r) = MvPowerSeries.C r :=
    fun r => (MvPowerSeries.substAlgHom hs).commutes r
  rw [← MvPowerSeries.coe_substAlgHom hs, hhT, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_mul, hC, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [map_mul, map_pow]

def Zs1 (p E : ℕ) (s : ZMod (2 * ν)) (ab : Fin r0 × Fin r1) :
    MvPowerSeries (TpV ν r1 ⊕ ZV ν r0 r1) K :=
  ∑ l ∈ range E, (-1) ^ l * zlS (s - 2 * (l : ZMod (2 * ν)), ab) ^ (p ^ (1 + 2 * l))

def Ts1 (TT : Finset (ZMod (2 * ν))) (ξ : ZMod (2 * ν) → Fin r0 → K) (p E : ℕ) (s : ZMod (2 * ν))
    (ab : Fin r0 × Fin r1) : MvPowerSeries (TpV ν r1 ⊕ ZV ν r0 r1) K :=
  ∑ l ∈ range E, (-1) ^ l * tpS TT ξ (s - 2 * (l : ZMod (2 * ν)), ab) ^ (p ^ (1 + 2 * l))

def Zs2 (p E : ℕ) (s : ZMod (2 * ν)) (ab : Fin r0 × Fin r1) :
    MvPowerSeries (TpV ν r1 ⊕ ZV ν r0 r1) K :=
  ∑ l ∈ range E, (-1) ^ l * zlS (s + 1 - 2 * (l : ZMod (2 * ν)), ab) ^ (p ^ (2 * l))

def Ts2 (TT : Finset (ZMod (2 * ν))) (ξ : ZMod (2 * ν) → Fin r0 → K) (p E : ℕ) (s : ZMod (2 * ν))
    (ab : Fin r0 × Fin r1) : MvPowerSeries (TpV ν r1 ⊕ ZV ν r0 r1) K :=
  ∑ l ∈ range E, (-1) ^ l * tpS TT ξ (s + 1 - 2 * (l : ZMod (2 * ν)), ab) ^ (p ^ (2 * l))

def Zs2' (p E : ℕ) (s : ZMod (2 * ν)) (ab : Fin r0 × Fin r1) :
    MvPowerSeries (TpV ν r1 ⊕ ZV ν r0 r1) K :=
  ∑ l ∈ range E, if l = 0 then 0
    else (-1) ^ l * zlS (s + 1 - 2 * (l : ZMod (2 * ν)), ab) ^ (p ^ (2 * l))

theorem split_lin (TT : Finset (ZMod (2 * ν))) (ξ : ZMod (2 * ν) → Fin r0 → K) (p E : ℕ)
    (s : ZMod (2 * ν)) (ab : Fin r0 × Fin r1) :
    Ts1 TT ξ p E s ab * Zs2 p E s ab =
      Ts1 TT ξ p E s ab * zlS (s + 1, ab) + Ts1 TT ξ p E s ab * Zs2' p E s ab := by
  cases E with
  | zero => simp [Ts1]
  | succ E =>
    rw [← mul_add]
    congr 1
    rw [Zs2, Zs2', Finset.sum_range_succ', Finset.sum_range_succ']
    simp [add_comm]

theorem sort_prod (TT : Finset (ZMod (2 * ν))) (ξ : ZMod (2 * ν) → Fin r0 → K) (p E : ℕ)
    (s : ZMod (2 * ν)) (ab : Fin r0 × Fin r1) :
    (Zs1 p E s ab + Ts1 TT ξ p E s ab) * (Zs2 p E s ab + Ts2 TT ξ p E s ab) =
      Ts1 TT ξ p E s ab * Ts2 TT ξ p E s ab + Ts1 TT ξ p E s ab * zlS (s + 1, ab) +
        (Zs1 p E s ab * (Zs2 p E s ab + Ts2 TT ξ p E s ab) + Ts1 TT ξ p E s ab * Zs2' p E s ab) := by
  have := split_lin TT ξ p E s ab
  linear_combination this

end Sub

section Terms

variable {K : Type} [Field K] {ν r0 r1 : ℕ}

theorem topMonoS_single {Tp Lw : Type} (a : Tp) (m : ℕ) :
    topMonoS (K := K) (Lw := Lw) (Finsupp.single a m) = MvPowerSeries.X (Sum.inl a) ^ m := by
  rw [topMonoS, Finsupp.mapDomain_single, MvPowerSeries.X_pow_eq]

theorem topMonoS_add {Tp Lw : Type} (d d' : Tp →₀ ℕ) :
    topMonoS (K := K) (Lw := Lw) (d + d') = topMonoS d * topMonoS d' := by
  rw [topMonoS, topMonoS, topMonoS, Finsupp.mapDomain_add, MvPowerSeries.monomial_mul_monomial,
    one_mul]

theorem tpS_pos {TT : Finset (ZMod (2 * ν))} (ξ : ZMod (2 * ν) → Fin r0 → K) {x : ZV ν r0 r1}
    (h : x.1 ∈ TT) : tpS TT ξ x =
      MvPowerSeries.C (ξ x.1 x.2.1) * MvPowerSeries.X (Sum.inl (x.1, x.2.2)) := if_pos h

theorem tpS_neg {TT : Finset (ZMod (2 * ν))} (ξ : ZMod (2 * ν) → Fin r0 → K) {x : ZV ν r0 r1}
    (h : x.1 ∉ TT) : tpS TT ξ x = 0 := if_neg h

theorem aAof_pos {E : ℕ} (p : ℕ) (u : ZMod (2 * ν) → K) {TT : Finset (ZMod (2 * ν))}
    (ξ : ZMod (2 * ν) → Fin r0 → K) {φ : PhiI ν r0 r1 E} (h : pairFirst φ ∈ TT ∧ pairSecond φ ∈ TT) :
    aAof p u TT ξ φ =
      u φ.1 * (-1) ^ (φ.2.1.val + φ.2.2.1.val) * ξ (pairFirst φ) φ.2.2.2.1 ^ (p ^ (1 + 2 * φ.2.1.val)) *
        ξ (pairSecond φ) φ.2.2.2.1 ^ (p ^ (2 * φ.2.2.1.val)) := if_pos h

theorem aAof_neg {E : ℕ} (p : ℕ) (u : ZMod (2 * ν) → K) {TT : Finset (ZMod (2 * ν))}
    (ξ : ZMod (2 * ν) → Fin r0 → K) {φ : PhiI ν r0 r1 E} (h : ¬ (pairFirst φ ∈ TT ∧ pairSecond φ ∈ TT)) :
    aAof p u TT ξ φ = 0 := if_neg h

theorem A_term {E : ℕ} {p : ℕ} (hp : p ≠ 0) (u : ZMod (2 * ν) → K) (TT : Finset (ZMod (2 * ν)))
    (ξ : ZMod (2 * ν) → Fin r0 → K) (s : ZMod (2 * ν)) (l l' : Fin E) (ab : Fin r0 × Fin r1) :
    MvPowerSeries.C (u s) *
        (((-1) ^ l.val * tpS TT ξ (s - 2 * (l.val : ZMod (2 * ν)), ab) ^ (p ^ (1 + 2 * l.val))) *
          ((-1) ^ l'.val * tpS TT ξ (s + 1 - 2 * (l'.val : ZMod (2 * ν)), ab) ^ (p ^ (2 * l'.val)))) =
      MvPowerSeries.C (aAof p u TT ξ (s, l, l', ab)) *
        topMonoS (Lw := ZV ν r0 r1) (dAof p (s, l, l', ab)) := by
  have n1 : p ^ (1 + 2 * l.val) ≠ 0 := pow_ne_zero _ hp
  have n2 : p ^ (2 * l'.val) ≠ 0 := pow_ne_zero _ hp
  by_cases h1 : s - 2 * (l.val : ZMod (2 * ν)) ∈ TT
  · by_cases h2 : s + 1 - 2 * (l'.val : ZMod (2 * ν)) ∈ TT
    · rw [tpS_pos (x := (s - 2 * (l.val : ZMod (2 * ν)), ab)) ξ h1,
        tpS_pos (x := (s + 1 - 2 * (l'.val : ZMod (2 * ν)), ab)) ξ h2,
        aAof_pos (φ := (s, l, l', ab)) p u ξ ⟨h1, h2⟩, dAof, topMonoS_add, topMonoS_single,
        topMonoS_single]
      simp only [pairFirst, pairSecond, map_mul, map_pow, map_neg, map_one, mul_pow]
      ring
    · rw [tpS_neg (x := (s + 1 - 2 * (l'.val : ZMod (2 * ν)), ab)) ξ h2,
        aAof_neg (φ := (s, l, l', ab)) p u ξ (fun h => h2 h.2), zero_pow n2]
      simp
  · rw [tpS_neg (x := (s - 2 * (l.val : ZMod (2 * ν)), ab)) ξ h1,
      aAof_neg (φ := (s, l, l', ab)) p u ξ (fun h => h1 h.1), zero_pow n1]
    simp

theorem A_eq [NeZero ν] {p : ℕ} (hp : p ≠ 0) (E : ℕ) (u : ZMod (2 * ν) → K)
    (TT : Finset (ZMod (2 * ν))) (ξ : ZMod (2 * ν) → Fin r0 → K) :
    ∑ s : ZMod (2 * ν), MvPowerSeries.C (u s) *
        ∑ ab : Fin r0 × Fin r1, Ts1 TT ξ p E s ab * Ts2 TT ξ p E s ab =
      ∑ φ : PhiI ν r0 r1 E,
        MvPowerSeries.C (aAof p u TT ξ φ) * topMonoS (Lw := ZV ν r0 r1) (dAof p φ) := by
  symm
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  calc _ = ∑ l : Fin E, ∑ ab : Fin r0 × Fin r1, ∑ l' : Fin E,
        MvPowerSeries.C (aAof p u TT ξ (s, l, l', ab)) *
          topMonoS (Lw := ZV ν r0 r1) (dAof p (s, l, l', ab)) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = _ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ab _ => ?_
        rw [Ts1, Ts2, Finset.sum_range, Finset.sum_range, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l' _ => (A_term hp u TT ξ s l l' ab).symm

theorem lowLin_bBof [NeZero ν] {E : ℕ} (p : ℕ) (ξ : ZMod (2 * ν) → Fin r0 → K) (s : ZMod (2 * ν))
    (l : Fin E) (b : Fin r1) :
    lowLin (Tp := TpV ν r1) (bBof p ξ (s, l, b)) =
      ∑ a : Fin r0, MvPowerSeries.C (ξ s a ^ (p ^ (2 * l.val + 1))) *
        zlS (s + 2 * (l.val : ZMod (2 * ν)) + 1, (a, b)) := by
  classical
  have hc : s + ((2 * l.val + 1 : ℕ) : ZMod (2 * ν)) = s + 2 * (l.val : ZMod (2 * ν)) + 1 := by
    push_cast; ring
  simp only [lowLin, bBof, colDir, hc]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single (s + 2 * (l.val : ZMod (2 * ν)) + 1)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single b]
    · simp [zlS]
    · intro b' _ hb'
      simp [hb']
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro s' _ hs'
    refine Finset.sum_eq_zero fun x _ => ?_
    simp [hs']
  · intro h; exact absurd (Finset.mem_univ _) h

theorem B_term {E : ℕ} {p : ℕ} (hp : p ≠ 0) (u : ZMod (2 * ν) → K) (TT : Finset (ZMod (2 * ν)))
    (ξ : ZMod (2 * ν) → Fin r0 → K) (s : ZMod (2 * ν)) (l : Fin E) (a : Fin r0) (b : Fin r1) :
    MvPowerSeries.C (u (s + 2 * (l.val : ZMod (2 * ν)))) *
        (((-1) ^ l.val * tpS TT ξ (s, (a, b)) ^ (p ^ (1 + 2 * l.val))) *
          zlS (s + 2 * (l.val : ZMod (2 * ν)) + 1, (a, b))) =
      MvPowerSeries.C (aBof u TT (s, l, b)) * topMonoS (dBof p (s, l, b)) *
        (MvPowerSeries.C (ξ s a ^ (p ^ (2 * l.val + 1))) *
          zlS (s + 2 * (l.val : ZMod (2 * ν)) + 1, (a, b))) := by
  have n1 : p ^ (2 * l.val + 1) ≠ 0 := pow_ne_zero _ hp
  rw [add_comm 1 (2 * l.val), dBof, topMonoS_single]
  by_cases h1 : s ∈ TT
  · rw [tpS_pos (x := (s, (a, b))) ξ h1, aBof, if_pos h1]
    simp only [map_mul, map_pow, map_neg, map_one, mul_pow]
    ring
  · rw [tpS_neg (x := (s, (a, b))) ξ h1, aBof, if_neg h1, zero_pow n1]
    simp

theorem B_eq [NeZero ν] {p : ℕ} (hp : p ≠ 0) (E : ℕ) (u : ZMod (2 * ν) → K)
    (TT : Finset (ZMod (2 * ν))) (ξ : ZMod (2 * ν) → Fin r0 → K) :
    ∑ s : ZMod (2 * ν), MvPowerSeries.C (u s) *
        ∑ ab : Fin r0 × Fin r1, Ts1 TT ξ p E s ab * zlS (s + 1, ab) =
      ∑ k : KapI ν r1 E,
        MvPowerSeries.C (aBof u TT k) * topMonoS (dBof p k) * lowLin (bBof p ξ k) := by
  symm
  calc _ = ∑ s : ZMod (2 * ν), ∑ l : Fin E, ∑ b : Fin r1, ∑ a : Fin r0,
        MvPowerSeries.C (u (s + 2 * (l.val : ZMod (2 * ν)))) *
          (((-1) ^ l.val * tpS TT ξ (s, (a, b)) ^ (p ^ (1 + 2 * l.val))) *
            zlS (s + 2 * (l.val : ZMod (2 * ν)) + 1, (a, b))) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun l _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [lowLin_bBof, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => (B_term hp u TT ξ s l a b).symm
    _ = ∑ l : Fin E, ∑ s : ZMod (2 * ν), ∑ ab : Fin r0 × Fin r1,
        MvPowerSeries.C (u (s + 2 * (l.val : ZMod (2 * ν)))) *
          (((-1) ^ l.val * tpS TT ξ (s, ab) ^ (p ^ (1 + 2 * l.val))) *
            zlS (s + 2 * (l.val : ZMod (2 * ν)) + 1, ab)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = ∑ l : Fin E, ∑ s : ZMod (2 * ν), ∑ ab : Fin r0 × Fin r1,
        MvPowerSeries.C (u s) *
          (((-1) ^ l.val * tpS TT ξ (s - 2 * (l.val : ZMod (2 * ν)), ab) ^ (p ^ (1 + 2 * l.val))) *
            zlS (s + 1, ab)) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        refine Eq.trans ?_ (Equiv.sum_comp (Equiv.addRight (2 * (l.val : ZMod (2 * ν)))) _)
        simp only [Equiv.coe_addRight, add_sub_cancel_right]
    _ = _ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum, Finset.sum_comm]
        refine Finset.sum_congr rfl fun ab _ => ?_
        rw [Ts1, Finset.sum_range, Finset.sum_mul, Finset.mul_sum]

end Terms

section Rest

variable {K : Type} [NormedField K] [IsUltrametricDist K] {ν r0 r1 : ℕ}

theorem integral_zlS (x : ZV ν r0 r1) : Integral (zlS (K := K) x) := integral_X _

theorem integral_tpS (TT : Finset (ZMod (2 * ν))) {ξ : ZMod (2 * ν) → Fin r0 → K}
    (hξ : ∀ s a, ‖ξ s a‖ ≤ 1) (x : ZV ν r0 r1) : Integral (tpS TT ξ x) := by
  rw [tpS]
  split_ifs
  · exact integral_mul (integral_C (hξ _ _)) (integral_X _)
  · exact integral_zero

theorem integral_altSum {ι : Type} (E : ℕ) (f : ℕ → MvPowerSeries ι K) (e : ℕ → ℕ)
    (hf : ∀ l, Integral (f l)) : Integral (∑ l ∈ range E, (-1) ^ l * f l ^ e l) :=
  integral_sum _ _ fun l _ => integral_mul (integral_negOnePow l) (integral_pow (hf l) _)

theorem integral_second_sum_variant (p E : ℕ) (s : ZMod (2 * ν)) (ab : Fin r0 × Fin r1) :
    Integral (Zs2' (K := K) p E s ab) :=
  integral_sum _ _ fun l _ => by
    split_ifs
    · exact integral_zero
    · exact integral_mul (integral_negOnePow l) (integral_pow (integral_zlS _) _)

theorem low_order_first_sum [NeZero ν] (p E : ℕ) (s : ZMod (2 * ν)) (ab : Fin r0 × Fin r1) :
    LowGe p (Zs1 (K := K) p E s ab) :=
  lowGe_sum _ _ fun l _ => lowGe_mul_left
    (lowGe_mono (Nat.le_self_pow (by omega) p) (lowGe_X_pow _ _)) _

theorem low_order_second_sum_variant [NeZero ν] (p E : ℕ) (s : ZMod (2 * ν)) (ab : Fin r0 × Fin r1) :
    LowGe p (Zs2' (K := K) p E s ab) :=
  lowGe_sum _ _ fun l _ => by
    split_ifs with h
    · exact lowGe_zero _
    · exact lowGe_mul_left (lowGe_mono (Nat.le_self_pow (by omega) p) (lowGe_X_pow _ _)) _

end Rest

end EDec

open EDec in

theorem decomposition_of_hh : HhDecomp := by
  intro K _ _ p ν r0 r1 E D _ u TT ξ hp h2 hn hu hξ hD
  have hp0 : p ≠ 0 := hp.ne_zero
  have hs : MvPowerSeries.HasSubst (zSub (r1 := r1) TT ξ) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_zSub TT ξ)

  have hcg : Cg p (MvPowerSeries.subst (zSub TT ξ) (hhT (r0 := r0) (r1 := r1) p E u))
      (∑ s : ZMod (2 * ν), MvPowerSeries.C (u s) * ∑ ab : Fin r0 × Fin r1,
        (Zs1 p E s ab + Ts1 TT ξ p E s ab) * (Zs2 p E s ab + Ts2 TT ξ p E s ab)) := by
    rw [subst_hhT]
    refine cg_sum _ _ _ fun s _ => ?_
    have hI2 : ∀ ab : Fin r0 × Fin r1, Integral (Zs2 (K := K) p E s ab + Ts2 TT ξ p E s ab) :=
      fun ab => integral_add (integral_altSum E _ _ fun l => integral_zlS _)
        (integral_altSum E _ _ fun l => integral_tpS TT hξ _)
    refine cg_mul (integral_C (hu s)) (integral_sum _ _ fun ab _ => integral_mul
      (integral_add (integral_altSum E _ _ fun l => integral_zlS _)
        (integral_altSum E _ _ fun l => integral_tpS TT hξ _)) (hI2 ab)) (cg_refl p _) ?_
    refine cg_sum _ _ _ fun ab _ => ?_
    rw [subst_sT, subst_sT]
    refine cg_mul (integral_pow (integral_altSum E _ _ fun l =>
      integral_add (integral_zlS _) (integral_tpS TT hξ _)) p) (hI2 ab) ?_ ?_
    · exact cg_first hp h2 hn E _ _ (fun l => integral_zlS _) (fun l => integral_tpS TT hξ _)
    · exact cg_second hp hn E _ _ (fun l => integral_zlS _) (fun l => integral_tpS TT hξ _)
  obtain ⟨Y, hY, hYe⟩ := exists_of_cg hp hn hcg
  refine ⟨∑ s : ZMod (2 * ν), MvPowerSeries.C (u s) * ∑ ab : Fin r0 × Fin r1,
      (Zs1 p E s ab * (Zs2 p E s ab + Ts2 TT ξ p E s ab) + Ts1 TT ξ p E s ab * Zs2' p E s ab),
    Y, ?_, hY, ?_, ?_⟩
  · refine integral_sum _ _ fun s _ => integral_mul (integral_C (hu s))
      (integral_sum _ _ fun ab _ => integral_add (integral_mul ?_ (integral_add ?_ ?_))
        (integral_mul ?_ (integral_second_sum_variant p E s ab)))
    · exact integral_altSum E _ _ fun l => integral_zlS _
    · exact integral_altSum E _ _ fun l => integral_zlS _
    · exact integral_altSum E _ _ fun l => integral_tpS TT hξ _
    · exact integral_altSum E _ _ fun l => integral_tpS TT hξ _
  · exact lowGe_sum _ _ fun s _ => lowGe_mul_left (lowGe_sum _ _ fun ab _ =>
      lowGe_add (lowGe_mul_right (low_order_first_sum p E s ab) _) (lowGe_mul_left (low_order_second_sum_variant p E s ab) _)) _
  · intro n hnD
    have hlow : Low ((p ^ 2) ^ E) (MvPowerSeries.subst (zSub TT ξ)
        (hhS (r0 := r0) (r1 := r1) p u - hhT p E u)) :=
      low_subst_of_low (constantCoeff_zSub TT ξ) (low_hh_sub hp.two_le E u)
    have h0 := hlow n (by rw [← pow_mul]; omega)
    rw [MvPowerSeries.subst_sub hs, map_sub, sub_eq_zero] at h0
    rw [h0, hYe, ← A_eq hp0 E u TT ξ, ← B_eq hp0 E u TT ξ]
    congr 2
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← mul_add, ← mul_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun ab _ => sort_prod TT ξ p E s ab

end Formalism.InvariantFactorPaths.G7
