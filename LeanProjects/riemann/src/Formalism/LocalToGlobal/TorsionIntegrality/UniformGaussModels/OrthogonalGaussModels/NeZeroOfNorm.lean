import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.PairsK
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.NormLeOneOfQuad
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveJetsUnitBall
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SqrtInUnramifiedCompletion

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.CM (HasCMBy omegaK)
open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.L2.Th1.A (logSer expSer wpReg)
open Formalism.L2.Th1.D (normInt)
open Formalism.L2.Th1.D.GaussNormEstimates (normZ_lt normZ_one normZ_le norm_one_of_close)
open Formalism.G (unitBall)

namespace CalcPAux

variable {p : ℕ} [Fact p.Prime]

def Zc (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] := (Int.castRingHom ℂ_[p]).range.topologicalClosure

theorem int_mem (k : ℤ) : (k : ℂ_[p]) ∈ Zc p :=
  Subring.le_topologicalClosure _ ⟨k, rfl⟩

theorem isClosed_Zc : IsClosed (Zc p : Set ℂ_[p]) := Subring.isClosed_topologicalClosure _

theorem mem_Zc_iff {a : ℂ_[p]} :
    a ∈ Zc p ↔ a ∈ closure (Set.range (fun n : ℤ => (n : ℂ_[p]))) := Iff.rfl

theorem ne_zero_of_norm {a : ℂ_[p]} (ha : ‖a‖ = 1) : a ≠ 0 := by
  intro h
  rw [h, norm_zero] at ha
  exact zero_ne_one ha

theorem norm_p_lt : ‖((p : ℤ) : ℂ_[p])‖ < 1 := normZ_lt.2 dvd_rfl

theorem inv_int_mem {N : ℤ} (hN : ¬ (p : ℤ) ∣ N) : ((N : ℂ_[p]))⁻¹ ∈ Zc p := by
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 Fact.out
  have hN1 : ‖(N : ℂ_[p])‖ = 1 := normZ_one hN
  have hN0 : (N : ℂ_[p]) ≠ 0 := ne_zero_of_norm hN1
  rw [mem_Zc_iff, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hε (norm_p_lt (p := p))
  have hcop : IsCoprime N ((p : ℤ) ^ j) :=
    IsCoprime.pow_right ((Prime.coprime_iff_not_dvd hp).2 hN).symm
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨(u : ℂ_[p]), ⟨u, rfl⟩, ?_⟩
  have e : ((N : ℂ_[p]))⁻¹ - (u : ℂ_[p]) = (N : ℂ_[p])⁻¹ * ((v : ℂ_[p]) * ((p : ℤ) : ℂ_[p]) ^ j) := by
    have h1 : (u : ℂ_[p]) * (N : ℂ_[p]) + (v : ℂ_[p]) * ((p : ℤ) : ℂ_[p]) ^ j = 1 := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℂ_[p])) huv
    field_simp
    linear_combination -h1
  rw [dist_eq_norm, e, norm_mul, norm_inv, hN1, inv_one, one_mul, norm_mul, norm_pow]
  calc ‖(v : ℂ_[p])‖ * ‖((p : ℤ) : ℂ_[p])‖ ^ j ≤ 1 * ‖((p : ℤ) : ℂ_[p])‖ ^ j :=
        mul_le_mul_of_nonneg_right (normZ_le v) (pow_nonneg (norm_nonneg _) _)
    _ < ε := by rw [one_mul]; exact hj

theorem inv_mem_Zc {c : ℂ_[p]} (hc : c ∈ Zc p) (h1 : ‖c‖ = 1) : c⁻¹ ∈ Zc p := by
  have hc0 := ne_zero_of_norm h1
  have hcl : c⁻¹ ∈ closure (Zc p : Set ℂ_[p]) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨_, ⟨k, rfl⟩, hk⟩ := (Metric.mem_closure_iff.1 (mem_Zc_iff.1 hc)) (min ε 1)
      (lt_min hε one_pos)
    rw [dist_eq_norm] at hk
    have hk' : ‖(k : ℂ_[p]) - c‖ < 1 := by
      rw [norm_sub_rev]
      exact hk.trans_le (min_le_right _ _)
    have hk1 : ‖(k : ℂ_[p])‖ = 1 := norm_one_of_close hk' h1
    have hk0 := ne_zero_of_norm hk1
    have hpk : ¬ (p : ℤ) ∣ k := fun h => (normZ_lt.2 h).ne hk1
    refine ⟨_, inv_int_mem hpk, ?_⟩
    have e : c⁻¹ - (k : ℂ_[p])⁻¹ = c⁻¹ * (k : ℂ_[p])⁻¹ * ((k : ℂ_[p]) - c) := by
      field_simp
    rw [dist_eq_norm, e, norm_mul, norm_mul, norm_inv, norm_inv, h1, hk1, inv_one, one_mul, one_mul,
      norm_sub_rev]
    exact hk.trans_le (min_le_left _ _)
  rwa [isClosed_Zc.closure_eq] at hcl

variable (dK : ℕ) (ι : ℂ ≃+* ℂ_[p])

def em (mn : ℤ × ℤ) : ℂ_[p] × ℂ_[p] :=
  (ι ((mn.1 : ℂ) + (mn.2 : ℂ) * omegaK dK), ι ((mn.1 : ℂ) + (mn.2 : ℂ) * (1 - omegaK dK)))

theorem pairsK_eq : pairsK dK p ι = closure (Set.range (em dK ι)) := rfl

theorem em_add (a b : ℤ × ℤ) : em dK ι a + em dK ι b = em dK ι (a.1 + b.1, a.2 + b.2) := by
  refine Prod.ext ?_ ?_
  · show ι _ + ι _ = ι _
    rw [← map_add]
    congr 1
    push_cast
    ring
  · show ι _ + ι _ = ι _
    rw [← map_add]
    congr 1
    push_cast
    ring

theorem em_neg (a : ℤ × ℤ) : -em dK ι a = em dK ι (-a.1, -a.2) := by
  refine Prod.ext ?_ ?_
  · show -ι _ = ι _
    rw [← map_neg]
    congr 1
    push_cast
    ring
  · show -ι _ = ι _
    rw [← map_neg]
    congr 1
    push_cast
    ring

theorem em_int (k : ℤ) : em dK ι (k, 0) = ((k : ℂ_[p]), (k : ℂ_[p])) := by
  refine Prod.ext ?_ ?_
  · show ι _ = _
    simp
  · show ι _ = _
    simp

theorem em_swap (a : ℤ × ℤ) : (em dK ι a).swap = em dK ι (a.1 + a.2, -a.2) := by
  refine Prod.ext ?_ ?_
  · show ι _ = ι _
    congr 1
    push_cast
    ring
  · show ι _ = ι _
    congr 1
    push_cast
    ring

variable {dK}

theorem omega_sq' (hmod : dK % 4 = 3) :
    omegaK dK ^ 2 = omegaK dK - (((((dK : ℤ) + 1) / 4 : ℤ)) : ℂ) := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (dK : ℤ) + 1 = 4 * k := ⟨((dK : ℤ) + 1) / 4, by omega⟩
  have hdiv : ((dK : ℤ) + 1) / 4 = k := by omega
  have hk' : (dK : ℂ) + 1 = 4 * (k : ℂ) := by exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) hk
  rw [hdiv, Formalism.L2.Th1.D.CurveNormEndomorphisms.omega_sq]
  linear_combination (-1 / 4 : ℂ) * hk'

theorem em_mul (hmod : dK % 4 = 3) (a b : ℤ × ℤ) : em dK ι a * em dK ι b =
    em dK ι (a.1 * b.1 - a.2 * b.2 * (((dK : ℤ) + 1) / 4), a.1 * b.2 + b.1 * a.2 + a.2 * b.2) := by
  have h := omega_sq' hmod
  refine Prod.ext ?_ ?_
  · show ι _ * ι _ = ι _
    rw [← map_mul]
    congr 1
    push_cast at h ⊢
    linear_combination ((a.2 : ℂ) * (b.2 : ℂ)) * h
  · show ι _ * ι _ = ι _
    rw [← map_mul]
    congr 1
    push_cast at h ⊢
    linear_combination ((a.2 : ℂ) * (b.2 : ℂ)) * h

theorem em_sum (a : ℤ × ℤ) : (em dK ι a).1 + (em dK ι a).2 = ((2 * a.1 + a.2 : ℤ) : ℂ_[p]) := by
  show ι _ + ι _ = _
  rw [← map_add, ← map_intCast ι]
  congr 1
  push_cast
  ring

theorem em_prod (hmod : dK % 4 = 3) (a : ℤ × ℤ) :
    (em dK ι a).1 * (em dK ι a).2 = ((normInt dK a.1 a.2 : ℤ) : ℂ_[p]) := by
  show ι _ * ι _ = _
  rw [← map_mul, OrthogonalGaussModelNormLemmas.prod_bar hmod, map_intCast]

theorem em_norm_le (hmod : dK % 4 = 3) (a : ℤ × ℤ) :
    ‖(em dK ι a).1‖ ≤ 1 ∧ ‖(em dK ι a).2‖ ≤ 1 :=
  ⟨OrthogonalGaussModelNormLemmas.norm_le_one_of_quad (em_sum ι a) (em_prod ι hmod a) (normZ_le _),
   OrthogonalGaussModelNormLemmas.norm_le_one_of_quad (by rw [add_comm]; exact em_sum ι a)
     (by rw [mul_comm]; exact em_prod ι hmod a) (normZ_le _)⟩

def S0 (hmod : dK % 4 = 3) : Subring (ℂ_[p] × ℂ_[p]) where
  carrier := Set.range (em dK ι)
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨_, (em_mul ι hmod a b).symm⟩
  one_mem' := ⟨(1, 0), by rw [em_int]; simp⟩
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨_, (em_add dK ι a b).symm⟩
  zero_mem' := ⟨(0, 0), by rw [em_int]; simp⟩
  neg_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨_, (em_neg dK ι a).symm⟩

def OO (hmod : dK % 4 = 3) : Subring (ℂ_[p] × ℂ_[p]) := (S0 ι hmod).topologicalClosure

theorem mem_OO (hmod : dK % 4 = 3) {z : ℂ_[p] × ℂ_[p]} : z ∈ OO ι hmod ↔ z ∈ pairsK dK p ι := Iff.rfl

theorem em_mem (hmod : dK % 4 = 3) (a : ℤ × ℤ) : em dK ι a ∈ OO ι hmod :=
  Subring.le_topologicalClosure _ ⟨a, rfl⟩

theorem OO_induction (hmod : dK % 4 = 3) {P : ℂ_[p] × ℂ_[p] → Prop} (hc : IsClosed {z | P z})
    (h : ∀ a, P (em dK ι a)) {z : ℂ_[p] × ℂ_[p]} (hz : z ∈ OO ι hmod) : P z :=
  closure_minimal (s := Set.range (em dK ι)) (t := {z | P z}) (by rintro _ ⟨a, rfl⟩; exact h a) hc hz

theorem swap_mem (hmod : dK % 4 = 3) {z : ℂ_[p] × ℂ_[p]} (hz : z ∈ OO ι hmod) :
    z.swap ∈ OO ι hmod :=
  map_mem_closure continuous_swap hz (by
    rintro _ ⟨a, rfl⟩
    exact ⟨_, (em_swap dK ι a).symm⟩)

theorem norm_le (hmod : dK % 4 = 3) {z : ℂ_[p] × ℂ_[p]} (hz : z ∈ OO ι hmod) :
    ‖z.1‖ ≤ 1 ∧ ‖z.2‖ ≤ 1 :=
  OO_induction ι hmod (P := fun z => ‖z.1‖ ≤ 1 ∧ ‖z.2‖ ≤ 1)
    ((isClosed_le continuous_fst.norm continuous_const).inter
      (isClosed_le continuous_snd.norm continuous_const)) (em_norm_le ι hmod) hz

theorem sum_mem (hmod : dK % 4 = 3) {z : ℂ_[p] × ℂ_[p]} (hz : z ∈ OO ι hmod) : z.1 + z.2 ∈ Zc p :=
  OO_induction ι hmod (P := fun z => z.1 + z.2 ∈ Zc p)
    (isClosed_Zc.preimage (continuous_fst.add continuous_snd))
    (fun a => by rw [em_sum]; exact int_mem _) hz

theorem prod_mem (hmod : dK % 4 = 3) {z : ℂ_[p] × ℂ_[p]} (hz : z ∈ OO ι hmod) : z.1 * z.2 ∈ Zc p :=
  OO_induction ι hmod (P := fun z => z.1 * z.2 ∈ Zc p)
    (isClosed_Zc.preimage (continuous_fst.mul continuous_snd))
    (fun a => by rw [em_prod ι hmod]; exact int_mem _) hz

theorem diag_mem (hmod : dK % 4 = 3) {c : ℂ_[p]} (hc : c ∈ Zc p) : (c, c) ∈ OO ι hmod :=
  map_mem_closure (f := fun c : ℂ_[p] => (c, c)) (continuous_id.prodMk continuous_id) hc (by
    rintro _ ⟨k, rfl⟩
    exact ⟨(k, 0), em_int dK ι k⟩)

theorem diag_int (hmod : dK % 4 = 3) (h2 : p ≠ 2) {a : ℂ_[p]} (ha : (a, a) ∈ OO ι hmod) :
    a ∈ Zc p := by
  have h := sum_mem ι hmod ha
  have h2' : ¬ (p : ℤ) ∣ 2 := by
    intro h
    have h' : p ∣ 2 := by exact_mod_cast h
    exact h2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h')
  have hi := inv_int_mem h2'
  have h0 : ((2 : ℤ) : ℂ_[p]) ≠ 0 := ne_zero_of_norm (normZ_one h2')
  have e : a = ((2 : ℤ) : ℂ_[p])⁻¹ * (a + a) := by
    field_simp
    push_cast
    ring
  rw [e]
  exact (Zc p).mul_mem hi h

theorem inv_mem (hmod : dK % 4 = 3) {z : ℂ_[p] × ℂ_[p]} (hz : z ∈ OO ι hmod) (h1 : ‖z.1‖ = 1)
    (h2 : ‖z.2‖ = 1) : (z.1⁻¹, z.2⁻¹) ∈ OO ι hmod := by
  have hc : ‖z.1 * z.2‖ = 1 := by rw [norm_mul, h1, h2, one_mul]
  have hi := diag_mem ι hmod (inv_mem_Zc (prod_mem ι hmod hz) hc)
  have e : (z.1⁻¹, z.2⁻¹) = z.swap * ((z.1 * z.2)⁻¹, (z.1 * z.2)⁻¹) := by
    have a0 := ne_zero_of_norm h1
    have b0 := ne_zero_of_norm h2
    refine Prod.ext ?_ ?_
    · show z.1⁻¹ = z.2 * (z.1 * z.2)⁻¹
      field_simp
    · show z.2⁻¹ = z.1 * (z.1 * z.2)⁻¹
      field_simp
  rw [e]
  exact (OO ι hmod).mul_mem (swap_mem ι hmod hz) hi

theorem isUnit_of_norm (hmod : dK % 4 = 3) (z : OO ι hmod) (h1 : ‖z.1.1‖ = 1) (h2 : ‖z.1.2‖ = 1) :
    IsUnit z :=
  isUnit_iff_exists_inv.2 ⟨⟨_, inv_mem ι hmod z.2 h1 h2⟩, Subtype.ext (Prod.ext
    (mul_inv_cancel₀ (ne_zero_of_norm h1)) (mul_inv_cancel₀ (ne_zero_of_norm h2)))⟩

theorem norm_of_unit (hmod : dK % 4 = 3) (u : (OO ι hmod)ˣ) :
    ‖(u : OO ι hmod).1.1‖ = 1 ∧ ‖(u : OO ι hmod).1.2‖ = 1 := by
  have h : (u : OO ι hmod).1 * ((u⁻¹ : (OO ι hmod)ˣ) : OO ι hmod).1 = 1 :=
    congrArg Subtype.val u.mul_inv
  have hu := norm_le ι hmod (u : OO ι hmod).2
  have hv := norm_le ι hmod ((u⁻¹ : (OO ι hmod)ˣ) : OO ι hmod).2
  have aux : ∀ x y : ℂ_[p], ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → x * y = 1 → ‖x‖ = 1 := by
    intro x y hx hy hxy
    refine le_antisymm hx ?_
    have h3 : ‖x‖ * ‖y‖ = 1 := by rw [← norm_mul, hxy, norm_one]
    calc (1 : ℝ) = ‖x‖ * ‖y‖ := h3.symm
      _ ≤ ‖x‖ * 1 := mul_le_mul_of_nonneg_left hy (norm_nonneg x)
      _ = ‖x‖ := mul_one _
  exact ⟨aux _ _ hu.1 hv.1 (congrArg Prod.fst h), aux _ _ hu.2 hv.2 (congrArg Prod.snd h)⟩

@[reducible] def starOO (hmod : dK % 4 = 3) : StarRing (OO ι hmod) where
  star z := ⟨z.1.swap, swap_mem ι hmod z.2⟩
  star_involutive z := Subtype.ext (Prod.swap_swap z.1)
  star_mul a b := Subtype.ext (by
    show (a.1 * b.1).swap = b.1.swap * a.1.swap
    rw [mul_comm]
    rfl)
  star_add a b := Subtype.ext rfl

def tau (hmod : dK % 4 = 3) : OO ι hmod →+* ℂ_[p] :=
  (RingHom.fst ℂ_[p] ℂ_[p]).comp (OO ι hmod).subtype

theorem tau_apply (hmod : dK % 4 = 3) (z : OO ι hmod) : tau ι hmod z = z.1.1 := rfl

theorem selfadj (hmod : dK % 4 = 3) (h2 : p ≠ 2) {z : ℂ_[p] × ℂ_[p]} (hz : z ∈ OO ι hmod)
    (hs : z.swap = z) : z.1 ∈ Zc p := by
  apply diag_int ι hmod h2
  have e : (z.1, z.1) = z := Prod.ext rfl (congrArg Prod.fst hs).symm
  rw [e]
  exact hz

theorem exists_shift (h5 : 5 ≤ p) {a b : ℂ_[p]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ∃ k : ℤ, ‖(k : ℂ_[p])‖ = 1 ∧ ‖a - (k : ℂ_[p])‖ = 1 ∧ ‖b - (k : ℂ_[p])‖ = 1 := by
  have hsmall : ∀ z : ℤ, z ≠ 0 → z.natAbs < 5 → ‖(z : ℂ_[p])‖ = 1 := by
    intro z hz hlt
    apply normZ_one
    intro hd
    have h1 := Nat.le_of_dvd (Int.natAbs_pos.2 hz) (Int.natCast_dvd.1 hd)
    omega
  have sub_le : ∀ x y : ℂ_[p], ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
    intro x y
    rw [sub_eq_add_neg, ← norm_neg y]
    exact IsUltrametricDist.norm_add_le_max _ _
  have excl : ∀ (x : ℂ_[p]) (j k : ℤ), ‖((j - k : ℤ) : ℂ_[p])‖ = 1 →
      ¬ (‖x - (j : ℂ_[p])‖ < 1 ∧ ‖x - (k : ℂ_[p])‖ < 1) := by
    rintro x j k h ⟨h1, h2⟩
    have e : ((j - k : ℤ) : ℂ_[p]) = (x - (k : ℂ_[p])) - (x - (j : ℂ_[p])) := by
      push_cast
      ring
    rw [e] at h
    have h3 := sub_le (x - (k : ℂ_[p])) (x - (j : ℂ_[p]))
    rw [h] at h3
    exact absurd h3 (not_le.2 (max_lt h2 h1))
  have le1 : ∀ (x : ℂ_[p]) (k : ℤ), ‖x‖ ≤ 1 → ‖x - (k : ℂ_[p])‖ ≤ 1 := fun x k hx =>
    (sub_le _ _).trans (max_le hx (normZ_le k))
  have a12 := excl a 1 2 (hsmall _ (by decide) (by decide))
  have a13 := excl a 1 3 (hsmall _ (by decide) (by decide))
  have a23 := excl a 2 3 (hsmall _ (by decide) (by decide))
  have b12 := excl b 1 2 (hsmall _ (by decide) (by decide))
  have b13 := excl b 1 3 (hsmall _ (by decide) (by decide))
  have b23 := excl b 2 3 (hsmall _ (by decide) (by decide))
  have hk : ∃ k : ℤ, k ≠ 0 ∧ k.natAbs < 5 ∧ ¬ ‖a - (k : ℂ_[p])‖ < 1 ∧ ¬ ‖b - (k : ℂ_[p])‖ < 1 := by
    by_cases A1 : ‖a - ((1 : ℤ) : ℂ_[p])‖ < 1
    · by_cases B2 : ‖b - ((2 : ℤ) : ℂ_[p])‖ < 1
      · exact ⟨3, by decide, by decide, fun h => a13 ⟨A1, h⟩, fun h => b23 ⟨B2, h⟩⟩
      · exact ⟨2, by decide, by decide, fun h => a12 ⟨A1, h⟩, B2⟩
    · by_cases B1 : ‖b - ((1 : ℤ) : ℂ_[p])‖ < 1
      · by_cases A2 : ‖a - ((2 : ℤ) : ℂ_[p])‖ < 1
        · exact ⟨3, by decide, by decide, fun h => a23 ⟨A2, h⟩, fun h => b13 ⟨B1, h⟩⟩
        · exact ⟨2, by decide, by decide, A2, fun h => b12 ⟨B1, h⟩⟩
      · exact ⟨1, by decide, by decide, A1, B1⟩
  obtain ⟨k, k0, k5, hak, hbk⟩ := hk
  exact ⟨k, hsmall k k0 k5, le_antisymm (le1 a k ha) (not_lt.1 hak),
    le_antisymm (le1 b k hb) (not_lt.1 hbk)⟩

theorem two_units (hmod : dK % 4 = 3) (h5 : 5 ≤ p) (α : OO ι hmod) :
    ∃ u v : (OO ι hmod)ˣ, α = u + v := by
  obtain ⟨ha, hb⟩ := norm_le ι hmod α.2
  obtain ⟨k, hk, hak, hbk⟩ := exists_shift h5 ha hb
  have hu : IsUnit (⟨((k : ℂ_[p]), (k : ℂ_[p])), diag_mem ι hmod (int_mem k)⟩ : OO ι hmod) :=
    isUnit_of_norm ι hmod _ hk hk
  have hv : IsUnit (α - ⟨((k : ℂ_[p]), (k : ℂ_[p])), diag_mem ι hmod (int_mem k)⟩ : OO ι hmod) :=
    isUnit_of_norm ι hmod _ hak hbk
  refine ⟨hu.unit, hv.unit, ?_⟩
  rw [IsUnit.unit_spec, IsUnit.unit_spec]
  ring

def Dn (hmod : dK % 4 = 3) : Set (OO ι hmod) :=
  {z | ∃ a : ℤ × ℤ, ¬ (p : ℤ) ∣ normInt dK a.1 a.2 ∧ z.1 = em dK ι a}

theorem dense (hmod : dK % 4 = 3) (u : (OO ι hmod)ˣ) : (u : OO ι hmod) ∈ closure (Dn ι hmod) := by
  rw [closure_subtype, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨h1, h2⟩ := norm_of_unit ι hmod u
  have hm : (u : OO ι hmod).1 ∈ closure (Set.range (em dK ι)) := (u : OO ι hmod).2
  obtain ⟨_, ⟨a, rfl⟩, ha⟩ := Metric.mem_closure_iff.1 hm (min ε 1) (lt_min hε one_pos)
  refine ⟨em dK ι a, ⟨⟨_, em_mem ι hmod a⟩, ⟨a, ?_, rfl⟩, rfl⟩, ha.trans_le (min_le_left _ _)⟩
  have hlt := ha.trans_le (min_le_right _ _)
  rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm] at hlt
  have e1 : ‖(em dK ι a).1‖ = 1 := norm_one_of_close (by rw [norm_sub_rev]; exact hlt.1) h1
  have e2 : ‖(em dK ι a).2‖ = 1 := norm_one_of_close (by rw [norm_sub_rev]; exact hlt.2) h2
  intro hd
  have h3 : ‖((normInt dK a.1 a.2 : ℤ) : ℂ_[p])‖ < 1 := normZ_lt.2 hd
  rw [← em_prod ι hmod, norm_mul, e1, e2, one_mul] at h3
  exact lt_irrefl _ h3

end CalcPAux

open CalcPAux in

theorem CalcP_of (hD : CMDatum) : CalcP := by
  intro dK L hmod hcm p _ h5 ι hW
  have hp2 : p ≠ 2 := by omega
  have h2 : ‖(2 : ℂ_[p])‖ = 1 := OrthogonalGaussModelNormLemmas.norm_two p hp2
  have hM : Formalism.L2.Th1.A.IntModel (curveL p L ι) :=
    ⟨hW.1, hW.2.1, hW.2.2.1, hW.2.2.2.1, hW.2.2.2.2.1⟩
  obtain ⟨-, hFr, hF1⟩ := Formalism.L2.Th1.C.curve_frame_unit_ball ℂ_[p] h2 _ hM (ι (Formalism.L2.Th1.F.s2 L))
  have hb2 : (curveL p L ι).b₂ = 0 := (Formalism.L2.Th1.A.shortInv ℂ_[p] _ _).1
  let _ : StarRing (OO ι hmod) := starOO ι hmod
  have key := (Formalism.L2.Th1.C.curveEndoUnitBall ℂ_[p] h2 _ hM (ι (Formalism.L2.Th1.F.s2 L)) (OO ι hmod)
    (tau ι hmod)
    (continuous_fst.comp continuous_subtype_val)
    (Continuous.subtype_mk (continuous_swap.comp continuous_subtype_val) _)
    (fun z hz => selfadj ι hmod hp2 z.2 (congrArg Subtype.val hz))
    (isUnit_of_norm ι hmod 2 h2 h2)
    (two_units ι hmod h5)
    (Dn ι hmod) (dense ι hmod)
    (by
      intro α hα
      obtain ⟨⟨m, n⟩, hN, hα⟩ := hα
      obtain ⟨S, neg, xP, yP, g1, g2, g3, g4, g5⟩ := hD dK L hmod hcm p ι hW m n hN
      have t1 : tau ι hmod α = ι ((m : ℂ) + (n : ℂ) * omegaK dK) := congrArg Prod.fst hα
      have t2 : tau ι hmod (star α) = ι ((m : ℂ) + (n : ℂ) * (1 - omegaK dK)) :=
        congrArg Prod.snd hα
      refine ⟨S, inferInstance, neg, xP, yP, ?_, g2, g3, ?_, ?_, ?_, ?_⟩
      · rw [t1]
        exact g1
      · rw [t1, t2]
        exact g4
      · rw [t1]
        exact OrthogonalGaussModelNormLemmas.norm_eq_one_of_quad (em_sum ι (m, n)) (em_prod ι hmod (m, n)) (normZ_one hN)
      · rw [hb2]
        simp
      · rw [t1, t2]
        exact g5)).1
  refine ⟨hFr, hF1, fun a b hab => ?_, fun a ha => ?_⟩
  · have h := key ⟨(a, b), hab⟩
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  · have hz : a ∈ closure (Set.range (fun n : ℤ => (n : ℂ_[p]))) := diag_int ι hmod hp2 ha
    exact closure_minimal (s := Set.range (fun n : ℤ => (n : ℂ_[p])))
      (t := {z : ℂ_[p] | Formalism.L2.Th1.C.IsBinomScalar (unitBall ℂ_[p]) z})
      (by
        rintro _ ⟨n, rfl⟩
        exact Formalism.L2.Th1.C.intBinomScalar ℂ_[p] _ n)
      (Formalism.L2.Th1.C.binomClosed ℂ_[p] _ (Formalism.L2.Th1.C.unit_ball_closed ℂ_[p])) hz

end Formalism.L2.Th1.Top
