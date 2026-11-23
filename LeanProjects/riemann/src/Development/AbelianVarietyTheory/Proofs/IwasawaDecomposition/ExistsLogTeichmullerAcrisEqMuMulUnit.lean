import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Acris0TorsionFree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTeichmullerTiltMinusOnePowDivEnvelopeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.LogEx

theorem mul_pred_lt_pow (l v : ℕ) (hl : 1 ≤ l) : v * (l - 1) + 1 ≤ l ^ v := by
  obtain ⟨d, rfl⟩ : ∃ d, l = d + 1 := ⟨l - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  induction v with
  | zero => simp
  | succ v ih =>
    rw [pow_succ]
    nlinarith [Nat.zero_le (v * d * d)]

theorem exists_term {R : Type} [CommRing R] (l : ℕ) (hl : l.Prime)
    (hu : ∀ a : ℕ, ¬ l ∣ a → IsUnit (a : R)) (m w : R) (hw : (l : R) * w = m ^ (l - 1))
    (hwl : (l : R) ∣ w ^ l) (k : ℕ) :
    ∃ c : R, ((k + 1 : ℕ) : R) * c = m ^ k ∧ (l : R) ^ (k / (l - 1) / l) ∣ c ∧
      (k ≠ 0 → c ∈ (Ideal.span {(l : R)}).radical) := by
  obtain ⟨v, a, ha, hk⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.succ_ne_zero k) l hl.ne_one
  obtain ⟨b, hb⟩ := (hu a ha).exists_right_inv
  have hl2 := hl.two_le
  have ha0 : 1 ≤ a := Nat.pos_of_ne_zero (by rintro rfl; exact ha (dvd_zero _))
  have hv : v ≤ k / (l - 1) := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    have h1 := mul_pred_lt_pow l v hl.one_le
    have h2 : l ^ v ≤ l ^ v * a := Nat.le_mul_of_pos_right _ ha0
    omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hv
  have hqr := Nat.div_add_mod k (l - 1)
  set q := k / (l - 1) with hq
  set r := k % (l - 1) with hr
  have hwr : w ∈ (Ideal.span {(l : R)}).radical := ⟨l, Ideal.mem_span_singleton.2 hwl⟩
  have hmr : m ∈ (Ideal.span {(l : R)}).radical := ⟨l - 1, Ideal.mem_span_singleton.2 ⟨w, hw.symm⟩⟩
  refine ⟨b * (l : R) ^ d * m ^ r * w ^ q, ?_, ?_, fun hk0 => ?_⟩
  · have e : m ^ k = ((l : R) * w) ^ q * m ^ r := by
      rw [hw, ← pow_mul, ← pow_add, hqr]
    have e2 : ((k + 1 : ℕ) : R) = (l : R) ^ v * a := by
      rw [show k + 1 = l ^ v * a from hk]; push_cast; rfl
    rw [e, e2, mul_pow]
    have e3 : (l : R) ^ q = (l : R) ^ v * (l : R) ^ d := by rw [hd, pow_add]
    rw [e3]
    linear_combination ((l : R) ^ v * (l : R) ^ d * m ^ r * w ^ q) * hb
  · refine Dvd.dvd.mul_left ?_ _
    refine (pow_dvd_pow_of_dvd hwl _).trans ?_
    rw [← pow_mul]
    exact pow_dvd_pow _ (Nat.mul_div_le q l)
  · rcases Nat.eq_zero_or_pos q with h | h
    · have : 0 < r := by
        rw [h] at hqr
        omega
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hmr _ this))
    · exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hwr _ h)

theorem exists_sum {A : Type} [CommRing A] (p : A) [IsAdicComplete (Ideal.span {p}) A]
    (c : ℕ → A) (N : ℕ → ℕ) (hN : Monotone N) (hc : ∀ r k, N r ≤ k → p ^ r ∣ c k) :
    ∃ u : A, ∀ r n, N r ≤ n → p ^ r ∣ u - ∑ k ∈ Finset.range n, c k := by
  have key : ∀ r n, N r ≤ n →
      p ^ r ∣ ∑ k ∈ Finset.range n, c k - ∑ k ∈ Finset.range (N r), c k := by
    intro r n h
    rw [← Finset.sum_Ico_eq_sub _ h]
    exact Finset.dvd_sum fun k hk => hc r k (Finset.mem_Ico.1 hk).1
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {p}) (M := A) inferInstance
    (f := fun r => ∑ k ∈ Finset.range (N r), c k) (fun {a b} hab => by
      rw [SModEq.comm, SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton]
      exact key a _ (hN hab))
  refine ⟨L, fun r n h => ?_⟩
  have h1 := hL r
  rw [SModEq.comm, SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at h1
  have := dvd_sub h1 (key r n h)
  rwa [sub_sub_sub_cancel_right] at this

theorem exists_unit {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) (l : ℕ) (hl : l.Prime)
    (hA : IsAdicComplete (Ideal.span {(l : A)}) A)
    (hu : ∀ a : ℕ, ¬ l ∣ a → IsUnit (a : R)) (m w : R) (hw : (l : R) * w = m ^ (l - 1))
    (hwl : (l : R) ∣ w ^ l) :
    ∃ (c : ℕ → R) (u : A), (∀ k, ((k + 1 : ℕ) : R) * c k = m ^ k) ∧ IsUnit u ∧
      ∀ r : ℕ, ∃ N : ℕ, ∀ n ≥ N,
        (l : A) ^ r ∣ u - f (∑ k ∈ Finset.range n, (-1) ^ k * c k) := by
  choose c h1 h2 h3 using exists_term l hl hu m w hw hwl
  have hl2 := hl.two_le
  obtain ⟨u, hs⟩ := exists_sum (l : A) (fun k => f ((-1) ^ k * c k)) (fun r => r * l * (l - 1))
    (fun a b hab => Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hab)) (fun r k hk => by
      have hr : r ≤ k / (l - 1) / l := by
        rw [Nat.le_div_iff_mul_le (by omega), Nat.le_div_iff_mul_le (by omega)]
        exact hk
      have := map_dvd f (((pow_dvd_pow (l : R) hr).trans (h2 k)).mul_left ((-1) ^ k))
      rwa [map_pow, map_natCast] at this)
  refine ⟨c, u, h1, ?_, fun r => ⟨_, fun n hn => by rw [map_sum]; exact hs r n hn⟩⟩
  have hc0 : c 0 = 1 := by simpa using h1 0
  have hrad : u - 1 ∈ (Ideal.span {(l : A)}).radical := by
    have h := hs 1 (1 * l * (l - 1) + 1) (Nat.le_succ _)
    rw [Finset.sum_range_succ', pow_one, hc0, pow_zero, mul_one, map_one] at h
    have h' := Ideal.le_radical (Ideal.mem_span_singleton.2 h)
    have h'' : ∑ k ∈ Finset.range (1 * l * (l - 1)), f ((-1) ^ (k + 1) * c (k + 1)) ∈
        (Ideal.span {(l : A)}).radical := by
      refine Ideal.sum_mem _ fun k _ => ?_
      rw [map_mul]
      refine Ideal.mul_mem_left _ _ ?_
      obtain ⟨n, hn⟩ := h3 (k + 1) (Nat.succ_ne_zero k)
      refine ⟨n, Ideal.mem_span_singleton.2 ?_⟩
      have := map_dvd f (Ideal.mem_span_singleton.1 hn)
      rwa [map_pow, map_natCast] at this
    have := add_mem h' h''
    convert this using 1
    ring
  have hj : u - 1 ∈ Ideal.jacobson (⊥ : Ideal A) := by
    have h := Ideal.radical_le_jacobson hrad
    have h' := Ideal.jacobson_mono (IsAdicComplete.le_jacobson_bot (Ideal.span {(l : A)})) h
    rwa [Ideal.jacobson_idem] at h'
  exact Ideal.isUnit_of_sub_one_mem_jacobson_bot u hj

theorem isUnit_nat_acris0 (l : ℕ) [Fact l.Prime] (a : ℕ) (ha : ¬ l ∣ a) :
    IsUnit (a : Per.Acris0 l) := by
  have h : IsUnit (a : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 ha
  have := h.map ((algebraMap (Per.Ainf l) (Per.Acris0 l)).comp (Per.zA l))
  rwa [map_natCast] at this

theorem algebraMap_acris (l : ℕ) [Fact l.Prime] (x : Per.Ainf l) :
    algebraMap (Per.Ainf l) (Per.Acris l) x =
      algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) x) :=
  GlobalTheory.RingIface.tower l x

theorem factorial_mul_sum {P : Type} [CommRing P] (m : P) (c : ℕ → P)
    (h : ∀ k, ((k + 1 : ℕ) : P) * c k = m ^ k) (n : ℕ) :
    ((n.factorial : ℕ) : P) * (m * ∑ k ∈ Finset.range n, (-1) ^ k * c k) =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : P) * m ^ (k + 1) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hd : k + 1 ∣ n.factorial := Nat.dvd_factorial (Nat.succ_pos k) (Finset.mem_range.1 hk)
  have e : ((n.factorial : ℕ) : P) = ((n.factorial / (k + 1) : ℕ) : P) * ((k + 1 : ℕ) : P) := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel hd]
  rw [pow_succ m, ← h k]
  linear_combination (m * (-1) ^ k * c k) * e

end GlobalTheory.MemLoc.LogEx

namespace GlobalTheory.MemLoc
open LogEx

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris

theorem exists_isLogA : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, e.untilt = 1 →
    ∃ (t u : Per.Acris l), IsLogA e t ∧ IsUnit u ∧
      t = algebraMap (Per.Ainf l) (Per.Acris l) (mu e) * u := by
  intro l _ e he
  obtain ⟨w, hw, hwl⟩ := GlobalTheory.T.exists_teichmullerTiltMinusOne_pow_div_envelope l e he
  obtain ⟨c, u, h1, hu, h2⟩ := exists_unit (algebraMap (Per.Acris0 l) (Per.Acris l)) l Fact.out
    (acris_basic l).1 (isUnit_nat_acris0 l) (algebraMap (Per.Ainf l) (Per.Acris0 l) (mu e)) w
    (Subtype.ext (by simpa using hw)) hwl
  refine ⟨_, u, fun r => ?_, hu, rfl⟩
  obtain ⟨N, hN⟩ := h2 r
  refine ⟨N, fun n hn => ⟨algebraMap (Per.Ainf l) (Per.Acris0 l) (mu e) *
    ∑ k ∈ Finset.range n, (-1) ^ k * c k, ?_, ?_⟩⟩
  · have := congrArg (Per.Acris0 l).val
      (factorial_mul_sum (algebraMap (Per.Ainf l) (Per.Acris0 l) (mu e)) c h1 n)
    rw [map_mul, map_natCast, map_sum] at this
    refine this.trans (Finset.sum_congr rfl fun k _ => ?_)
    rw [map_mul, map_mul, map_pow, map_pow, map_natCast, map_neg, map_one, AlgHom.commutes]
  · obtain ⟨z, hz⟩ := hN n hn
    refine ⟨algebraMap (Per.Ainf l) (Per.Acris l) (mu e) * z, ?_⟩
    rw [map_mul, ← algebraMap_acris, ← mul_sub, hz]
    ring

end GlobalTheory.MemLoc
