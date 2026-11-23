import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import GroundTheory.LocalFields.FormalGroups.LubinTateGroup
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.AdicMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section

open Ideal

namespace GlobalTheory.LTTilt

section General

variable {O : Type} [CommRing O] {l : ℕ} [hl : Fact l.Prime] [Fact (¬ IsUnit (l : O))]

def IsTiltOf (f : ℕ) (π : O) (x : PreTilt O l) (v : ℕ → O) : Prop :=
  ∀ n : ℕ, ∃ y : O, PreTilt.coeff (f * n) x = Ideal.Quotient.mk (span {(l : O)}) y ∧ y - v n ∈ span {π}

omit [Fact (¬ IsUnit (l : O))] in
theorem geom_mem (I : Ideal O) (hlI : (l : O) ∈ I) {a b : O} (h : a - b ∈ I) :
    ∑ i ∈ Finset.range l, a ^ i * b ^ (l - 1 - i) ∈ I := by
  rw [← Ideal.Quotient.eq_zero_iff_mem] at h hlI ⊢
  have hab : Ideal.Quotient.mk I a = Ideal.Quotient.mk I b := by rw [← sub_eq_zero, ← map_sub]; exact h
  rw [map_sum]
  simp only [map_mul, map_pow, hab, ← pow_add]
  have e : ∀ i ∈ Finset.range l, Ideal.Quotient.mk I b ^ (i + (l - 1 - i)) = Ideal.Quotient.mk I b ^ (l - 1) := by
    intro i hi
    rw [Finset.mem_range] at hi
    congr 1
    omega
  rw [Finset.sum_congr rfl e, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [map_natCast] at hlI
  rw [hlI, zero_mul]

omit [Fact (¬ IsUnit (l : O))] in

theorem pow_l_sub_mem (I : Ideal O) (hlI : (l : O) ∈ I) {a b : O} {j : ℕ} (hj : 1 ≤ j) (h : a - b ∈ I ^ j) :
    a ^ l - b ^ l ∈ I ^ (j + 1) := by
  rw [← geom_sum₂_mul, pow_succ']
  exact Ideal.mul_mem_mul (geom_mem I hlI (Ideal.pow_le_self (by omega) h)) h

omit [Fact (¬ IsUnit (l : O))] in

theorem pow_l_pow_sub_mem (I : Ideal O) (hlI : (l : O) ∈ I) {a b : O} (h : a - b ∈ I) (k : ℕ) :
    a ^ (l ^ k) - b ^ (l ^ k) ∈ I ^ (k + 1) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [pow_succ l k, pow_mul, pow_mul]
    exact pow_l_sub_mem I hlI (by omega) ih

omit [hl : Fact l.Prime] [Fact (¬ IsUnit (l : O))] in
theorem pow_sub_mem (I : Ideal O) {a b : O} (h : a - b ∈ I) (m : ℕ) : a ^ m - b ^ m ∈ I := by
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow a b m
  rw [hc]
  exact I.mul_mem_right c h

omit [hl : Fact l.Prime] [Fact (¬ IsUnit (l : O))] in

theorem compat_pow (I : Ideal O) (q : ℕ) {v : ℕ → O} (hv : ∀ n, v (n + 1) ^ q - v n ∈ I) (m n : ℕ) :
    v (n + m) ^ (q ^ m) - v n ∈ I := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : v (n + (m + 1)) ^ (q ^ (m + 1)) - v n =
        ((v (n + m + 1) ^ q) ^ (q ^ m) - v (n + m) ^ (q ^ m)) + (v (n + m) ^ (q ^ m) - v n) := by
      rw [← add_assoc, pow_succ', pow_mul]; ring
    rw [e]
    exact I.add_mem (pow_sub_mem I (hv (n + m)) _) ih

theorem coeff_eq_pow (x : PreTilt O l) (k m : ℕ) :
    PreTilt.coeff k x = PreTilt.coeff (k + m) x ^ (l ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [ih, pow_succ' l m, pow_mul]
    congr 1
    show x.1 (k + m) = x.1 (k + m + 1) ^ l
    exact (x.2 (k + m)).symm

variable (f : ℕ) (π : O)

variable (l) in

def tiltSeq (N : ℕ) (v : ℕ → O) (k : ℕ) : ModP O l :=
  Ideal.Quotient.mk (span {(l : O)}) (v (k + N) ^ (l ^ (f * (k + N) - k)))

variable {f π}

theorem span_pow_le (N : ℕ) (hN : π ^ N ∈ span {(l : O)}) {j : ℕ} (hj : N ≤ j) :
    span {π} ^ j ≤ span {(l : O)} := by
  refine (Ideal.pow_le_pow_right hj).trans ?_
  rw [Ideal.span_singleton_pow, Ideal.span_le, Set.singleton_subset_iff]
  exact hN

theorem tiltSeq_pow (hf : 0 < f) (hπl : (l : O) ∈ span {π}) (N : ℕ) (hN : π ^ N ∈ span {(l : O)})
    {v : ℕ → O} (hv : ∀ n, v (n + 1) ^ (l ^ f) - v n ∈ span {π}) (k : ℕ) :
    tiltSeq l f N v (k + 1) ^ l = tiltSeq l f N v k := by
  unfold tiltSeq
  rw [← map_pow, Ideal.Quotient.eq]
  set A := f * (k + N) with hA
  have h1 : f * (k + 1 + N) = A + f := by rw [hA]; ring
  have h2 : k + N ≤ A := by rw [hA]; exact Nat.le_mul_of_pos_left _ hf
  have he : (v (k + 1 + N) ^ l ^ (f * (k + 1 + N) - (k + 1))) ^ l =
      (v (k + N + 1) ^ (l ^ f)) ^ (l ^ (A - k)) := by
    rw [← pow_mul, ← pow_succ, ← pow_mul, ← pow_add, h1]
    have : k + 1 + N = k + N + 1 := by omega
    rw [this]
    congr 2
    omega
  rw [he]
  refine span_pow_le N hN (j := A - k + 1) (by omega) ?_
  exact pow_l_pow_sub_mem _ hπl (hv (k + N)) (A - k)

def tiltOf (hf : 0 < f) (hπl : (l : O) ∈ span {π}) (N : ℕ) (hN : π ^ N ∈ span {(l : O)})
    (v : ℕ → O) (hv : ∀ n, v (n + 1) ^ (l ^ f) - v n ∈ span {π}) : PreTilt O l :=
  (⟨tiltSeq l f N v, tiltSeq_pow hf hπl N hN hv⟩ : Perfection (ModP O l) l)

theorem isTiltOf_tiltOf (hf : 0 < f) (hπl : (l : O) ∈ span {π}) (N : ℕ) (hN : π ^ N ∈ span {(l : O)})
    (v : ℕ → O) (hv : ∀ n, v (n + 1) ^ (l ^ f) - v n ∈ span {π}) :
    IsTiltOf f π (tiltOf hf hπl N hN v hv) v := by
  intro n
  refine ⟨v (f * n + N) ^ (l ^ (f * (f * n + N) - f * n)), rfl, ?_⟩
  have hn : n ≤ f * n := Nat.le_mul_of_pos_left _ hf
  obtain ⟨t, ht⟩ : ∃ t, f * n + N = n + t := ⟨f * n + N - n, by omega⟩
  have e1 : f * (f * n + N) - f * n = f * t := by
    have : f * (f * n + N) = f * n + f * t := by rw [ht, mul_add]
    omega
  rw [e1, ht, pow_mul]
  exact compat_pow _ _ hv t n

theorem isTiltOf_unique (hf : 0 < f) (hπl : (l : O) ∈ span {π}) (N : ℕ) (hN : π ^ N ∈ span {(l : O)})
    {v : ℕ → O} {x x' : PreTilt O l} (hx : IsTiltOf f π x v) (hx' : IsTiltOf f π x' v) : x = x' := by
  refine Perfection.ext fun k => ?_
  change PreTilt.coeff k x = PreTilt.coeff k x'
  have hn : k + N ≤ f * (k + N) := Nat.le_mul_of_pos_left _ hf
  obtain ⟨y, hy, hyv⟩ := hx (k + N)
  obtain ⟨y', hy', hyv'⟩ := hx' (k + N)
  have hm : k + (f * (k + N) - k) = f * (k + N) := by omega
  rw [coeff_eq_pow x k (f * (k + N) - k), coeff_eq_pow x' k (f * (k + N) - k), hm, hy, hy', ← map_pow,
    ← map_pow, Ideal.Quotient.eq]
  refine span_pow_le N hN (j := f * (k + N) - k + 1) (by omega) ?_
  refine pow_l_pow_sub_mem _ hπl ?_ _
  have := (span {π}).sub_mem hyv hyv'
  rwa [sub_sub_sub_cancel_right] at this

theorem ne_zero_of_isTiltOf (hπl : (l : O) ∈ span {π}) {v : ℕ → O} {x : PreTilt O l}
    (hx : IsTiltOf f π x v) (n : ℕ) (hn : v n ∉ span {π}) : x ≠ 0 := by
  rintro rfl
  obtain ⟨y, hy, hyv⟩ := hx n
  rw [map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem] at hy
  have hy' : y ∈ span {π} := (span_le.2 (Set.singleton_subset_iff.2 hπl)) hy
  apply hn
  have := (span {π}).sub_mem hy' hyv
  rwa [sub_sub_cancel] at this

theorem not_isUnit_of_isTiltOf (hπl : (l : O) ∈ span {π}) (hπ : ¬ IsUnit π) {v : ℕ → O} {x : PreTilt O l}
    (hx : IsTiltOf f π x v) (h0 : v 0 ∈ span {π}) : ¬ IsUnit x := by
  intro hu
  obtain ⟨y, hy, hyv⟩ := hx 0
  rw [mul_zero] at hy
  have hyI : y ∈ span {π} := by
    have := (span {π}).add_mem hyv h0
    rwa [sub_add_cancel] at this
  have hle : span {(l : O)} ≤ span {π} := span_le.2 (Set.singleton_subset_iff.2 hπl)
  have h1 := (hu.map (PreTilt.coeff 0)).map (Ideal.Quotient.factor hle)
  rw [hy, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.2 hyI] at h1
  apply hπ
  rw [← Ideal.span_singleton_eq_top, Ideal.eq_top_iff_one, ← Ideal.Quotient.eq_zero_iff_mem, map_one]
  exact (isUnit_zero_iff.1 h1).symm

end General

end GlobalTheory.LTTilt

namespace GlobalTheory.LTTilt

open Formalism.BasicNotions Formalism.BasicNotions.Loc

section OC

variable {l : ℕ} [Fact l.Prime]

theorem norm_eq_valuation (x : ℂ_[l]) : ‖x‖ = ((Valued.v x : NNReal) : ℝ) := by
  rw [PadicComplex.norm_eq_norm, Valuation.norm_def, PadicComplex.RankOne.hom_eq_embedding,
    Valuation.embedding_restrict]

theorem mem_OC_iff (x : ℂ_[l]) : x ∈ 𝓞_ℂ_[l] ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, norm_eq_valuation]
  exact_mod_cast Iff.rfl

theorem norm_OC_le_one (x : OC l) : ‖(x : ℂ_[l])‖ ≤ 1 := (mem_OC_iff _).1 x.2

theorem mem_span_iff_norm (c z : OC l) : z ∈ span {c} ↔ ‖(z : ℂ_[l])‖ ≤ ‖(c : ℂ_[l])‖ := by
  rw [mem_span_singleton']
  constructor
  · rintro ⟨a, rfl⟩
    push_cast
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_OC_le_one a)
  · intro h
    by_cases hc : (c : ℂ_[l]) = 0
    · rw [hc, norm_zero, norm_le_zero_iff] at h
      refine ⟨0, Subtype.ext ?_⟩
      push_cast
      rw [zero_mul, h]
    · refine ⟨⟨(z : ℂ_[l]) / c, (mem_OC_iff _).2 ?_⟩, Subtype.ext ?_⟩
      · rw [norm_div, div_le_one (norm_pos_iff.2 hc)]
        exact h
      · show (z : ℂ_[l]) / c * c = z
        exact div_mul_cancel₀ _ hc

theorem norm_lt_one_of_not_isUnit (π : OC l) (hπ : ¬ IsUnit π) : ‖(π : ℂ_[l])‖ < 1 := by
  refine lt_of_le_of_ne (norm_OC_le_one π) fun h => hπ ?_
  have h0 : (π : ℂ_[l]) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h
    exact zero_ne_one h
  refine isUnit_iff_exists_inv.2 ⟨⟨(π : ℂ_[l])⁻¹, (mem_OC_iff _).2 (by rw [norm_inv, h, inv_one])⟩,
    Subtype.ext ?_⟩
  show (π : ℂ_[l]) * (π : ℂ_[l])⁻¹ = 1
  exact mul_inv_cancel₀ h0

theorem exists_pow_mem_span (π : OC l) (hπ : ¬ IsUnit π) : ∃ N : ℕ, π ^ N ∈ span {((l : ℕ) : OC l)} := by
  have hl0 : (0 : ℝ) < ‖((l : ℕ) : ℂ_[l])‖ :=
    norm_pos_iff.2 (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hl0 (norm_lt_one_of_not_isUnit π hπ)
  refine ⟨N, (mem_span_iff_norm _ _).2 ?_⟩
  push_cast
  rw [norm_pow]
  exact hN.le

theorem norm_le_of_hasSum {g : ℕ → ℂ_[l]} {s : ℂ_[l]} (h : HasSum g s) {C : ℝ} (hC : ∀ i, ‖g i‖ ≤ C) :
    ‖s‖ ≤ C := by
  rw [← h.tsum_eq]
  exact IsUltrametricDist.norm_tsum_le_of_forall_le hC

theorem pow_sub_mem_of_hasSum (q : ℕ) (π : OC l) (F : PowerSeries (OC l))
    (hF : ∀ i, PowerSeries.coeff i (F - PowerSeries.X ^ q) ∈ span {π}) (x y : OC l)
    (hS : HasSum (fun i => ((PowerSeries.coeff i F * x ^ i : OC l) : ℂ_[l])) (y : ℂ_[l])) :
    x ^ q - y ∈ span {π} := by
  rw [mem_span_iff_norm]
  have h2 : HasSum (fun i => ((PowerSeries.coeff i (F - PowerSeries.X ^ q) * x ^ i : OC l) : ℂ_[l]))
      ((y : ℂ_[l]) - (x : ℂ_[l]) ^ q) := by
    have := hS.sub (hasSum_ite_eq q ((x : ℂ_[l]) ^ q))
    have e : (fun i => ((PowerSeries.coeff i (F - PowerSeries.X ^ q) * x ^ i : OC l) : ℂ_[l])) =
        fun i => ((PowerSeries.coeff i F * x ^ i : OC l) : ℂ_[l]) - (if i = q then (x : ℂ_[l]) ^ q else 0) := by
      funext i
      rw [map_sub, PowerSeries.coeff_X_pow]
      split_ifs with hi
      · subst hi
        push_cast
        ring
      · push_cast
        ring
    rw [e]
    exact this
  have h3 := norm_le_of_hasSum h2 (C := ‖(π : ℂ_[l])‖) fun i =>
    (mem_span_iff_norm _ _).1 (Ideal.mul_mem_right (x ^ i) _ (hF i))
  push_cast
  rw [norm_sub_rev]
  exact h3

theorem norm_le_of_hasSum_small (π : OC l) (F : PowerSeries (OC l)) (h0 : PowerSeries.constantCoeff F = 0)
    (h1 : PowerSeries.coeff 1 F = π) (x y : OC l)
    (hS : HasSum (fun i => ((PowerSeries.coeff i F * x ^ i : OC l) : ℂ_[l])) (y : ℂ_[l]))
    (hx : ‖(x : ℂ_[l])‖ ≤ ‖(π : ℂ_[l])‖) : ‖(y : ℂ_[l])‖ ≤ ‖(π : ℂ_[l])‖ * ‖(x : ℂ_[l])‖ := by
  refine norm_le_of_hasSum hS fun i => ?_
  have hxn := norm_nonneg (x : ℂ_[l])
  have hx1 : ‖(x : ℂ_[l])‖ ≤ 1 := norm_OC_le_one x
  rcases i with _ | _ | i
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
    simp only [zero_mul, ZeroMemClass.coe_zero, norm_zero]
    positivity
  · rw [h1]
    push_cast
    rw [norm_mul, pow_one]
  · push_cast
    rw [norm_mul, norm_pow]
    have hp : ‖(x : ℂ_[l])‖ ^ (i + 2) ≤ ‖(x : ℂ_[l])‖ ^ 2 := pow_le_pow_of_le_one hxn hx1 (by omega)
    have hsq : ‖(x : ℂ_[l])‖ ^ 2 ≤ ‖(π : ℂ_[l])‖ * ‖(x : ℂ_[l])‖ := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right hx hxn
    have hpos : 0 ≤ ‖(x : ℂ_[l])‖ ^ (i + 2) := by positivity
    exact (mul_le_of_le_one_left hpos (norm_OC_le_one _)).trans (hp.trans hsq)

theorem exists_not_mem_span (π : OC l) (hπ : ¬ IsUnit π) (F : PowerSeries (OC l))
    (h0 : PowerSeries.constantCoeff F = 0) (h1 : PowerSeries.coeff 1 F = π) (v : ℕ → OC l)
    (hS : ∀ n, HasSum (fun i => ((PowerSeries.coeff i F * v (n + 1) ^ i : OC l) : ℂ_[l])) (v n : ℂ_[l]))
    (hv1 : v 1 ≠ 0) : ∃ n, v n ∉ span {π} := by
  by_contra hcon
  push_neg at hcon
  set a := ‖(π : ℂ_[l])‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb : ∀ n, ‖(v n : ℂ_[l])‖ ≤ a * ‖(v (n + 1) : ℂ_[l])‖ := fun n =>
    norm_le_of_hasSum_small π F h0 h1 _ _ (hS n) ((mem_span_iff_norm _ _).1 (hcon (n + 1)))
  have hk' : ∀ k, ‖(v 1 : ℂ_[l])‖ ≤ a ^ k * ‖(v (k + 1) : ℂ_[l])‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      refine ih.trans ?_
      have := mul_le_mul_of_nonneg_left (hb (k + 1)) (pow_nonneg ha0 k)
      rw [pow_succ, mul_assoc]
      exact this
  have hk : ∀ k, ‖(v 1 : ℂ_[l])‖ ≤ a ^ k := fun k =>
    (hk' k).trans (mul_le_of_le_one_right (pow_nonneg ha0 k) (norm_OC_le_one _))
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one ha0 (norm_lt_one_of_not_isUnit π hπ)
  have h := ge_of_tendsto' hlim hk
  apply hv1
  apply Subtype.ext
  rw [norm_le_zero_iff.1 h]
  rfl

theorem isTiltOf_actT {P : LocPrime l} (AI : LocAinf l P) (g : GQ l) (f : ℕ) (π : OC l) {x : OCb l}
    {v w : ℕ → OC l} (hx : IsTiltOf f π x v) (hw : ∀ n, (w n : ℂ_[l]) = AI.actC g (v n)) :
    IsTiltOf f π (AI.actT g x) w := by
  intro n
  obtain ⟨y, hy, hyv⟩ := hx n
  obtain ⟨y', hy', hc⟩ := AI.actT_coeff g x (f * n) y hy
  refine ⟨y', hc, (mem_span_iff_norm _ _).2 ?_⟩
  have h := (mem_span_iff_norm _ _).1 hyv
  push_cast at h ⊢
  rw [hy', hw, ← map_sub, AI.actC_norm]
  exact h

theorem existsUnique_isTiltOf (f : ℕ) (hf : 0 < f) (π : OC l) (hπ : ¬ IsUnit π)
    (hπl : ((l : ℕ) : OC l) ∈ span {π}) (v : ℕ → OC l)
    (hv : ∀ n, v (n + 1) ^ (l ^ f) - v n ∈ span {π}) : ∃! x : OCb l, IsTiltOf f π x v := by
  obtain ⟨N, hN⟩ := exists_pow_mem_span π hπ
  exact ⟨tiltOf hf hπl N hN v hv, isTiltOf_tiltOf hf hπl N hN v hv,
    fun x' hx' => isTiltOf_unique hf hπl N hN hx' (isTiltOf_tiltOf hf hπl N hN v hv)⟩

end OC

end GlobalTheory.LTTilt

namespace GlobalTheory.LTTilt

open Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem exists_tilt : ∀ (l : ℕ) [Fact l.Prime] (f : ℕ), 0 < f → ∀ (π : OC l), ¬ IsUnit π → ((l : ℕ) : OC l) ∈ span {π} →
    ∀ (F : PowerSeries (OC l)), PowerSeries.constantCoeff F = 0 → PowerSeries.coeff 1 F = π →
      (∀ i, PowerSeries.coeff i (F - PowerSeries.X ^ (l ^ f)) ∈ span {π}) →
    ∀ v : ℕ → OC l,
      (∀ n, HasSum (fun i => ((PowerSeries.coeff i F * v (n + 1) ^ i : OC l) : ℂ_[l])) (v n : ℂ_[l])) →
      v 0 = 0 → v 1 ≠ 0 →
    ∃ x : OCb l, IsTiltOf f π x v ∧ x ≠ 0 ∧ ¬ IsUnit x ∧ (∀ x' : OCb l, IsTiltOf f π x' v → x' = x) ∧
      ∀ (P : LocPrime l) (AI : LocAinf l P) (g : GQ l) (w : ℕ → OC l),
        (∀ n, (w n : ℂ_[l]) = AI.actC g (v n)) → IsTiltOf f π (AI.actT g x) w := by
  intro l _ f hf π hπ hπl F h0 h1 hF v hS hv0 hv1
  have hv : ∀ n, v (n + 1) ^ (l ^ f) - v n ∈ span {π} := fun n =>
    pow_sub_mem_of_hasSum _ π F hF _ _ (hS n)
  obtain ⟨x, hx, hu⟩ := existsUnique_isTiltOf f hf π hπ hπl v hv
  obtain ⟨n, hn⟩ := exists_not_mem_span π hπ F h0 h1 v hS hv1
  refine ⟨x, hx, ne_zero_of_isTiltOf hπl hx n hn, not_isUnit_of_isTiltOf hπl hπ hx ?_, hu,
    fun P AI g w hw => isTiltOf_actT AI g f π hx hw⟩
  rw [hv0]
  exact zero_mem _

end GlobalTheory.LTTilt

namespace GlobalTheory.LTTilt

section Ring

variable {O : Type} [CommRing O] {l : ℕ} [hl : Fact l.Prime] [Fact (¬ IsUnit (l : O))] {f : ℕ} {π : O}

theorem isTiltOf_zero : IsTiltOf f π (0 : PreTilt O l) (fun _ => 0) := fun _ =>
  ⟨0, by rw [map_zero, map_zero], by rw [sub_zero]; exact zero_mem _⟩

theorem isTiltOf_one : IsTiltOf f π (1 : PreTilt O l) (fun _ => 1) := fun _ =>
  ⟨1, by rw [map_one, map_one], by rw [sub_self]; exact zero_mem _⟩

theorem isTiltOf_add {x y : PreTilt O l} {v u : ℕ → O} (hx : IsTiltOf f π x v) (hy : IsTiltOf f π y u) :
    IsTiltOf f π (x + y) (fun n => v n + u n) := by
  intro n
  obtain ⟨a, ha, ha'⟩ := hx n
  obtain ⟨b, hb, hb'⟩ := hy n
  refine ⟨a + b, by rw [map_add, ha, hb, map_add], ?_⟩
  have := (span {π}).add_mem ha' hb'
  convert this using 1
  ring

theorem isTiltOf_neg {x : PreTilt O l} {v : ℕ → O} (hx : IsTiltOf f π x v) :
    IsTiltOf f π (-x) (fun n => -v n) := by
  intro n
  obtain ⟨a, ha, ha'⟩ := hx n
  refine ⟨-a, by rw [map_neg, ha, map_neg], ?_⟩
  have := (span {π}).neg_mem ha'
  convert this using 1
  ring

theorem isTiltOf_sub {x y : PreTilt O l} {v u : ℕ → O} (hx : IsTiltOf f π x v) (hy : IsTiltOf f π y u) :
    IsTiltOf f π (x - y) (fun n => v n - u n) := by
  have := isTiltOf_add hx (isTiltOf_neg hy)
  simpa only [sub_eq_add_neg] using this

theorem isTiltOf_mul {x y : PreTilt O l} {v u : ℕ → O} (hx : IsTiltOf f π x v) (hy : IsTiltOf f π y u) :
    IsTiltOf f π (x * y) (fun n => v n * u n) := by
  intro n
  obtain ⟨a, ha, ha'⟩ := hx n
  obtain ⟨b, hb, hb'⟩ := hy n
  refine ⟨a * b, by rw [map_mul, ha, hb, map_mul], ?_⟩
  have := (span {π}).add_mem ((span {π}).mul_mem_right b ha') ((span {π}).mul_mem_left (v n) hb')
  convert this using 1
  ring

theorem isTiltOf_pow {x : PreTilt O l} {v : ℕ → O} (hx : IsTiltOf f π x v) (k : ℕ) :
    IsTiltOf f π (x ^ k) (fun n => v n ^ k) := by
  induction k with
  | zero => simpa only [pow_zero] using (isTiltOf_one : IsTiltOf f π (1 : PreTilt O l) fun _ => 1)
  | succ k ih => simpa only [pow_succ] using isTiltOf_mul ih hx

theorem isTiltOf_sum {ι : Type} (s : Finset ι) {x : ι → PreTilt O l} {v : ι → ℕ → O}
    (h : ∀ i ∈ s, IsTiltOf f π (x i) (v i)) : IsTiltOf f π (∑ i ∈ s, x i) (fun n => ∑ i ∈ s, v i n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (isTiltOf_zero : IsTiltOf f π (0 : PreTilt O l) fun _ => 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact isTiltOf_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end Ring

section OCb

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime]

theorem sharpRoot_sub_mem {f : ℕ} {π : OC l} (hπl : ((l : ℕ) : OC l) ∈ span {π}) {x : OCb l} {v : ℕ → OC l}
    (hx : IsTiltOf f π x v) (n : ℕ) : GlobalTheory.TiltAlgClosed.sharpRoot (O := OC l) (p := l) x (f * n) - v n ∈ span {π} := by
  obtain ⟨y, hy, hyv⟩ := hx n
  have h1 : GlobalTheory.TiltAlgClosed.sharpRoot (O := OC l) (p := l) x (f * n) - y ∈ span {((l : ℕ) : OC l)} := by
    rw [← Ideal.Quotient.eq, GlobalTheory.TiltAlgClosed.mk_sharpRoot, hy]
  have h2 := span_le.2 (Set.singleton_subset_iff.2 hπl) h1
  have := (span {π}).add_mem h2 hyv
  rwa [sub_add_sub_cancel] at this

theorem norm_le_max_of_sub_mem {a b π : OC l} (h : a - b ∈ span {π}) :
    ‖(a : ℂ_[l])‖ ≤ max ‖(b : ℂ_[l])‖ ‖(π : ℂ_[l])‖ := by
  have h1 := (mem_span_iff_norm π (a - b)).1 h
  have e : (a : ℂ_[l]) = (b : ℂ_[l]) + ((a - b : OC l) : ℂ_[l]) := by push_cast; ring
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max le_rfl h1)

theorem untilt_ne_zero {x : OCb l} (hx : x ≠ 0) : x.untilt ≠ 0 := fun h =>
  hx (zero_dvd_iff.1 (GlobalTheory.TiltAlgClosed.dvd_of_untilt_dvd (by rw [h]; exact dvd_zero _)))

theorem exists_norm_sharpRoot_gt {x : OCb l} (hx : x.untilt ≠ 0) {π : OC l} (hπ : ¬ IsUnit π) {f : ℕ}
    (hf : 0 < f) : ∃ n, ‖(π : ℂ_[l])‖ < ‖(GlobalTheory.TiltAlgClosed.sharpRoot (O := OC l) (p := l) x (f * n) : ℂ_[l])‖ := by
  have hr : 0 < ‖((x.untilt : OC l) : ℂ_[l])‖ := norm_pos_iff.2 fun h => hx (Subtype.ext h)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr (norm_lt_one_of_not_isUnit π hπ)
  refine ⟨n, lt_of_not_ge fun h => ?_⟩
  have e : ‖((x.untilt : OC l) : ℂ_[l])‖ =
      ‖(GlobalTheory.TiltAlgClosed.sharpRoot (O := OC l) (p := l) x (f * n) : ℂ_[l])‖ ^ (l ^ (f * n)) := by
    rw [← norm_pow, ← SubmonoidClass.coe_pow, GlobalTheory.TiltAlgClosed.sharpRoot_pow]
  have h0 := norm_nonneg (π : ℂ_[l])
  have h1 : ‖(π : ℂ_[l])‖ ≤ 1 := norm_OC_le_one π
  have hle : n ≤ l ^ (f * n) :=
    (Nat.le_mul_of_pos_left n hf).trans (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le
  have : ‖((x.untilt : OC l) : ℂ_[l])‖ ≤ ‖(π : ℂ_[l])‖ ^ n := by
    rw [e]
    exact (pow_le_pow_left₀ (norm_nonneg _) h _).trans (pow_le_pow_of_le_one h0 h1 hle)
  linarith

end OCb

end GlobalTheory.LTTilt

namespace GlobalTheory.LTTilt

section Div

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime]

theorem dvd_of_isTiltOf {f : ℕ} (hf : 0 < f) {π : OC l} (hπ : ¬ IsUnit π) (hπl : ((l : ℕ) : OC l) ∈ span {π})
    {y X : OCb l} {d e : ℕ → OC l} (hy : IsTiltOf f π y d) (hX : IsTiltOf f π X e) (hX0 : X.untilt ≠ 0)
    (hde : ∀ n, ‖(d n : ℂ_[l])‖ ≤ ‖(e n : ℂ_[l])‖) : X ∣ y := by
  obtain ⟨n, hn⟩ := exists_norm_sharpRoot_gt hX0 hπ hf
  have he : ‖(e n : ℂ_[l])‖ ≤ ‖(GlobalTheory.TiltAlgClosed.sharpRoot (O := OC l) (p := l) X (f * n) : ℂ_[l])‖ := by
    have h1 := (span {π}).neg_mem (sharpRoot_sub_mem hπl hX n)
    rw [neg_sub] at h1
    exact (norm_le_max_of_sub_mem h1).trans (max_le le_rfl hn.le)
  have hyn : ‖(GlobalTheory.TiltAlgClosed.sharpRoot (O := OC l) (p := l) y (f * n) : ℂ_[l])‖ ≤
      ‖(GlobalTheory.TiltAlgClosed.sharpRoot (O := OC l) (p := l) X (f * n) : ℂ_[l])‖ :=
    (norm_le_max_of_sub_mem (sharpRoot_sub_mem hπl hy n)).trans (max_le ((hde n).trans he) hn.le)
  apply GlobalTheory.TiltAlgClosed.dvd_of_untilt_dvd
  rw [← Ideal.mem_span_singleton, mem_span_iff_norm, ← GlobalTheory.TiltAlgClosed.sharpRoot_pow y (f * n),
    ← GlobalTheory.TiltAlgClosed.sharpRoot_pow X (f * n), SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, norm_pow, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hyn _

theorem isTiltOf_σF {f : ℕ} {π : OC l} {x : OCb l} {v : ℕ → OC l} (hx : IsTiltOf f π x v) (g : GQ l) :
    IsTiltOf f π (Per.σF g x) (fun n => Per.σO g (v n)) := by
  intro n
  obtain ⟨y, hy, hyv⟩ := hx n
  refine ⟨Per.σO g y, ?_, ?_⟩
  · exact GlobalTheory.AdicMaps.coeff_galois l g x (f * n) y hy
  · rw [mem_span_iff_norm] at hyv ⊢
    have e : ((Per.σO g y - Per.σO g (v n) : OC l) : ℂ_[l]) = Per.σC g ((y - v n : OC l) : ℂ_[l]) := by
      rw [← map_sub]
      exact GlobalTheory.RingIface.sigO_coe (l := l) g _
    rw [e, GlobalTheory.RingBasics.norm_σC]
    exact hyv

theorem norm_untilt_lt_one {f : ℕ} {π : OC l} (hπ : ¬ IsUnit π) (hπl : ((l : ℕ) : OC l) ∈ span {π}) {x : OCb l}
    {v : ℕ → OC l} (hx : IsTiltOf f π x v) (h0 : v 0 = 0) : ‖((x.untilt : OC l) : ℂ_[l])‖ < 1 := by
  have h1 := sharpRoot_sub_mem hπl hx 0
  have e := GlobalTheory.TiltAlgClosed.sharpRoot_pow (O := OC l) (p := l) x 0
  rw [mul_zero, h0, sub_zero] at h1
  rw [pow_zero, pow_one] at e
  rw [e, mem_span_iff_norm] at h1
  exact h1.trans_lt (norm_lt_one_of_not_isUnit π hπ)

theorem norm_tail_le (a : ℕ → OC l) (y : OC l) (W : ℂ_[l]) (h : HasSum (fun i => ((a i * y ^ i : OC l) : ℂ_[l])) W)
    (M : ℕ) : ‖W - ((∑ i ∈ Finset.range M, a i * y ^ i : OC l) : ℂ_[l])‖ ≤ ‖(y : ℂ_[l])‖ ^ M := by
  classical
  set t : ℕ → ℂ_[l] := fun i => ((a i * y ^ i : OC l) : ℂ_[l]) with ht
  have h2 : HasSum (fun i => if i ∈ Finset.range M then t i else 0)
      (∑ i ∈ Finset.range M, if i ∈ Finset.range M then t i else 0) :=
    hasSum_sum_of_ne_finset_zero fun i hi => if_neg hi
  rw [Finset.sum_ite_mem, Finset.inter_self] at h2
  have h3 := h.sub h2
  have e : ((∑ i ∈ Finset.range M, a i * y ^ i : OC l) : ℂ_[l]) = ∑ i ∈ Finset.range M, t i := by
    rw [ht]
    push_cast
    rfl
  rw [e]
  refine norm_le_of_hasSum h3 fun i => ?_
  have hy1 : ‖(y : ℂ_[l])‖ ≤ 1 := norm_OC_le_one y
  by_cases hi : i ∈ Finset.range M
  · rw [if_pos hi, sub_self, norm_zero]
    positivity
  · rw [if_neg hi, sub_zero, ht]
    rw [Finset.mem_range, not_lt] at hi
    push_cast
    rw [norm_mul, norm_pow]
    exact (mul_le_of_le_one_left (by positivity) (norm_OC_le_one _)).trans
      (pow_le_pow_of_le_one (norm_nonneg _) hy1 hi)

end Div

end GlobalTheory.LTTilt

namespace GlobalTheory.LTTilt

section LubinTate

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Prism GlobalTheory.AinfK Formalism.BasicNotions.Examples₂.LB
open GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime]

instance finite_residueField_OL (K : FinExt l) : Finite (IsLocalRing.ResidueField ↥(OL K)) := OL_resFinite K

theorem natCast_mem_span_intToOC (K : FinExt l) {π : ↥(OL K)} (hπ : Irreducible π) :
    ((l : ℕ) : OC l) ∈ span {intToOC K π} := by
  have := map_dvd (intToOC K) (GlobalTheory.AinfK.dvd_of_not_isUnit hπ (l_mem_max K))
  rw [map_natCast] at this
  exact Ideal.mem_span_singleton.2 this

theorem not_isUnit_intToOC (K : FinExt l) {π : ↥(OL K)} (hπ : Irreducible π) : ¬ IsUnit (intToOC K π) := by
  intro hu
  obtain ⟨n, hn⟩ := GlobalTheory.AinfK.exists_l_dvd_pow hπ
  have := map_dvd (intToOC K) hn
  rw [map_natCast, map_pow] at this
  exact (Fact.out : ¬ IsUnit ((l : ℕ) : OC l)) (isUnit_of_dvd_unit this (hu.pow _))

theorem isTiltOf_red_inO (K : FinExt l) {π : ↥(OL K)} (hπ : Irreducible π) (c : ↥(OL K)) :
    IsTiltOf (fK K) (intToOC K π) (red K (inO K c)) (fun _ => intToOC K c) := by
  set y := red K (inO K c) with hydef
  have hq : y ^ (l ^ fK K) = y := by rw [hydef, ← red_frobq, frobq_inO]
  have hqn : ∀ n, y ^ (l ^ (fK K * n)) = y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hq]
  intro n
  refine ⟨y.untilt, ?_, ?_⟩
  · have h1 := coeff_eq_pow y 0 (fK K * n)
    rw [zero_add, ← map_pow, hqn] at h1
    rw [← h1, PreTilt.mk_untilt_eq_coeff_zero]
  · obtain ⟨d, hd⟩ := GlobalTheory.AinfK.dvd_thetaK_sub hπ (inO K c)
    rw [thetaK_inO, ← hydef] at hd
    rw [mem_span_singleton']
    exact ⟨-d, by linear_combination hd⟩

theorem isTiltOf_eval (K : FinExt l) {π : ↥(OL K)} (hπ : Irreducible π) {x : OCb l} {v : ℕ → OC l}
    (hx : IsTiltOf (fK K) (intToOC K π) x v) (hx0 : x ≠ 0) (G : PowerSeries ↥(OL K)) {w : ℕ → OC l} {z : OCb l}
    (hw : ∀ n, HasSum (fun i => ((intToOC K (PowerSeries.coeff i G) * v n ^ i : OC l) : ℂ_[l])) (w n : ℂ_[l]))
    (hz : IsTiltOf (fK K) (intToOC K π) z w) (M : ℕ) :
    z - ∑ i ∈ Finset.range M, red K (inO K (PowerSeries.coeff i G)) * x ^ i ∈ span {x ^ M} := by
  have hS : IsTiltOf (fK K) (intToOC K π) (∑ i ∈ Finset.range M, red K (inO K (PowerSeries.coeff i G)) * x ^ i)
      (fun n => ∑ i ∈ Finset.range M, intToOC K (PowerSeries.coeff i G) * v n ^ i) :=
    isTiltOf_sum (v := fun i n => intToOC K (PowerSeries.coeff i G) * v n ^ i) _
      fun i _ => isTiltOf_mul (isTiltOf_red_inO K hπ _) (isTiltOf_pow hx i)
  have hD := isTiltOf_sub hz hS
  have hx0' : (x ^ M).untilt ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero M (untilt_ne_zero hx0)
  rw [Ideal.mem_span_singleton]
  refine dvd_of_isTiltOf (Nat.pos_of_ne_zero (NeZero.ne (fK K))) (not_isUnit_intToOC K hπ)
    (natCast_mem_span_intToOC K hπ) hD (isTiltOf_pow hx M) hx0' fun n => ?_
  have := norm_tail_le (fun i => intToOC K (PowerSeries.coeff i G)) (v n) (w n) (hw n) M
  push_cast at this ⊢
  rw [norm_pow]
  exact this

end LubinTate

end GlobalTheory.LTTilt

namespace GlobalTheory.LTTilt

section Compat

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Prism GlobalTheory.AinfK Formalism.BasicNotions.Examples₂.LB IsLocalRing
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime]

theorem pow_card_sub_mem (K : FinExt l) {π : ↥(OL K)} (hπ : Irreducible π) (c : ↥(OL K)) :
    intToOC K c ^ (l ^ fK K) - intToOC K c ∈ span {intToOC K π} := by
  have h := res_pow (card_res K) (residue _ c)
  rw [← map_pow, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff] at h
  obtain ⟨d, hd⟩ := GlobalTheory.AinfK.dvd_of_not_isUnit hπ h
  rw [Ideal.mem_span_singleton]
  exact ⟨intToOC K d, by rw [← map_pow, ← map_sub, hd, map_mul]⟩

theorem eval_compat (K : FinExt l) {π : ↥(OL K)} (hπ : Irreducible π) {v : ℕ → OC l}
    (hv : ∀ n, v (n + 1) ^ (l ^ fK K) - v n ∈ span {intToOC K π}) (hv1 : ∀ n, ‖(v n : ℂ_[l])‖ < 1)
    (G : PowerSeries ↥(OL K)) {w : ℕ → OC l}
    (hw : ∀ n, HasSum (fun i => ((intToOC K (PowerSeries.coeff i G) * v n ^ i : OC l) : ℂ_[l])) (w n : ℂ_[l]))
    (n : ℕ) : w (n + 1) ^ (l ^ fK K) - w n ∈ span {intToOC K π} := by
  set P := intToOC K π with hP
  have hP0 : 0 < ‖(P : ℂ_[l])‖ := by
    rw [norm_pos_iff]
    intro h
    have := (mem_span_iff_norm P _).1 (natCast_mem_span_intToOC K hπ)
    rw [h, norm_zero] at this
    push_cast at this
    exact (norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero : ((l : ℕ) : ℂ_[l]) ≠ 0)).not_ge this
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hP0 (max_lt (hv1 n) (hv1 (n + 1)))
  have tail : ∀ m, ‖(v m : ℂ_[l])‖ ≤ max ‖(v n : ℂ_[l])‖ ‖(v (n + 1) : ℂ_[l])‖ →
      Ideal.Quotient.mk (span {P}) (w m) =
        ∑ i ∈ Finset.range M, Ideal.Quotient.mk (span {P}) (intToOC K (PowerSeries.coeff i G)) *
          Ideal.Quotient.mk (span {P}) (v m) ^ i := by
    intro m hm
    simp only [← map_pow, ← map_mul, ← map_sum]
    rw [Ideal.Quotient.eq, mem_span_iff_norm]
    have := norm_tail_le (fun i => intToOC K (PowerSeries.coeff i G)) (v m) (w m) (hw m) M
    push_cast at this ⊢
    exact this.trans ((pow_le_pow_left₀ (norm_nonneg _) hm M).trans hM.le)
  have hR : Nontrivial (OC l ⧸ span {P}) :=
    Ideal.Quotient.nontrivial_iff.2 (by rw [Ne, Ideal.span_singleton_eq_top]; exact not_isUnit_intToOC K hπ)
  have hlR : ((l : ℕ) : OC l ⧸ span {P}) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (span {P})), Ideal.Quotient.eq_zero_iff_mem]
    exact natCast_mem_span_intToOC K hπ
  haveI : CharP (OC l ⧸ span {P}) l := (CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)).2 hlR
  have hvq : Ideal.Quotient.mk (span {P}) (v (n + 1)) ^ (l ^ fK K) = Ideal.Quotient.mk (span {P}) (v n) := by
    rw [← map_pow]
    exact Ideal.Quotient.eq.2 (hv n)
  have haq : ∀ c : ↥(OL K), Ideal.Quotient.mk (span {P}) (intToOC K c) ^ (l ^ fK K) =
      Ideal.Quotient.mk (span {P}) (intToOC K c) := fun c => by
    rw [← map_pow]
    exact Ideal.Quotient.eq.2 (pow_card_sub_mem K hπ c)
  rw [← Ideal.Quotient.eq, map_pow, tail (n + 1) (le_max_right _ _), tail n (le_max_left _ _),
    sum_pow_char_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow, haq, ← pow_mul, mul_comm i, pow_mul, hvq]

theorem norm_lt_one_of_compat (K : FinExt l) {π : ↥(OL K)} (hπ : Irreducible π) {v : ℕ → OC l}
    (hv : ∀ n, v (n + 1) ^ (l ^ fK K) - v n ∈ span {intToOC K π}) (h0 : v 0 = 0) (n : ℕ) :
    ‖(v n : ℂ_[l])‖ < 1 := by
  have hπ1 := norm_lt_one_of_not_isUnit _ (not_isUnit_intToOC K hπ)
  induction n with
  | zero => rw [h0]; simp
  | succ n ih =>
    have h := (norm_le_max_of_sub_mem (hv n)).trans_lt (max_lt ih hπ1)
    push_cast at h
    rw [norm_pow] at h
    exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)).1 h

end Compat

end GlobalTheory.LTTilt

namespace GlobalTheory.LTTilt

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Prism GlobalTheory.AinfK Formalism.BasicNotions.Examples₂.LB
open GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)) (hπ : Irreducible π)
    (F : PowerSeries ↥(OL K)) (hF : IsLubinTateSeries π F) (v : ℕ → OC l),
    (∀ n, HasSum (fun i => ((intToOC K (PowerSeries.coeff i F) * v (n + 1) ^ i : OC l) : ℂ_[l])) (v n : ℂ_[l])) →
    v 0 = 0 → v 1 ≠ 0 →
    ∃ x : OCb l, IsTiltOf (fK K) (intToOC K π) x v ∧ x ≠ 0 ∧ ‖((x.untilt : OC l) : ℂ_[l])‖ < 1 ∧ ¬ IsUnit x ∧
      (∀ x' : OCb l, IsTiltOf (fK K) (intToOC K π) x' v → x' = x) ∧
      (∀ (G : PowerSeries ↥(OL K)) (w : ℕ → OC l),
        (∀ n, HasSum (fun i => ((intToOC K (PowerSeries.coeff i G) * v n ^ i : OC l) : ℂ_[l])) (w n : ℂ_[l])) →
        ∃ z : OCb l, IsTiltOf (fK K) (intToOC K π) z w ∧ (∀ z' : OCb l, IsTiltOf (fK K) (intToOC K π) z' w → z' = z) ∧
          ∀ M : ℕ, z - ∑ i ∈ Finset.range M, red K (inO K (PowerSeries.coeff i G)) * x ^ i ∈ span {x ^ M}) ∧
      ∀ (g : ↥(GK K)) (u : ↥(OL K)),
        (∀ n, HasSum (fun i => ((intToOC K (PowerSeries.coeff i (lubinTateHom hπ hF hF u).toPowerSeries) *
          v n ^ i : OC l) : ℂ_[l])) ((Per.σO (g : GQ l) (v n) : OC l) : ℂ_[l])) →
        ∀ M : ℕ, Per.σF (g : GQ l) x - ∑ i ∈ Finset.range M,
          red K (inO K (PowerSeries.coeff i (lubinTateHom hπ hF hF u).toPowerSeries)) * x ^ i ∈ span {x ^ M} := by
  intro l _ K π hπ F hF v hS hv0 hv1
  set F' := PowerSeries.map (intToOC K) F with hF'
  have h0 : PowerSeries.constantCoeff F' = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hF', PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hF.constantCoeff_eq_zero, map_zero]
  have h1 : PowerSeries.coeff 1 F' = intToOC K π := by rw [hF', PowerSeries.coeff_map, hF.coeff_one]
  have hq : ∀ i, PowerSeries.coeff i (F' - PowerSeries.X ^ (l ^ fK K)) ∈ span {intToOC K π} := by
    intro i
    have h := hF.dvd_coeff_sub i
    rw [card_res] at h
    have := map_dvd (intToOC K) h
    rw [← PowerSeries.coeff_map, map_sub, map_pow, PowerSeries.map_X] at this
    exact Ideal.mem_span_singleton.2 this
  have hS' : ∀ n, HasSum (fun i => ((PowerSeries.coeff i F' * v (n + 1) ^ i : OC l) : ℂ_[l])) (v n : ℂ_[l]) := by
    intro n
    simpa only [hF', PowerSeries.coeff_map] using hS n
  have hπu := not_isUnit_intToOC K hπ
  have hfpos : 0 < fK K := Nat.pos_of_ne_zero (NeZero.ne (fK K))
  have hπl := natCast_mem_span_intToOC K hπ
  obtain ⟨x, hx, hx0, hxu, huniq, -⟩ := exists_tilt l (fK K) hfpos (intToOC K π)
    hπu hπl F' h0 h1 hq v hS' hv0 hv1
  refine ⟨x, hx, hx0, norm_untilt_lt_one hπu hπl hx hv0, hxu, huniq,
    fun G w hw => ?_,
    fun g u hg M => isTiltOf_eval K hπ hx hx0 _ hg (isTiltOf_σF hx (g : GQ l)) M⟩
  have hv : ∀ n, v (n + 1) ^ (l ^ fK K) - v n ∈ span {intToOC K π} := fun n =>
    pow_sub_mem_of_hasSum _ _ F' hq _ _ (hS' n)
  obtain ⟨z, hz, hzu⟩ := existsUnique_isTiltOf (fK K) hfpos (intToOC K π) hπu hπl w
    (eval_compat K hπ hv (norm_lt_one_of_compat K hπ hv hv0) G hw)
  exact ⟨z, hz, hzu, isTiltOf_eval K hπ hx hx0 G hw hz⟩

end GlobalTheory.LTTilt
