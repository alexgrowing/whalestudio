import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.SingleLetterBiextensionRelation
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.UnimodularGram.Orthonormal

open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (OwOK TrDual)
open Formalism.InvariantFactorPaths.G7 (UnrOK)

namespace UpperTheory.NormSurjectiveFixedIntegers

variable {K : Type} [NormedField K] [IsUltrametricDist K]

private lemma nadd {a b : K} {r : ℝ} (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) : ‖a + b‖ ≤ r :=
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)

private lemma naddlt {a b : K} {r : ℝ} (ha : ‖a‖ < r) (hb : ‖b‖ < r) : ‖a + b‖ < r :=
  (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)

private lemma norm_one_of_close {a b : K} (hb : ‖b‖ = 1) (h : ‖a - b‖ < 1) : ‖a‖ = 1 := by
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := a - b) (y := b)
    (by rw [hb]; exact h.ne)
  rw [sub_add_cancel, hb, max_eq_right h.le] at this
  exact this

private lemma sqrt_near [CompleteSpace K] (h2 : ‖(2 : K)‖ = 1) (w : K) (hw : ‖w‖ < 1) :
    ∃ t : K, ‖t‖ < 1 ∧ t ^ 2 + 2 * t = w := by
  have h20 : (2 : K) ≠ 0 := by
    intro h
    rw [h, norm_zero] at h2
    exact zero_ne_one h2
  let f : K → K := fun t => (w - t ^ 2) / 2
  let s : Set K := Metric.closedBall 0 ‖w‖
  have hs : IsComplete s := Metric.isClosed_closedBall.isComplete
  have hmem : ∀ t, t ∈ s ↔ ‖t‖ ≤ ‖w‖ := fun t => mem_closedBall_zero_iff
  have hmaps : Set.MapsTo f s s := by
    intro t ht
    rw [hmem] at ht ⊢
    show ‖(w - t ^ 2) / 2‖ ≤ _
    rw [norm_div, h2, div_one, sub_eq_add_neg]
    refine nadd le_rfl ?_
    rw [norm_neg, norm_pow]
    nlinarith [norm_nonneg t]
  have hc : ContractingWith ‖w‖₊ (hmaps.restrict f s s) := by
    refine ⟨by exact_mod_cast hw, LipschitzWith.of_dist_le_mul ?_⟩
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    rw [hmem] at ha hb
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    show ‖(w - a ^ 2) / 2 - (w - b ^ 2) / 2‖ ≤ ‖w‖ * ‖a - b‖
    have : (w - a ^ 2) / 2 - (w - b ^ 2) / 2 = -((a + b) * (a - b)) / 2 := by ring
    rw [this, norm_div, h2, div_one, norm_neg, norm_mul]
    exact mul_le_mul_of_nonneg_right (nadd ha hb) (norm_nonneg _)
  obtain ⟨t, ht, hfix, -⟩ := ContractingWith.exists_fixedPoint' hs hmaps hc
    (x := 0) ((hmem 0).2 (by simp)) (edist_ne_top _ _)
  refine ⟨t, ((hmem t).1 ht).trans_lt hw, ?_⟩
  have : (w - t ^ 2) / 2 = t := hfix
  field_simp at this
  linear_combination -this

variable {l : ℕ} {σ : K →+* K}

private lemma linv_lt (hU : UnrOK K l σ) : (l : ℝ)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ (by exact_mod_cast hU.1.one_lt)

private lemma sig_close (hU : UnrOK K l σ) {a : K} (ha : ‖a‖ ≤ 1) : ‖σ a - a ^ l‖ < 1 :=
  (hU.2.2.2.2 a ha).trans_lt (linv_lt hU)

private lemma sig_le (hU : UnrOK K l σ) {a : K} (ha : ‖a‖ ≤ 1) : ‖σ a‖ ≤ 1 := by
  have := nadd (sig_close hU ha).le (show ‖a ^ l‖ ≤ 1 by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha)
  rwa [sub_add_cancel] at this

private lemma sig_lt (hU : UnrOK K l σ) {a : K} (ha : ‖a‖ < 1) : ‖σ a‖ < 1 := by
  have := naddlt (sig_close hU ha.le)
    (show ‖a ^ l‖ < 1 by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) ha hU.1.ne_zero)
  rwa [sub_add_cancel] at this

private lemma sig_iter_le (hU : UnrOK K l σ) (n : ℕ) {a : K} (ha : ‖a‖ ≤ 1) : ‖σ^[n] a‖ ≤ 1 := by
  induction n with
  | zero => exact ha
  | succ n ih => rw [Function.iterate_succ_apply']; exact sig_le hU ih

private lemma norm_two (hU : UnrOK K l σ) : ‖(2 : K)‖ = 1 := by
  have := Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd (K := K) hU.1
    (by rw [hU.2.2.1]; exact linv_lt hU) (m := 2)
    (fun h => absurd (Nat.le_of_dvd two_pos h) (not_le.2 hU.2.1))
  exact_mod_cast this

private lemma norm_onto [CompleteSpace K] [CharZero K] (hU : UnrOK K l σ) (ζ : K)
    (hζ : IsPrimitiveRoot ζ (l ^ 2 - 1)) (u : K) (hu : ‖u‖ = 1) (hs : σ u = u) :
    ∃ a : K, ‖a‖ ≤ 1 ∧ σ (σ a) = a ∧ a * σ a = u := by
  have hl := hU.2.1
  have hσζ : σ ζ = ζ ^ l := Formalism.L2.Th1.D.teichSigma K l 2 σ hU (by omega) ζ hζ.pow_eq_one
  have hfac : l ^ 2 - 1 = (l + 1) * (l - 1) := by
    have := Nat.sq_sub_sq l 1
    simpa using this
  have hN0 : 0 < l ^ 2 - 1 := by rw [hfac]; exact Nat.mul_pos (by omega) (by omega)
  have nζ : ‖ζ‖ = 1 := Formalism.L2.Th1.D.FormalExponential.norm_eq_one_of_pow hN0.ne' hζ.pow_eq_one
  have hη : IsPrimitiveRoot (ζ ^ (l + 1)) (l - 1) := hζ.pow hN0 hfac
  have h1 : ‖u ^ (l - 1) - 1‖ < 1 := by
    have h := sig_close hU hu.le
    have e : σ u - u ^ l = -(u * (u ^ (l - 1) - 1)) := by
      rw [hs, mul_sub, ← pow_succ', Nat.sub_add_cancel (by omega)]; ring
    rwa [e, norm_neg, norm_mul, hu, one_mul] at h
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ‖u - (ζ ^ (l + 1)) ^ k‖ < 1 := by
    by_contra hcon
    push Not at hcon
    have hp := congrArg (Polynomial.eval u) (X_pow_sub_C_eq_prod hη (α := 1) (a := 1) (by omega) (one_pow _))
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_prod, mul_one] at hp
    rw [hp, norm_prod] at h1
    exact absurd h1 (not_lt.2 (Finset.prod_induction _ (fun y : ℝ => 1 ≤ y) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl fun j _ => hcon j))
  set x : K := ζ ^ k with hx
  have hxx : x * σ x = (ζ ^ (l + 1)) ^ k := by
    rw [hx, map_pow, hσζ, ← mul_pow, ← pow_succ']
  have hx2 : σ (σ x) = x := by
    rw [hx, map_pow, map_pow, hσζ, map_pow, hσζ, ← pow_mul ζ l l, ← sq,
      show l ^ 2 = (l ^ 2 - 1) + 1 by omega, pow_succ, hζ.pow_eq_one, one_mul]
  have nx : ‖x‖ = 1 := by rw [hx, norm_pow, nζ, one_pow]
  rw [← hxx] at hk
  set n : K := x * σ x with hn
  have nn : ‖n‖ = 1 := by rw [hxx, norm_pow, norm_pow, nζ, one_pow, one_pow]
  have hn0 : n ≠ 0 := by
    intro h
    rw [h, norm_zero] at nn
    exact zero_ne_one nn
  have hsn : σ n = n := by rw [hn, map_mul, hx2, mul_comm]
  obtain ⟨t, ht, htw⟩ := sqrt_near (norm_two hU) ((u - n) / n) (by rwa [norm_div, nn, div_one])
  have htw' : σ t ^ 2 + 2 * σ t = (u - n) / n := by
    have := congrArg σ htw
    rwa [map_add, map_pow, map_mul, map_ofNat, map_div₀, map_sub, hs, hsn] at this
  have hst : σ t = t := by
    have e : (σ t - t) * (σ t + t + 2) = 0 := by linear_combination htw' - htw
    have h3 : ‖σ t + t + 2‖ = 1 := norm_one_of_close (norm_two hU)
      (by rw [add_sub_cancel_right]; exact naddlt (sig_lt hU ht) ht)
    rcases mul_eq_zero.1 e with h | h
    · exact sub_eq_zero.1 h
    · rw [h, norm_zero] at h3
      exact absurd h3 zero_ne_one
  refine ⟨x * (1 + t), ?_, ?_, ?_⟩
  · rw [norm_mul, nx, one_mul]
    exact nadd norm_one.le ht.le
  · simp only [map_mul, map_add, map_one, hst, hx2]
  · simp only [map_mul, map_add, map_one, hst]
    have : (t ^ 2 + 2 * t) * n = u - n := by rw [htw]; field_simp
    linear_combination this + (1 + t) ^ 2 * hn

private def intFix (hU : UnrOK K l σ) : Subring K where
  carrier := {x | ‖x‖ ≤ 1 ∧ σ (σ x) = x}
  mul_mem' := fun {a b} ha hb => ⟨by
    rw [norm_mul]; exact mul_le_one₀ ha.1 (norm_nonneg _) hb.1, by
    rw [map_mul, map_mul, ha.2, hb.2]⟩
  one_mem' := ⟨norm_one.le, by rw [map_one, map_one]⟩
  add_mem' := fun {a b} ha hb => ⟨nadd ha.1 hb.1, by rw [map_add, map_add, ha.2, hb.2]⟩
  zero_mem' := ⟨by simp, by rw [map_zero, map_zero]⟩
  neg_mem' := fun {a} ha => ⟨by rw [norm_neg]; exact ha.1, by rw [map_neg, map_neg, ha.2]⟩

private lemma unit_of_norm (hU : UnrOK K l σ) (a : intFix hU) (ha : ‖(a : K)‖ = 1) : IsUnit a := by
  have h0 : (a : K) ≠ 0 := by
    intro h
    rw [h, norm_zero] at ha
    exact zero_ne_one ha
  refine IsUnit.of_mul_eq_one ⟨(a : K)⁻¹, by rw [norm_inv, ha, inv_one], by
    rw [map_inv₀, map_inv₀, a.2.2]⟩ (Subtype.ext ?_)
  exact mul_inv_cancel₀ h0

private lemma norm_of_unit (hU : UnrOK K l σ) (a : intFix hU) (ha : IsUnit a) : ‖(a : K)‖ = 1 := by
  obtain ⟨b, hb⟩ := ha.exists_right_inv
  have h : ‖(a : K)‖ * ‖(b : K)‖ = 1 := by
    rw [← norm_mul, ← Subring.coe_mul, hb, Subring.coe_one, norm_one]
  refine le_antisymm a.2.1 ?_
  nlinarith [b.2.1, norm_nonneg (a : K)]

private lemma congr_one [CompleteSpace K] [CharZero K] (hU : UnrOK K l σ) (ζ : K)
    (hζ : IsPrimitiveRoot ζ (l ^ 2 - 1)) {n : Type} [Fintype n] [DecidableEq n]
    (H G : Matrix n n K) (hH : ∀ i j, ‖H i j‖ ≤ 1 ∧ σ (σ (H i j)) = H i j)
    (hG : ∀ i j, ‖G i j‖ ≤ 1 ∧ σ (σ (G i j)) = G i j) (hh : ∀ i j, σ (H j i) = H i j)
    (hHG : H * G = 1) :
    ∃ P : Matrix n n K, (∀ i j, ‖P i j‖ ≤ 1 ∧ σ (σ (P i j)) = P i j) ∧
      ∀ r r', ∑ k, (∑ j, P r j * H j k) * σ (P r' k) = if r = r' then 1 else 0 := by
  letI : StarRing (intFix hU) :=
    { star := fun a => ⟨σ a, sig_le hU a.2.1, by rw [a.2.2]⟩
      star_involutive := fun a => Subtype.ext a.2.2
      star_mul := fun a b => Subtype.ext (by
        show σ ((a : K) * b) = σ b * σ a
        rw [map_mul, mul_comm])
      star_add := fun a b => Subtype.ext (map_add σ (a : K) b) }
  have hst : ∀ a : intFix hU, ((star a : intFix hU) : K) = σ a := fun a => rfl
  haveI : IsLocalRing (intFix hU) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    rcases a.2.1.lt_or_eq with h | h
    · refine Or.inr (unit_of_norm hU _ (norm_one_of_close norm_one ?_))
      simpa using h
    · exact Or.inl (unit_of_norm hU _ h)
  have hD : KStar.Cstarloc.UnramDatum (intFix hU) := by
    constructor
    · refine ⟨⟨(2 : K)⁻¹, by rw [norm_inv, norm_two hU, inv_one], by simp only [map_inv₀, map_ofNat]⟩,
        Subtype.ext ?_⟩
      show (2 : K)⁻¹ + σ (2 : K)⁻¹ = 1
      rw [map_inv₀, map_ofNat]
      norm_num
    · intro u hu hs
      obtain ⟨a, h1, h2, h3⟩ := norm_onto hU ζ hζ u (norm_of_unit hU u hu)
        (congrArg Subtype.val hs)
      exact ⟨⟨a, h1, h2⟩, Subtype.ext h3⟩
  let H' : Matrix n n (intFix hU) := Matrix.of fun i j => ⟨H i j, hH i j⟩
  let G' : Matrix n n (intFix hU) := Matrix.of fun i j => ⟨G i j, hG i j⟩
  have hHG' : H' * G' = 1 := by
    ext i j
    have := congrFun (congrFun hHG i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [Matrix.mul_apply, Matrix.one_apply, AddSubmonoidClass.coe_finset_sum]
    refine this.trans ?_
    split_ifs <;> rfl
  obtain ⟨P, -, hP⟩ := KStar.Cstarloc.exists_congr_one hD H'
    (by ext i j; exact hh i j) (Matrix.isUnit_det_of_right_inverse hHG')
  refine ⟨Matrix.of fun i j => (P i j : K), fun i j => (P i j).2, fun r r' => ?_⟩
  have := congrArg (intFix hU).subtype (congrFun (congrFun hP r) r')
  simp only [Matrix.mul_apply, Matrix.one_apply, map_sum, map_mul, Matrix.conjTranspose_apply,
    Subring.coe_subtype, hst] at this
  refine this.trans ?_
  split_ifs <;> rfl

private def tr (σ : K →+* K) (i : ℕ) (x : K) : K := ∑ k ∈ Finset.range i, (σ ^ (2 * k)) x

omit [IsUltrametricDist K] in
private lemma pp (a b : ℕ) (x : K) : (σ ^ a) ((σ ^ b) x) = (σ ^ (a + b)) x := by
  rw [pow_add]; rfl

omit [IsUltrametricDist K] in
private lemma tr_shift (i : ℕ) (x : K) (hx : (σ ^ (2 * i)) x = x) : tr σ i ((σ ^ 2) x) = tr σ i x := by
  have h1 := Finset.sum_range_succ (fun k => (σ ^ (2 * k)) x) i
  have h2 := Finset.sum_range_succ' (fun k => (σ ^ (2 * k)) x) i
  simp only [mul_zero, pow_zero, RingHom.coe_one, id] at h2
  rw [h1, hx] at h2
  unfold tr
  simp only [pp]
  exact (add_right_cancel h2).symm

omit [IsUltrametricDist K] in
private lemma tr_map (i m : ℕ) (x : K) : (σ ^ m) (tr σ i x) = tr σ i ((σ ^ m) x) := by
  unfold tr
  simp only [map_sum, pp, add_comm]

omit [IsUltrametricDist K] in
private lemma tr_shift' (i : ℕ) (x : K) (hx : (σ ^ (2 * i)) x = x) (j : ℕ) :
    tr σ i ((σ ^ (2 * j)) x) = tr σ i x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [mul_add, add_comm, mul_one, ← pp, tr_shift, ih]
    rw [pp, add_comm, ← pp, hx]

omit [IsUltrametricDist K] in
private lemma fix_even {c : K} (hc : σ (σ c) = c) (k : ℕ) : (σ ^ (2 * k)) c = c := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [mul_add, ← pp]
    exact (congrArg _ hc).trans ih

omit [IsUltrametricDist K] in
private lemma tr_eq (i : ℕ) [NeZero i] (x : K) :
    (∑ s : ZMod (2 * i), if s.val % 2 = 0 then σ^[s.val] x else 0) = tr σ i x := by
  rw [Formalism.L2.Th1.D.TraceDualSums.sum_zmod (2 * i) (fun k => if k % 2 = 0 then σ^[k] x else 0),
    Formalism.L2.Th1.D.TraceDualSums.sum_range_even i (fun k => σ^[k] x)]
  simp only [tr, RingHom.coe_pow]

private lemma tr_mem (hU : UnrOK K l σ) (i : ℕ) (x : K) (hn : ‖x‖ ≤ 1)
    (hx : (σ ^ (2 * i)) x = x) : ‖tr σ i x‖ ≤ 1 ∧ σ (σ (tr σ i x)) = tr σ i x := by
  refine ⟨IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_, ?_⟩
  · rw [RingHom.coe_pow]; exact sig_iter_le hU _ hn
  · show (σ ^ 2) (tr σ i x) = _
    rw [tr_map, tr_shift i x hx]

private lemma main [CompleteSpace K] [CharZero K] (hU : UnrOK K l σ) (ζ : K)
    (hζ : IsPrimitiveRoot ζ (l ^ 2 - 1)) (i : ℕ) [NeZero i] (hi : Odd i) (om oms : Fin i → K)
    (h1 : OwOK (2 * i) σ om oms) (h2 : TrDual (2 * i) σ om oms) :
    ∃ om : Fin i → K, OwOK (2 * i) σ om (fun r => σ^[i] (om r)) ∧
      TrDual (2 * i) σ om (fun r => σ^[i] (om r)) := by
  obtain ⟨hn, hf⟩ := h1
  have hd := h2.2
  simp only [tr_eq] at hd
  simp only [← RingHom.coe_pow] at hf
  obtain ⟨j, hj⟩ := hi
  have hle : ∀ {a : K}, ‖a‖ ≤ 1 → ‖(σ ^ i) a‖ ≤ 1 := fun ha => by
    rw [RingHom.coe_pow]; exact sig_iter_le hU _ ha
  have hfi : ∀ {a : K}, (σ ^ (2 * i)) a = a → (σ ^ (2 * i)) ((σ ^ i) a) = (σ ^ i) a := fun ha => by
    rw [pp, add_comm, ← pp, ha]
  have hmul : ∀ {a b : K}, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖a * b‖ ≤ 1 := fun ha hb => by
    rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb
  let V : Matrix (Fin i) (Fin i) K := Matrix.of fun k r => (σ ^ (2 * k.val)) (om r)
  let Q : Matrix (Fin i) (Fin i) K := Matrix.of fun r k => (σ ^ (2 * k.val)) (oms r)
  have hQV : Q * V = 1 := by
    ext r r'
    rw [Matrix.mul_apply, Matrix.one_apply]
    have := hd r' r
    rw [tr, Finset.sum_range] at this
    simp only [map_mul] at this
    simp only [V, Q, Matrix.of_apply, mul_comm ((σ ^ _) (oms r)), this, eq_comm]
  have hVQ : V * Q = 1 := mul_eq_one_comm.1 hQV
  let H : Matrix (Fin i) (Fin i) K := Matrix.of fun r r' => tr σ i (om r * (σ ^ i) (om r'))
  let G : Matrix (Fin i) (Fin i) K := Matrix.of fun r r' => tr σ i ((σ ^ i) (oms r) * oms r')
  have eH : H = V.transpose * V.map (σ ^ i) := by
    ext r r'
    simp only [H, V, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.map_apply,
      tr, Finset.sum_range, map_mul, pp, add_comm]
  have eG : G = Q.map (σ ^ i) * Q.transpose := by
    ext r r'
    simp only [G, Q, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.map_apply,
      tr, Finset.sum_range, map_mul, pp, add_comm]
  have hHG : H * G = 1 := by
    rw [eH, eG, Matrix.mul_assoc, ← Matrix.mul_assoc (V.map _), ← Matrix.map_mul, hVQ,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, ← Matrix.transpose_mul, hQV,
      Matrix.transpose_one]
  have hh : ∀ r r', σ (H r' r) = H r r' := by
    intro r r'
    show (σ ^ 1) (tr σ i (om r' * (σ ^ i) (om r))) = tr σ i (om r * (σ ^ i) (om r'))
    rw [tr_map, ← tr_shift' i _ _ j]
    · rw [map_mul, map_mul, pp, pp, pp, ← hj, show i + i = 2 * i by ring, (hf r).1, mul_comm]
    · rw [pp, add_comm, ← pp, map_mul (σ ^ (2 * i)), (hf r').1, hfi (hf r).1]
  obtain ⟨P, hP, hPH⟩ := congr_one hU ζ hζ H G
    (fun r r' => tr_mem hU i _ (hmul (hn r).1 (hle (hn r').1))
      (by rw [map_mul, (hf r).1, hfi (hf r').1]))
    (fun r r' => tr_mem hU i _ (hmul (hle (hn r).2) (hn r').2)
      (by rw [map_mul, (hf r').2, hfi (hf r).2])) hh hHG
  have n1 : ∀ r, ‖∑ a, P r a * om a‖ ≤ 1 := fun r =>
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun a _ =>
      hmul (hP r a).1 (hn a).1
  have f1 : ∀ r, (σ ^ (2 * i)) (∑ a, P r a * om a) = ∑ a, P r a * om a := fun r => by
    simp only [map_sum, map_mul, fix_even (hP _ _).2, (hf _).1]
  have hPi : ∀ r a, (σ ^ i) (P r a) = σ (P r a) := fun r a => by
    rw [hj, add_comm, ← pp, fix_even (hP _ _).2, pow_one]
  have hPs : ∀ r a k, (σ ^ (2 * k)) (σ (P r a)) = σ (P r a) := fun r a k =>
    fix_even (by rw [(hP r a).2]) k
  refine ⟨fun r => ∑ a, P r a * om a, ⟨fun r => ⟨n1 r, sig_iter_le hU _ (n1 r)⟩, fun r => ?_⟩,
    by rw [Fintype.card_fin], fun r r' => ?_⟩
  · simp only [← RingHom.coe_pow]
    exact ⟨f1 r, hfi (f1 r)⟩
  · rw [tr_eq, ← hPH r r', ← RingHom.coe_pow]
    simp only [H, Matrix.of_apply, tr, map_sum, map_mul, hPi, hPs, fix_even (hP _ _).2,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
    ring

private lemma not_dvd {l d : ℕ} (hp : l.Prime) (hd : d ≠ 0) : 0 < l ^ d - 1 ∧ ¬ l ∣ l ^ d - 1 := by
  have h0 : 1 < l ^ d := Nat.one_lt_pow hd hp.one_lt
  refine ⟨by omega, fun h => ?_⟩
  have h2 := Nat.dvd_sub (dvd_pow_self l hd) h
  rw [Nat.sub_sub_self h0.le] at h2
  exact hp.one_lt.ne' (Nat.dvd_one.1 h2)

end UpperTheory.NormSurjectiveFixedIntegers

theorem UpperTheory.exists_unit_quotient_of_normOne_unramified_ultrametric :
    ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ → ∀ (i : ℕ) [NeZero i], Odd i →
    ∃ om : Fin i → MaximalUnramifiedExtension l, OwOK (2 * i) σ om (fun r => σ^[i] (om r)) ∧ TrDual (2 * i) σ om (fun r => σ^[i] (om r)) := by
  intro l _ _ σ hU i _ hi
  haveI : CompleteSpace (MaximalUnramifiedExtension l) := Formalism.L2.Th1.D.kurComplete l
  have a1 := UpperTheory.NormSurjectiveFixedIntegers.not_dvd (d := 2) hU.1 two_ne_zero
  have a2 := UpperTheory.NormSurjectiveFixedIntegers.not_dvd (d := 2 * i) hU.1 (NeZero.ne _)
  obtain ⟨ζ, hζ⟩ := Formalism.L2.Th1.D.kurRoots l _ a1.1 a1.2
  obtain ⟨ξ, hξ⟩ := Formalism.L2.Th1.D.kurRoots l _ a2.1 a2.2
  have h := Formalism.L2.Th1.D.trDualExists (MaximalUnramifiedExtension l) l (2 * i) σ hU (even_two_mul i) ξ hξ
  rw [show 2 * i / 2 = i by omega] at h
  obtain ⟨om, oms, h1, h2⟩ := h
  exact UpperTheory.NormSurjectiveFixedIntegers.main hU ζ hζ i hi om oms h1 h2
