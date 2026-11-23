import Mathlib

open Polynomial

noncomputable section

namespace Formalism.L2.G

variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ) [NeZero n]

abbrev F1 : Type := GaloisField p n

abbrev F2 : Type := FiniteField.Extension (GaloisField p n) p 2

instance : CharP (F2 p n) p := charP_of_injective_algebraMap (algebraMap (ZMod p) (F2 p n)).injective p

instance : PerfectRing (F2 p n) p := PerfectRing.ofFiniteOfIsReduced p _

abbrev WQ : Type := WittVector p (F1 p n)

abbrev W2 : Type := WittVector p (F2 p n)

def jW : WQ p n →+* W2 p n := WittVector.map (algebraMap (F1 p n) (F2 p n))

private theorem card_wittVector_quot_p_eq_card_field (k : Type) [Field k] [CharP k p] [PerfectRing k p] :
    Nat.card (WittVector p k ⧸ Ideal.span {(p : WittVector p k)}) = Nat.card k := by
  have hsurj : Function.Surjective (WittVector.constantCoeff : WittVector p k →+* k) := by
    intro r
    exact ⟨WittVector.teichmuller p r, WittVector.teichmuller_coeff_zero p r⟩
  have hker : RingHom.ker (WittVector.constantCoeff : WittVector p k →+* k) =
      Ideal.span {(p : WittVector p k)} := by
    ext x
    rw [RingHom.mem_ker, Ideal.mem_span_singleton']
    constructor
    · intro hx
      by_cases h0 : x = 0
      · exact ⟨0, by rw [h0, zero_mul]⟩
      obtain ⟨m, b, hb0, hb⟩ := WittVector.exists_eq_pow_p_mul x h0
      cases m with
      | zero =>
        exfalso
        rw [pow_zero, one_mul] at hb
        exact hb0 (hb ▸ hx)
      | succ m => exact ⟨(p : WittVector p k) ^ m * b, by rw [hb]; ring⟩
    · rintro ⟨a, rfl⟩
      rw [map_mul, map_natCast, CharP.cast_eq_zero, mul_zero]
  rw [← hker]
  exact Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv

theorem card_quot_WQ : Nat.card (WQ p n ⧸ Ideal.span {(p : WQ p n)}) = p ^ n := by
  rw [card_wittVector_quot_p_eq_card_field]
  exact GaloisField.card p n (NeZero.ne n)

theorem card_quotient_extRing : Nat.card (W2 p n ⧸ Ideal.span {(p : W2 p n)}) = p ^ (2 * n) := by
  rw [card_wittVector_quot_p_eq_card_field, Module.natCard_eq_pow_finrank (K := F1 p n),
    FiniteField.finrank_extension, GaloisField.card p n (NeZero.ne n), ← pow_mul, mul_comm]

omit [NeZero n] in
theorem frob_WQ (x : WQ p n) : ∃ y : WQ p n, WittVector.frobenius x = x ^ p + (p : WQ p n) * y := by
  set d := WittVector.frobenius x - x ^ p with hd
  have hd0 : d.coeff 0 = 0 := by
    have h1 : WittVector.constantCoeff d = 0 := by
      rw [hd, map_sub, map_pow]
      show (WittVector.frobenius x).coeff 0 - (x.coeff 0) ^ p = 0
      rw [WittVector.coeff_frobenius_charP, sub_self]
    exact h1
  by_cases h0 : d = 0
  · refine ⟨0, ?_⟩
    rw [mul_zero, add_zero]
    exact sub_eq_zero.mp h0
  obtain ⟨k, y, hy0, hy⟩ := WittVector.exists_eq_pow_p_mul d h0
  cases k with
  | zero =>
    exfalso
    rw [pow_zero, one_mul] at hy
    exact hy0 (hy ▸ hd0)
  | succ k =>
    refine ⟨(p : WQ p n) ^ k * y, ?_⟩
    have : WittVector.frobenius x = x ^ p + d := by rw [hd]; ring
    rw [this, hy]
    ring

theorem frob_iter_WQ (x : WQ p n) : (WittVector.frobenius^[n]) x = x := by
  have hit : ∀ (m : ℕ) (y : WQ p n) (k : ℕ),
      ((WittVector.frobenius^[m]) y).coeff k = y.coeff k ^ (p ^ m) := by
    intro m
    induction m with
    | zero => intro y k; simp
    | succ m ih =>
      intro y k
      rw [Function.iterate_succ_apply', WittVector.coeff_frobenius_charP, ih, ← pow_mul, pow_succ]
  ext k
  rw [hit]
  haveI : Fintype (F1 p n) := Fintype.ofFinite _
  have hcard : Fintype.card (F1 p n) = p ^ n := by
    rw [Fintype.card_eq_nat_card]; exact GaloisField.card p n (NeZero.ne n)
  rw [← hcard, FiniteField.pow_card]

def sig : FractionRing (WQ p n) ≃+* FractionRing (WQ p n) :=
  IsFractionRing.ringEquivOfRingEquiv (WittVector.frobeniusEquiv p (F1 p n))

omit [NeZero n] in
theorem sig_alg (x : WQ p n) : sig p n (algebraMap _ _ x) = algebraMap _ _ (WittVector.frobenius x) := by
  unfold sig
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  rfl

omit [NeZero n] in
theorem sig_pow_alg (k : ℕ) (x : WQ p n) :
    (sig p n ^ k) (algebraMap _ _ x) = algebraMap _ _ ((WittVector.frobenius^[k]) x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ]
    show (sig p n ^ k) (sig p n (algebraMap _ _ x)) = _
    rw [sig_alg, ih, Function.iterate_succ_apply]

theorem sig_period : sig p n ^ n = 1 := by
  have h : ((sig p n ^ n).toRingHom : FractionRing (WQ p n) →+* FractionRing (WQ p n)) =
      RingHom.id _ := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (WQ p n)) ?_
    ext x
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingHom.id_apply]
    rw [sig_pow_alg, frob_iter_WQ]
  ext y
  have := congrArg (fun f : FractionRing (WQ p n) →+* FractionRing (WQ p n) => f y) h
  simpa using this

theorem precomplete_pi {R : Type*} [CommRing R] (π : R) [IsPrecomplete (Ideal.span {π}) R] (d : ℕ) :
    IsPrecomplete (Ideal.span {π}) (Fin d → R) := by
  have key : ∀ (m : ℕ) (v : Fin d → R),
      v ∈ (Ideal.span {π} ^ m • ⊤ : Submodule R (Fin d → R)) ↔ ∀ i, v i ∈ Ideal.span {π} ^ m := by
    intro m v
    constructor
    · intro hv
      refine Submodule.smul_induction_on (p := fun v : Fin d → R => ∀ i, v i ∈ Ideal.span {π} ^ m)
        hv ?_ ?_
      · intro r hr w _ i
        simp only [Pi.smul_apply, smul_eq_mul]
        exact Ideal.mul_mem_right _ _ hr
      · intro x y hx hy i
        simp only [Pi.add_apply]
        exact Ideal.add_mem _ (hx i) (hy i)
    · intro hv
      have hsum : v = ∑ i, v i • Pi.single i (1 : R) := by
        ext j
        simp [Finset.sum_apply, Pi.single_apply]
      rw [hsum]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hv i) Submodule.mem_top
  have key1 : ∀ (m : ℕ) (r : R), r ∈ (Ideal.span {π} ^ m • ⊤ : Submodule R R) ↔
      r ∈ Ideal.span {π} ^ m := by
    intro m r
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  refine ⟨fun f hf => ?_⟩
  have hcomp : ∀ i, ∃ L : R, ∀ k,
      f k i ≡ L [SMOD (Ideal.span {π} ^ k • ⊤ : Submodule R R)] := by
    intro i
    refine IsPrecomplete.prec inferInstance (fun {a b} hab => ?_)
    have h1 := hf hab
    rw [SModEq.sub_mem] at h1 ⊢
    rw [key] at h1
    rw [key1]
    simpa using h1 i
  choose L hL using hcomp
  refine ⟨L, fun k => ?_⟩
  rw [SModEq.sub_mem, key]
  intro i
  have h2 := hL i k
  rw [SModEq.sub_mem, key1] at h2
  simpa using h2

omit [NeZero n] in
theorem jW_natCast : jW p n (p : WQ p n) = (p : W2 p n) := map_natCast _ _

omit [NeZero n] in
theorem jW_coeff (x : WQ p n) (k : ℕ) : (jW p n x).coeff k = algebraMap (F1 p n) (F2 p n) (x.coeff k) :=
  WittVector.map_coeff _ _ _

omit [NeZero n] in
theorem jW_injective : Function.Injective (jW p n) := by
  intro x y h
  ext k
  have := congrArg (fun z => WittVector.coeff z k) h
  simp only [jW_coeff] at this
  exact (algebraMap (F1 p n) (F2 p n)).injective this

private theorem exists_mul_p_pow_eq_verschiebung_iterate (k : Type) [Field k] [CharP k p] [PerfectRing k p] (m : ℕ)
    (s : WittVector p k) :
    ∃ a : WittVector p k, a * (p : WittVector p k) ^ m = (⇑WittVector.verschiebung)^[m] s := by
  induction m generalizing s with
  | zero => exact ⟨s, by simp⟩
  | succ m ih =>
    obtain ⟨a, ha⟩ := ih s
    obtain ⟨b, hb⟩ : ∃ b, WittVector.frobenius b = a := by
      refine ⟨(WittVector.frobeniusEquiv p k).symm a, ?_⟩
      have := (WittVector.frobeniusEquiv p k).apply_symm_apply a
      rwa [WittVector.frobeniusEquiv_apply] at this
    refine ⟨b, ?_⟩
    rw [Function.iterate_succ_apply', ← ha, ← hb]
    have : WittVector.frobenius b * (p : WittVector p k) ^ m =
        WittVector.frobenius (b * (p : WittVector p k) ^ m) := by
      rw [map_mul, map_pow, map_natCast]
    rw [this, WittVector.verschiebung_frobenius]
    ring

private theorem mem_span_p_pow_iff_coeff_eq_zero (k : Type) [Field k] [CharP k p] [PerfectRing k p] (m : ℕ)
    (x : WittVector p k) :
    x ∈ Ideal.span {(p : WittVector p k)} ^ m ↔ ∀ i < m, x.coeff i = 0 := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, rfl⟩
    induction m with
    | zero => intro i hi; omega
    | succ m ih =>
      intro i hi
      have e : a * (p : WittVector p k) ^ (m + 1) = (a * (p : WittVector p k) ^ m) * p := by ring
      rw [e, ← WittVector.verschiebung_frobenius]
      cases i with
      | zero => exact WittVector.verschiebung_coeff_zero _
      | succ i =>
        rw [WittVector.verschiebung_coeff_succ, WittVector.coeff_frobenius_charP,
          ih i (by omega), zero_pow hp.out.ne_zero]
  · intro hx
    obtain ⟨a, ha⟩ := exists_mul_p_pow_eq_verschiebung_iterate p k m (x.shift m)
    exact ⟨a, by rw [ha]; exact (WittVector.eq_iterate_verschiebung hx).symm⟩

private theorem coeff_sub_eq_zero_iff_coeff_eq (k : Type) [CommRing k] (m : ℕ) (x y : WittVector p k) :
    (∀ i < m, (x - y).coeff i = 0) ↔ ∀ i < m, x.coeff i = y.coeff i := by
  have h0 : ∀ z : WittVector p k, (∀ i < m, z.coeff i = 0) ↔ WittVector.truncate m z = 0 := by
    intro z
    constructor
    · intro h
      ext i
      simp [WittVector.coeff_truncate, h i i.2]
    · intro h i hi
      have := congrArg (TruncatedWittVector.coeff ⟨i, hi⟩) h
      simpa [WittVector.coeff_truncate] using this
  rw [h0, map_sub, sub_eq_zero]
  constructor
  · intro h i hi
    have := congrArg (TruncatedWittVector.coeff ⟨i, hi⟩) h
    simpa [WittVector.coeff_truncate] using this
  · intro h
    ext i
    simp [WittVector.coeff_truncate, h i i.2]

private theorem isAdicComplete_span_p_wittVector (k : Type) [Field k] [CharP k p] [PerfectRing k p] :
    IsAdicComplete (Ideal.span {(p : WittVector p k)}) (WittVector p k) := by
  have hmem : ∀ (m : ℕ) (x : WittVector p k),
      x ∈ (Ideal.span {(p : WittVector p k)} ^ m • ⊤ : Submodule (WittVector p k) (WittVector p k)) ↔
        ∀ i < m, x.coeff i = 0 := by
    intro m x
    rw [Ideal.smul_eq_mul, Ideal.mul_top, mem_span_p_pow_iff_coeff_eq_zero]
  have hmod : ∀ (m : ℕ) (x y : WittVector p k),
      x ≡ y [SMOD (Ideal.span {(p : WittVector p k)} ^ m • ⊤ : Submodule (WittVector p k) (WittVector p k))] ↔
        ∀ i < m, x.coeff i = y.coeff i := by
    intro m x y
    rw [SModEq.sub_mem, hmem, coeff_sub_eq_zero_iff_coeff_eq]
  have H : IsHausdorff (Ideal.span {(p : WittVector p k)}) (WittVector p k) := by
    refine ⟨fun x hx => ?_⟩
    ext i
    have := (hmod (i + 1) x 0).mp (hx (i + 1)) i (by omega)
    simpa using this
  have P : IsPrecomplete (Ideal.span {(p : WittVector p k)}) (WittVector p k) := by
    refine ⟨fun f hf => ?_⟩
    refine ⟨WittVector.mk p (fun i => (f (i + 1)).coeff i), fun m => ?_⟩
    rw [hmod]
    intro i hi
    simp only [WittVector.coeff_mk]
    exact ((hmod (i + 1) (f (i + 1)) (f m)).mp (hf (by omega)) i (by omega)).symm
  haveI := H
  haveI := P
  constructor

private theorem mem_span_pow_smul_top_pi_iff {R : Type*} [CommRing R] (π : R) (d m : ℕ) (v : Fin d → R) :
    v ∈ (Ideal.span {π} ^ m • ⊤ : Submodule R (Fin d → R)) ↔ ∀ i, v i ∈ Ideal.span {π} ^ m := by
  constructor
  · intro hv
    refine Submodule.smul_induction_on (p := fun v : Fin d → R => ∀ i, v i ∈ Ideal.span {π} ^ m)
      hv ?_ ?_
    · intro r hr w _ i
      simp only [Pi.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ hr
    · intro x y hx hy i
      simp only [Pi.add_apply]
      exact Ideal.add_mem _ (hx i) (hy i)
  · intro hv
    have hsum : v = ∑ i, v i • Pi.single i (1 : R) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hv i) Submodule.mem_top

theorem jW_finite : (jW p n).Finite := by
  classical
  haveI hc1 := isAdicComplete_span_p_wittVector p (F1 p n)
  haveI hc2 := isAdicComplete_span_p_wittVector p (F2 p n)
  haveI : IsPrecomplete (Ideal.span {(p : WQ p n)}) (Fin 2 → WQ p n) := precomplete_pi _ 2
  have hfr : Module.finrank (F1 p n) (F2 p n) = 2 := FiniteField.finrank_extension _ _ _
  let b : Module.Basis (Fin 2) (F1 p n) (F2 p n) := Module.finBasisOfFinrankEq _ _ hfr
  let e : Fin 2 → W2 p n := fun j => WittVector.teichmuller p (b j)
  have hjW : ∀ (m : ℕ) (a : WQ p n), jW p n ((p : WQ p n) ^ m * a) = (p : W2 p n) ^ m * jW p n a := by
    intro m a
    rw [map_mul, map_pow, map_natCast]
  have step : ∀ w : W2 p n, ∃ a : Fin 2 → WQ p n, ∃ w' : W2 p n,
      w = ∑ j, jW p n (a j) * e j + (p : W2 p n) * w' := by
    intro w
    set c := b.repr (w.coeff 0) with hc
    refine ⟨fun j => WittVector.teichmuller p (c j), ?_⟩
    have h0 : (w - ∑ j, jW p n (WittVector.teichmuller p (c j)) * e j).coeff 0 = 0 := by
      show WittVector.constantCoeff (w - ∑ j, jW p n (WittVector.teichmuller p (c j)) * e j) = 0
      rw [map_sub, map_sum]
      have h1 : ∀ j, WittVector.constantCoeff (jW p n (WittVector.teichmuller p (c j)) * e j) =
          c j • b j := by
        intro j
        rw [map_mul, Algebra.smul_def]
        congr 1 <;> first
          | exact WittVector.teichmuller_coeff_zero p (b j)
          | (show (jW p n _).coeff 0 = _; rw [jW_coeff, WittVector.teichmuller_coeff_zero])
      simp only [h1]
      rw [sub_eq_zero, hc, b.sum_repr]
      rfl
    have hm : w - ∑ j, jW p n (WittVector.teichmuller p (c j)) * e j ∈
        Ideal.span {(p : W2 p n)} := by
      have := (mem_span_p_pow_iff_coeff_eq_zero p (F2 p n) 1 _).mpr (fun i hi => by
        obtain rfl : i = 0 := by omega
        exact h0)
      rwa [pow_one] at this
    obtain ⟨w', hw'⟩ := Ideal.mem_span_singleton'.mp hm
    exact ⟨w', by rw [mul_comm, hw']; ring⟩
  choose A Rm hAR using step
  have expand : ∀ (w : W2 p n) (N : ℕ), w = ∑ j, jW p n (∑ m ∈ Finset.range N,
      (p : WQ p n) ^ m * A (Rm^[m] w) j) * e j + (p : W2 p n) ^ N * Rm^[N] w := by
    intro w N
    induction N with
    | zero => simp
    | succ N ih =>
      have h := hAR (Rm^[N] w)
      rw [Function.iterate_succ_apply']
      conv_lhs => rw [ih]
      conv_lhs => rw [h]
      simp only [Finset.sum_range_succ, map_add, add_mul, Finset.sum_add_distrib, hjW, mul_add,
        Finset.mul_sum]
      ring
  unfold RingHom.Finite
  letI : Algebra (WQ p n) (W2 p n) := (jW p n).toAlgebra
  refine ⟨⟨Finset.univ.image e, ?_⟩⟩
  rw [Submodule.eq_top_iff']
  intro w
  obtain ⟨s, hsdef⟩ : ∃ s : ℕ → Fin 2 → WQ p n, ∀ N j,
      s N j = ∑ m ∈ Finset.range N, (p : WQ p n) ^ m * A (Rm^[m] w) j := ⟨_, fun _ _ => rfl⟩
  have hs : ∀ {a b : ℕ}, a ≤ b → s a ≡ s b [SMOD (Ideal.span {(p : WQ p n)} ^ a • ⊤ :
      Submodule (WQ p n) (Fin 2 → WQ p n))] := by
    intro a b hab
    rw [SModEq.sub_mem, mem_span_pow_smul_top_pi_iff]
    intro j
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
    have h1 : s a j - s (a + d) j = -((p : WQ p n) ^ a *
        ∑ l ∈ Finset.range d, (p : WQ p n) ^ l * A (Rm^[a + l] w) j) := by
      simp only [Pi.sub_apply, hsdef, Finset.sum_range_add, Finset.mul_sum, pow_add]
      ring
    rw [Pi.sub_apply, h1, Ideal.span_singleton_pow]
    exact neg_mem (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec inferInstance hs
  have hw : w = ∑ j, jW p n (L j) * e j := by
    rw [← sub_eq_zero]
    refine IsHausdorff.haus hc2.toIsHausdorff _ (fun N => ?_)
    rw [SModEq.sub_mem, sub_zero, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton']
    have h1 := hL N
    rw [SModEq.sub_mem, mem_span_pow_smul_top_pi_iff] at h1
    have h2 : ∀ j, ∃ t, t * (p : WQ p n) ^ N = s N j - L j := fun j => by
      have := h1 j
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at this
      exact this
    choose tt htt using h2
    have h3 : ∀ j, jW p n (L j) = jW p n (s N j) - (p : W2 p n) ^ N * jW p n (tt j) := by
      intro j
      have : L j = s N j - (p : WQ p n) ^ N * tt j := by rw [mul_comm, htt j]; ring
      rw [this, map_sub, hjW]
    have hx : w = ∑ j, jW p n (s N j) * e j + (p : W2 p n) ^ N * Rm^[N] w := by
      simp only [hsdef]
      exact expand w N
    have key : w - ∑ j, jW p n (L j) * e j =
        (∑ j, jW p n (tt j) * e j + Rm^[N] w) * (p : W2 p n) ^ N := by
      conv_lhs => rw [hx]
      simp only [h3, sub_mul, Finset.sum_sub_distrib, add_mul, Finset.sum_mul]
      ring_nf
    exact ⟨_, key.symm⟩
  rw [hw]
  refine Submodule.sum_mem _ fun j _ => ?_
  have h4 : jW p n (L j) * e j = L j • e j := rfl
  rw [h4]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

theorem isSquare_algebraMap (hp2 : p ≠ 2) (a : F1 p n) : IsSquare (algebraMap (F1 p n) (F2 p n) a) := by
  by_cases ha : a = 0
  · rw [ha, map_zero]; exact ⟨0, by simp⟩
  haveI : Fintype (F1 p n) := Fintype.ofFinite _
  haveI : Fintype (F2 p n) := Fintype.ofFinite _
  have hq : Fintype.card (F1 p n) = p ^ n := by
    rw [Fintype.card_eq_nat_card]; exact GaloisField.card p n (NeZero.ne n)
  have hq2 : Fintype.card (F2 p n) = (p ^ n) ^ 2 := by
    rw [Fintype.card_eq_nat_card, Module.natCard_eq_pow_finrank (K := F1 p n),
      FiniteField.finrank_extension, GaloisField.card p n (NeZero.ne n)]
  have hchar : ringChar (F2 p n) ≠ 2 := by
    rw [ringChar.eq (F2 p n) p]; exact hp2
  have ha' : algebraMap (F1 p n) (F2 p n) a ≠ 0 := by
    rw [ne_eq, map_eq_zero]; exact ha
  rw [FiniteField.isSquare_iff hchar ha', hq2]
  obtain ⟨r, hr⟩ : Odd (p ^ n) := (hp.out.odd_of_ne_two hp2).pow
  have hexp : (p ^ n) ^ 2 / 2 = (p ^ n - 1) * (r + 1) := by
    rw [hr, show (2 * r + 1) ^ 2 = 2 * (2 * r * (r + 1)) + 1 by ring,
      Nat.mul_add_div (by norm_num : 0 < 2), Nat.add_sub_cancel]
    norm_num
  rw [hexp, pow_mul, ← map_pow, ← hq, FiniteField.pow_card_sub_one_eq_one a ha, map_one, one_pow]

omit [NeZero n] in
theorem sq_lift (c : W2 p n) (y0 : F2 p n) (hc : c.coeff 0 = y0 * y0) (hy00 : y0 ≠ 0)
    (h2 : (2 : F2 p n) ≠ 0) : ∃ y : W2 p n, y ^ 2 = c := by
  haveI := isAdicComplete_span_p_wittVector p (F2 p n)
  haveI := IsAdicComplete.henselianRing (W2 p n) (Ideal.span {(p : W2 p n)})
  have hmon : (Polynomial.X ^ 2 - Polynomial.C c).Monic := Polynomial.monic_X_pow_sub_C c (by norm_num)
  set a0 : W2 p n := WittVector.teichmuller p y0 with ha0
  have ha00 : WittVector.constantCoeff a0 = y0 := WittVector.teichmuller_coeff_zero p y0
  have hev : (Polynomial.X ^ 2 - Polynomial.C c).eval a0 ∈ Ideal.span {(p : W2 p n)} := by
    have := (mem_span_p_pow_iff_coeff_eq_zero p (F2 p n) 1 ((Polynomial.X ^ 2 - Polynomial.C c).eval a0)).mpr
      (fun i hi => by
        obtain rfl : i = 0 := by omega
        show WittVector.constantCoeff _ = 0
        simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
          map_sub, map_pow, ha00]
        rw [show WittVector.constantCoeff c = c.coeff 0 from rfl, hc]
        ring)
    rwa [pow_one] at this
  have hder : IsUnit ((Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C c)).eval a0) := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    show WittVector.constantCoeff _ ≠ 0
    simp only [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C,
      sub_zero, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_natCast, map_mul, map_pow, map_natCast, ha00]
    norm_num
    exact ⟨h2, hy00⟩
  obtain ⟨y, hy, -⟩ := HenselianRing.is_henselian _ hmon a0 hev (hder.map _)
  refine ⟨y, ?_⟩
  have := hy.eq_zero
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at this
  exact sub_eq_zero.mp this

theorem exists_sq_eq_intCast_of_not_dvd_of_ne_two (hp2 : p ≠ 2) (z : ℤ) (hz : ¬ (p : ℤ) ∣ z) : ∃ y : W2 p n, y ^ 2 = (z : W2 p n) := by
  obtain ⟨r, hr⟩ := isSquare_algebraMap p n hp2 (z : F1 p n)
  have hz0 : ((z : ℤ) : F2 p n) ≠ 0 := by
    rw [ne_eq, CharP.intCast_eq_zero_iff (F2 p n) p]; exact hz
  have hc : (z : W2 p n).coeff 0 = r * r := by
    have : WittVector.constantCoeff (z : W2 p n) = ((z : ℤ) : F2 p n) := map_intCast _ _
    rw [← hr, map_intCast]
    exact this
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hz0
    rw [← map_intCast (algebraMap (F1 p n) (F2 p n)), hr, mul_zero]
  have h2 : (2 : F2 p n) ≠ 0 := by
    have : ((2 : ℕ) : F2 p n) ≠ 0 := by
      rw [ne_eq, CharP.cast_eq_zero_iff (F2 p n) p]
      intro hdvd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp hdvd)
    simpa using this
  exact sq_lift p n _ r hc hr0 h2

end Formalism.L2.G
