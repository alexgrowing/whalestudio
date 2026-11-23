import Mathlib

namespace GlobalTheory.AlgRing

private theorem exists_idempotent_of_not_isNilpotent (k R : Type) [Field k] [Ring R] [Algebra k R]
    (x : R) (hx : IsIntegral k x) (hn : ¬ IsNilpotent x) :
    ∃ e : R, IsIdempotentElem e ∧ e ≠ 0 ∧ ∃ q : Polynomial k, e = x * Polynomial.aeval x q := by
  have hp0 : minpoly k x ≠ 0 := minpoly.ne_zero hx
  obtain ⟨g, hpg, hg⟩ :=
    Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd (minpoly k x) hp0 0
  simp only [map_zero, sub_zero] at hpg hg
  set s := Polynomial.rootMultiplicity 0 (minpoly k x)
  have hcop : IsCoprime (Polynomial.X ^ (s + 1)) g :=
    (Polynomial.irreducible_X.coprime_iff_not_dvd.mpr hg).pow_left
  obtain ⟨a, b, hab⟩ := hcop
  have hev : Polynomial.aeval x (Polynomial.X ^ s * g) = 0 := by
    rw [← hpg]; exact minpoly.aeval k x
  have hE : ∀ P : Polynomial k,
      Polynomial.aeval x (P * (Polynomial.X ^ s * g)) = 0 := fun P => by rw [map_mul, hev, mul_zero]
  refine ⟨Polynomial.aeval x (a * Polynomial.X ^ (s + 1)), ?_, ?_, ⟨a * Polynomial.X ^ s, ?_⟩⟩
  · have hpoly : (a * Polynomial.X ^ (s + 1)) * (a * Polynomial.X ^ (s + 1)) =
        a * Polynomial.X ^ (s + 1) + (-(a * b * Polynomial.X)) * (Polynomial.X ^ s * g) := by
      linear_combination (a * Polynomial.X ^ (s + 1)) * hab
    unfold IsIdempotentElem
    rw [← map_mul, hpoly, map_add, hE, add_zero]
  · intro he
    apply hn
    refine ⟨s, ?_⟩
    have hpoly : (Polynomial.X : Polynomial k) ^ s =
        Polynomial.X ^ s * (a * Polynomial.X ^ (s + 1)) + b * (Polynomial.X ^ s * g) := by
      linear_combination (Polynomial.X ^ s) * hab.symm
    have := congrArg (Polynomial.aeval x) hpoly
    rwa [map_add, hE, add_zero, map_mul, he, mul_zero, map_pow, Polynomial.aeval_X] at this
  · have h : a * Polynomial.X ^ (s + 1) = Polynomial.X * (a * Polynomial.X ^ s) := by ring
    rw [h, map_mul, Polynomial.aeval_X]

private theorem exists_idempotent_mem_left_multiples (k R : Type) [Field k] [Ring R] [Algebra k R]
    (hint : ∀ x : R, IsIntegral k x) (hnil : ∀ x : R, (∀ y : R, IsNilpotent (y * x)) → x = 0)
    (x : R) (hx : x ≠ 0) : ∃ e r : R, IsIdempotentElem e ∧ e ≠ 0 ∧ e = r * x := by
  have : ¬ ∀ y : R, IsNilpotent (y * x) := fun h => hx (hnil x h)
  push_neg at this
  obtain ⟨y, hy⟩ := this
  obtain ⟨e, he, he0, q, rfl⟩ := exists_idempotent_of_not_isNilpotent k R (y * x) (hint _) hy
  have hcomm : Commute (y * x) (Polynomial.aeval (y * x) q) := by
    simpa using (Polynomial.commute_X q).map (Polynomial.aeval (y * x))
  refine ⟨_, Polynomial.aeval (y * x) q * y, he, he0, ?_⟩
  rw [hcomm.eq, mul_assoc]

private theorem sum_eq_one_of_maximal_orthogonalIdempotents (k R : Type) [Field k] [Ring R]
    [Algebra k R] (hint : ∀ x : R, IsIntegral k x)
    (hnil : ∀ x : R, (∀ y : R, IsNilpotent (y * x)) → x = 0) {m : ℕ} (e : Fin m → R)
    (he : OrthogonalIdempotents e) (hne : ∀ i, e i ≠ 0)
    (hmax : ∀ e' : Fin (m + 1) → R, OrthogonalIdempotents e' → (∀ i, e' i ≠ 0) → False) :
    ∑ i, e i = 1 := by
  by_contra hsum
  set f := 1 - ∑ i, e i with hfdef
  have hf0 : f ≠ 0 := sub_ne_zero.mpr (Ne.symm hsum)
  have hS : IsIdempotentElem (∑ i, e i) := he.isIdempotentElem_sum
  have hf : IsIdempotentElem f := hS.one_sub
  have hef : ∀ i, e i * f = 0 := fun i => by
    rw [hfdef, mul_sub, mul_one, he.mul_sum_of_mem (Finset.mem_univ i), sub_self]
  have hfe : ∀ i, f * e i = 0 := fun i => by
    rw [hfdef, sub_mul, one_mul, Finset.sum_mul,
      Finset.sum_eq_single i (fun j _ hj => he.ortho hj) (by simp), (he.idem i).eq, sub_self]
  obtain ⟨e', r, he', he'0, rfl⟩ :=
    exists_idempotent_mem_left_multiples k R hint hnil f hf0
  have hg : IsIdempotentElem (f * (r * f)) := by
    unfold IsIdempotentElem
    calc f * (r * f) * (f * (r * f)) = f * (r * (f * f)) * (r * f) := by noncomm_ring
      _ = f * (r * f) := by rw [hf.eq, mul_assoc, he'.eq]
  have hg0 : f * (r * f) ≠ 0 := by
    intro h0
    apply he'0
    rw [← he'.eq, mul_assoc, h0, mul_zero]
  refine hmax (Fin.cons (f * (r * f)) e) ⟨fun i => ?_, fun i j hij => ?_⟩ fun i => ?_
  · refine Fin.cases hg (fun i => ?_) i
    simpa using he.idem i
  · induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact absurd rfl hij
      | succ j => simp only [Fin.cons_zero, Fin.cons_succ]; rw [mul_assoc, mul_assoc, hfe, mul_zero, mul_zero]
    | succ i =>
      induction j using Fin.cases with
      | zero => simp only [Fin.cons_zero, Fin.cons_succ]; rw [← mul_assoc, hef, zero_mul]
      | succ j =>
        simp only [Fin.cons_succ]
        exact he.ortho fun h => hij (by rw [h])
  · refine Fin.cases hg0 (fun i => ?_) i
    simpa using hne i

private theorem not_isNilpotent_mul_mul_of_mul_eq_of_not_isNilpotent {R : Type} [Ring R] (f a y : R) (hl : f * a = a)
    (hy : ¬ IsNilpotent (y * a)) : ¬ IsNilpotent (a * y * f) := by
  have hpow : ∀ j : ℕ, (a * y) ^ (j + 1) = (a * y * f) ^ j * (a * y) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ (a * y) (j + 1), ih, pow_succ (a * y * f) j, mul_assoc ((a * y * f) ^ j),
        mul_assoc ((a * y * f) ^ j)]
      congr 1
      rw [mul_assoc (a * y) f, ← mul_assoc f a y, hl]
  rintro ⟨n, hn⟩
  have hya : ∀ j : ℕ, (y * a) ^ (j + 1) = y * (a * y) ^ j * a := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, ih, pow_succ]; simp only [mul_assoc]
  exact hy ⟨n + 2, by rw [hya, hpow, hn, zero_mul, mul_zero, zero_mul]⟩

private theorem eq_of_idempotent_in_corner_of_maximal {R : Type} [Ring R] {m : ℕ} (e : Fin m → R)
    (he : OrthogonalIdempotents e) (hne : ∀ i, e i ≠ 0)
    (hmax : ∀ e' : Fin (m + 1) → R, OrthogonalIdempotents e' → (∀ i, e' i ≠ 0) → False)
    (i : Fin m) (f : R) (hf : IsIdempotentElem f) (hf0 : f ≠ 0) (hl : e i * f = f)
    (hr : f * e i = f) : f = e i := by
  by_contra hfe
  have hg : IsIdempotentElem (e i - f) := by
    unfold IsIdempotentElem
    rw [sub_mul, mul_sub, mul_sub, (he.idem i).eq, hl, hr, hf.eq]; abel
  have hg0 : e i - f ≠ 0 := sub_ne_zero.mpr (Ne.symm hfe)
  have hgf : (e i - f) * f = 0 := by rw [sub_mul, hl, hf.eq, sub_self]
  have hfg : f * (e i - f) = 0 := by rw [mul_sub, hr, hf.eq, sub_self]
  have hjf : ∀ j, j ≠ i → e j * f = 0 := fun j hj => by rw [← hl, ← mul_assoc, he.ortho hj, zero_mul]
  have hfj : ∀ j, j ≠ i → f * e j = 0 := fun j hj => by rw [← hr, mul_assoc, he.ortho hj.symm, mul_zero]
  have hjg : ∀ j, j ≠ i → e j * (e i - f) = 0 := fun j hj => by rw [mul_sub, he.ortho hj, hjf j hj, sub_self]
  have hgj : ∀ j, j ≠ i → (e i - f) * e j = 0 := fun j hj => by rw [sub_mul, he.ortho hj.symm, hfj j hj, sub_self]
  set u := Function.update e i f
  have hu : ∀ j, u j = if j = i then f else e j := fun j => Function.update_apply e i f j
  refine hmax (Fin.cons (e i - f) u) ⟨fun j => ?_, fun a b hab => ?_⟩ fun j => ?_
  · refine Fin.cases hg (fun j => ?_) j
    simp only [Fin.cons_succ, hu]; split_ifs
    · exact hf
    · exact he.idem j
  · induction a using Fin.cases with
    | zero =>
      induction b using Fin.cases with
      | zero => exact absurd rfl hab
      | succ b =>
        simp only [Fin.cons_zero, Fin.cons_succ, hu]; split_ifs with hb
        · exact hgf
        · exact hgj b hb
    | succ a =>
      induction b using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero, Fin.cons_succ, hu]; split_ifs with ha
        · exact hfg
        · exact hjg a ha
      | succ b =>
        have hab' : a ≠ b := fun h => hab (by rw [h])
        simp only [Fin.cons_succ, hu]
        split_ifs with ha hb hb
        · exact absurd (ha.trans hb.symm) hab'
        · exact hfj b hb
        · exact hjf a ha
        · exact he.ortho hab'
  · refine Fin.cases hg0 (fun j => ?_) j
    simp only [Fin.cons_succ, hu]; split_ifs
    · exact hf0
    · exact hne j

private theorem exists_right_inverse_in_corner_of_not_isNilpotent (k R : Type) [Field k] [Ring R] [Algebra k R]
    (hint : ∀ x : R, IsIntegral k x) {m : ℕ} (e : Fin m → R)
    (he : OrthogonalIdempotents e) (hne : ∀ i, e i ≠ 0)
    (hmax : ∀ e' : Fin (m + 1) → R, OrthogonalIdempotents e' → (∀ i, e' i ≠ 0) → False)
    (i : Fin m) (z : R) (hl : e i * z = z) (hr : z * e i = z) (hz : ¬ IsNilpotent z) :
    ∃ t, e i * t = t ∧ z * t = e i := by
  obtain ⟨f, hf, hf0, q, rfl⟩ := exists_idempotent_of_not_isNilpotent k R z (hint z) hz
  have hcomm : Commute z (Polynomial.aeval z q) := by
    simpa using (Polynomial.commute_X q).map (Polynomial.aeval z)
  have hfl : e i * (z * Polynomial.aeval z q) = z * Polynomial.aeval z q := by
    rw [← mul_assoc, hl]
  have hfr : z * Polynomial.aeval z q * e i = z * Polynomial.aeval z q := by
    rw [hcomm.eq, mul_assoc, hr]
  have hfe := eq_of_idempotent_in_corner_of_maximal e he hne hmax i _ hf hf0 hfl hfr
  refine ⟨e i * Polynomial.aeval z q, by rw [← mul_assoc, (he.idem i).eq], ?_⟩
  rw [← mul_assoc, hr, hfe]

private theorem eq_zero_of_isNilpotent_in_corner_of_maximal (k R : Type) [Field k] [Ring R] [Algebra k R]
    (hint : ∀ x : R, IsIntegral k x) (hnil : ∀ x : R, (∀ y : R, IsNilpotent (y * x)) → x = 0)
    {m : ℕ} (e : Fin m → R)
    (he : OrthogonalIdempotents e) (hne : ∀ i, e i ≠ 0)
    (hmax : ∀ e' : Fin (m + 1) → R, OrthogonalIdempotents e' → (∀ i, e' i ≠ 0) → False)
    (i : Fin m) (w : R) (hl : e i * w = w) (hr : w * e i = w) (hw : IsNilpotent w) : w = 0 := by
  by_contra hw0
  have : ¬ ∀ y : R, IsNilpotent (y * w) := fun h => hw0 (hnil w h)
  push_neg at this
  obtain ⟨y, hy⟩ := this
  have hpow : ∀ j : ℕ, (w * y) ^ (j + 1) = (w * y * e i) ^ j * (w * y) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ (w * y) (j + 1), ih, pow_succ (w * y * e i) j, mul_assoc ((w * y * e i) ^ j),
        mul_assoc ((w * y * e i) ^ j)]
      congr 1
      rw [mul_assoc (w * y) (e i), ← mul_assoc (e i) w y, hl]
  have hu : ¬ IsNilpotent (w * y * e i) := by
    rintro ⟨n, hn⟩
    have hyw : ∀ j : ℕ, (y * w) ^ (j + 1) = y * (w * y) ^ j * w := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => rw [pow_succ, ih, pow_succ]; simp only [mul_assoc]
    exact hy ⟨n + 2, by rw [hyw, hpow, hn, zero_mul, mul_zero, zero_mul]⟩
  obtain ⟨t, het, hut⟩ := exists_right_inverse_in_corner_of_not_isNilpotent k R hint e he hne hmax i (w * y * e i)
    (by rw [← mul_assoc, ← mul_assoc, hl]) (by rw [mul_assoc, (he.idem i).eq]) hu
  set s := e i * (y * e i * t)
  have hs : e i * s = s := by rw [← mul_assoc, (he.idem i).eq]
  have hws : w * s = e i := by
    have h3 : w * (y * e i * t) = w * y * e i * t := by simp only [mul_assoc]
    rw [← mul_assoc, hr, h3, hut]
  have hj : ∀ j : ℕ, e i = w ^ (j + 1) * s ^ (j + 1) := by
    intro j
    induction j with
    | zero => simp [hws]
    | succ j ih =>
      rw [pow_succ w (j + 1), pow_succ' s (j + 1), mul_assoc, ← mul_assoc w s, hws,
        pow_succ' s j, ← mul_assoc (e i) s, hs, ← pow_succ']
      exact ih
  obtain ⟨N, hN⟩ := hw
  apply hne i
  rw [hj N, pow_succ, hN, zero_mul, zero_mul]

private theorem exists_eq_smul_idempotent_of_mem_corner (k R : Type) [Field k] [IsAlgClosed k] [Ring R]
    [Algebra k R] (hint : ∀ x : R, IsIntegral k x)
    (hnil : ∀ x : R, (∀ y : R, IsNilpotent (y * x)) → x = 0) {m : ℕ} (e : Fin m → R)
    (he : OrthogonalIdempotents e) (hne : ∀ i, e i ≠ 0)
    (hmax : ∀ e' : Fin (m + 1) → R, OrthogonalIdempotents e' → (∀ i, e' i ≠ 0) → False)
    (i : Fin m) (z : R) (hl : e i * z = z) (hr : z * e i = z) : ∃ c : k, z = c • e i := by
  by_cases hz : IsNilpotent z
  · refine ⟨0, ?_⟩
    rw [zero_smul]
    exact eq_zero_of_isNilpotent_in_corner_of_maximal k R hint hnil e he hne hmax i z hl hr hz
  have hp0 : minpoly k z ≠ 0 := minpoly.ne_zero (hint z)
  obtain ⟨g, hpg, hg⟩ :=
    Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd (minpoly k z) hp0 0
  simp only [map_zero, sub_zero] at hpg hg
  set s := Polynomial.rootMultiplicity 0 (minpoly k z)
  have hev : Polynomial.aeval z (Polynomial.X ^ s * g) = 0 := by
    rw [← hpg]; exact minpoly.aeval k z
  have hg0 : g ≠ 0 := by rintro rfl; rw [mul_zero] at hpg; exact hp0 hpg
  have hgdeg : g.degree ≠ 0 := by
    intro h0
    rw [Polynomial.eq_C_of_degree_eq_zero h0, map_mul, map_pow, Polynomial.aeval_X,
      Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one] at hev
    have hc : g.coeff 0 ≠ 0 := fun h => hg (Polynomial.X_dvd_iff.mpr h)
    exact hz ⟨s, by simpa [hc] using hev⟩
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_root g hgdeg
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hg (by simpa using Polynomial.dvd_iff_isRoot.mpr hc)
  by_contra hno
  push_neg at hno
  set w := z - c • e i with hw
  have hei : e i * e i = e i := (he.idem i).eq
  have hwl : e i * w = w := by rw [hw, mul_sub, hl, mul_smul_comm, hei]
  have hwr : w * e i = w := by rw [hw, sub_mul, hr, smul_mul_assoc, hei]
  have hwn : ¬ IsNilpotent w := fun hn => hno c (sub_eq_zero.mp
    (eq_zero_of_isNilpotent_in_corner_of_maximal k R hint hnil e he hne hmax i w hwl hwr hn))
  obtain ⟨t, het, hwt⟩ := exists_right_inverse_in_corner_of_not_isNilpotent k R hint e he hne hmax i w hwl hwr hwn
  have hzu : Polynomial.aeval z (Polynomial.X - Polynomial.C c) *
      (t - c⁻¹ • (1 - e i)) = 1 := by
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
    have h1 : z * t - c • t = e i := by
      rw [← hwt, hw, sub_mul, smul_mul_assoc, het]
    have h2 : (z - c • (1 : R)) * (1 - e i) = -(c • (1 - e i)) := by
      simp only [mul_sub, sub_mul, mul_one, one_mul, hr, smul_mul_assoc, smul_sub]
      abel
    rw [mul_sub, mul_smul_comm, h2, smul_neg, smul_smul, inv_mul_cancel₀ hc0, one_smul,
      sub_mul, smul_mul_assoc, one_mul, h1]
    abel
  obtain ⟨h, hh⟩ : ∃ h, g = (Polynomial.X - Polynomial.C c) * h :=
    Polynomial.dvd_iff_isRoot.mpr hc
  have hcomm : Polynomial.X ^ s * g = (Polynomial.X ^ s * h) * (Polynomial.X - Polynomial.C c) := by
    rw [hh]; ring
  have hzero : Polynomial.aeval z (Polynomial.X ^ s * h) = 0 := by
    rw [hcomm, map_mul] at hev
    have := congrArg (· * (t - c⁻¹ • (1 - e i))) hev
    rwa [mul_assoc, hzu, mul_one, zero_mul] at this
  have hh0 : Polynomial.X ^ s * h ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) ?_
    rintro rfl; exact hg0 (by rw [hh, mul_zero])
  have hdeg := minpoly.degree_le_of_ne_zero k z hh0 hzero
  rw [hpg, hcomm, Polynomial.degree_mul, Polynomial.degree_X_sub_C] at hdeg
  have hfin : (Polynomial.X ^ s * h).degree ≠ ⊥ := by
    rwa [Ne, Polynomial.degree_eq_bot]
  obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.mp hfin
  rw [← hn] at hdeg
  rw [← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_le_coe] at hdeg
  omega

private theorem exists_smul_eq_corner_of_maximal_orthogonalIdempotents (k R : Type) [Field k] [IsAlgClosed k] [Ring R]
    [Algebra k R] (hint : ∀ x : R, IsIntegral k x)
    (hnil : ∀ x : R, (∀ y : R, IsNilpotent (y * x)) → x = 0) {m : ℕ} (e : Fin m → R)
    (he : OrthogonalIdempotents e) (hne : ∀ i, e i ≠ 0)
    (hmax : ∀ e' : Fin (m + 1) → R, OrthogonalIdempotents e' → (∀ i, e' i ≠ 0) → False)
    (i j : Fin m) : ∃ a : R, ∀ r : R, ∃ c : k, e i * r * e j = c • a := by
  by_cases h : ∀ r, e i * r * e j = 0
  · exact ⟨0, fun r => ⟨0, by rw [h r, smul_zero]⟩⟩
  push_neg at h
  obtain ⟨r0, ha0⟩ := h
  set a := e i * r0 * e j
  have hii : e i * e i = e i := (he.idem i).eq
  have hjj : e j * e j = e j := (he.idem j).eq
  have hal : e i * a = a := by simp only [a, ← mul_assoc, hii]
  have har : a * e j = a := by simp only [a, mul_assoc, hjj]
  have : ¬ ∀ y : R, IsNilpotent (y * a) := fun h => ha0 (hnil a h)
  push_neg at this
  obtain ⟨y, hy⟩ := this
  have hu := not_isNilpotent_mul_mul_of_mul_eq_of_not_isNilpotent (e i) a y hal hy
  obtain ⟨ν, hν⟩ := exists_eq_smul_idempotent_of_mem_corner k R hint hnil e he hne hmax i (a * y * e i)
    (by rw [← mul_assoc, ← mul_assoc, hal]) (by rw [mul_assoc, hii])
  have hν0 : ν ≠ 0 := by
    rintro rfl; rw [zero_smul] at hν; exact hu (by rw [hν]; exact IsNilpotent.zero)
  set b := ν⁻¹ • (e j * y * e i)
  have hab : a * b = e i := by
    simp only [b, mul_smul_comm, ← mul_assoc, har]
    rw [hν, smul_smul, inv_mul_cancel₀ hν0, one_smul]
  have hbe : b * e i = b := by simp only [b, smul_mul_assoc, mul_assoc, hii]
  obtain ⟨μ, hμ⟩ := exists_eq_smul_idempotent_of_mem_corner k R hint hnil e he hne hmax j (b * a)
    (by simp only [b, smul_mul_assoc, mul_smul_comm, ← mul_assoc, hjj]) (by rw [mul_assoc, har])
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hμ
    apply ha0
    rw [← hal, ← hab, mul_assoc, hμ, mul_zero]
  refine ⟨a, fun r => ?_⟩
  set c := e i * r * e j
  have hcl : e i * c = c := by simp only [c, ← mul_assoc, hii]
  have hcr : c * e j = c := by simp only [c, mul_assoc, hjj]
  obtain ⟨l, hl⟩ := exists_eq_smul_idempotent_of_mem_corner k R hint hnil e he hne hmax i (c * b)
    (by rw [← mul_assoc, hcl]) (by rw [mul_assoc, hbe])
  refine ⟨μ⁻¹ * l, ?_⟩
  calc c = c * e j := hcr.symm
    _ = μ⁻¹ • (c * (b * a)) := by rw [hμ, mul_smul_comm, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
    _ = (μ⁻¹ * l) • a := by rw [← mul_assoc, hl, smul_mul_assoc, hal, smul_smul]

theorem _root_.GlobalTheory.AlgRing.finite_and_isSemisimpleRing :
    ∀ (k R : Type) [Field k] [IsAlgClosed k] [Ring R] [Algebra k R] (d : ℕ),
      (∀ x : R, IsIntegral k x) → (∀ x : R, (∀ y : R, IsNilpotent (y * x)) → x = 0) →
      (∀ (m : ℕ) (e : Fin m → R), OrthogonalIdempotents e → (∀ i, e i ≠ 0) → m ≤ d) →
      Module.Finite k R ∧ IsSemisimpleRing R := by
  intro k R _ _ _ _ d hint hnil hidem
  have hfin : Module.Finite k R := by
    classical
    let P : ℕ → Prop := fun m => ∃ e : Fin m → R, OrthogonalIdempotents e ∧ ∀ i, e i ≠ 0
    have hP0 : P 0 := ⟨Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0⟩
    obtain ⟨e, he, hne⟩ : P (Nat.findGreatest P d) := Nat.findGreatest_spec (Nat.zero_le d) hP0
    have hmax : ∀ e' : Fin (Nat.findGreatest P d + 1) → R, OrthogonalIdempotents e' →
        (∀ i, e' i ≠ 0) → False := fun e' he' hne' =>
      Nat.findGreatest_is_greatest (Nat.lt_succ_self _) (hidem _ e' he' hne') ⟨e', he', hne'⟩
    have hsum := sum_eq_one_of_maximal_orthogonalIdempotents k R hint hnil e he hne hmax
    choose a ha using fun p : Fin (Nat.findGreatest P d) × Fin (Nat.findGreatest P d) =>
      exists_smul_eq_corner_of_maximal_orthogonalIdempotents k R hint hnil e he hne hmax p.1 p.2
    refine ⟨⟨Finset.univ.image a, eq_top_iff.mpr fun r _ => ?_⟩⟩
    have hr : r = (∑ i, e i) * r * (∑ j, e j) := by rw [hsum, one_mul, mul_one]
    rw [hr]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    refine Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c, hc⟩ := ha (i, j) r
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  refine ⟨hfin, ?_⟩
  have : IsArtinianRing R := IsArtinianRing.of_finite k R
  refine IsArtinianRing.isSemisimpleRing_iff_jacobson.mpr (eq_bot_iff.mpr fun x hx => ?_)
  rw [Submodule.mem_bot]
  refine hnil x fun y => ?_
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  have hx' : x ∈ Ideal.jacobson (⊥ : Ideal R) := by
    rw [Ring.jacobson_eq_sInf_isMaximal] at hx
    exact Submodule.mem_sInf.mpr fun J hJ => Submodule.mem_sInf.mp hx J hJ.2
  have hyx : y * x ∈ Ideal.jacobson (⊥ : Ideal R) := Ideal.mul_mem_left _ y hx'
  have := Ideal.pow_mem_pow hyx n
  rw [hn] at this
  exact ⟨n, by simpa using this⟩

end GlobalTheory.AlgRing
