import Mathlib

noncomputable section

open NumberField

namespace PositivityTheory.HtPt.Kftwo

structure Biq (F : Type) [Field F] [CharZero F] (m : ℕ) where

  w : F

  i : F
  w_sq : w * w = w - m
  i_sq : i * i = -1
  span : ∀ x : F, ∃ a b c e : ℚ, x = a + b * w + c * i + e * (w * i)
  indep : ∀ a b c e : ℚ, (a : F) + b * w + c * i + e * (w * i) = 0 → a = 0 ∧ b = 0 ∧ c = 0 ∧ e = 0

  σ : F →+* F

  τ : F →+* F
  σw : σ w = w
  σi : σ i = -i
  τw : τ w = 1 - w
  τi : τ i = i

section Exists

variable (m : ℕ)

abbrev Q1 : Type := QuadraticAlgebra ℚ (-(m : ℚ)) 1

abbrev Q2 : Type := QuadraticAlgebra (Q1 m) (-1) 0

attribute [local simp] QuadraticAlgebra.re_one QuadraticAlgebra.im_one

theorem fact1 (hm : 0 < m) : ∀ r : ℚ, r ^ 2 ≠ -(m : ℚ) + 1 * r := fun r h => by
  have : (1 : ℚ) ≤ m := by exact_mod_cast hm
  nlinarith [sq_nonneg (r - 1 / 2)]

theorem fact2 (hp : (4 * m - 1).Prime) (r : Q1 m) : r ^ 2 ≠ -1 + 0 * r := fun h => by
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp [Nat.not_prime_zero] at hp
    · exact h
  have h1 := congrArg QuadraticAlgebra.re h
  have h2 := congrArg QuadraticAlgebra.im h
  simp [pow_two] at h1 h2
  have hb : r.im ≠ 0 := fun h0 => by
    rw [h0] at h1
    nlinarith [sq_nonneg r.re]
  have ha : r.im = -2 * r.re := by
    have : r.im * (r.im + 2 * r.re) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hb
    · linear_combination h
  have hr : r.re ≠ 0 := fun h0 => hb (by rw [ha, h0, mul_zero])
  have hd : ((4 * m - 1 : ℕ) : ℚ) = (1 / r.re) * (1 / r.re) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    field_simp
    rw [ha] at h1
    linear_combination -h1
  have hs : IsSquare ((4 * m - 1 : ℕ) : ℚ) := ⟨_, hd⟩
  exact hp.not_isSquare (Rat.isSquare_natCast_iff.1 hs)

theorem exists_biq (hp : (4 * m - 1).Prime) :
    ∃ (F : Type) (_ : Field F) (_ : CharZero F), Nonempty (Biq F m) := by
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp [Nat.not_prime_zero] at hp
    · exact h
  have := Fact.mk (fact1 m hm)
  have := Fact.mk (fact2 m hp)
  have hc : ∀ a : ℚ, (a : (Q2 m)) = ⟨⟨a, 0⟩, 0⟩ := fun a => by
    have := map_ratCast ((algebraMap (Q1 m) (Q2 m)).comp (algebraMap ℚ (Q1 m))) a
    rw [← this]; rfl
  let τ : (Q2 m) →+* (Q2 m) :=
    { toFun := fun z => ⟨star z.re, star z.im⟩
      map_one' := by ext1 <;> simp
      map_zero' := by ext1 <;> simp
      map_add' := fun x y => by ext1 <;> simp
      map_mul' := fun x y => by ext1 <;> simp }
  refine ⟨(Q2 m), inferInstance, inferInstance, ⟨⟨⟨⟨0, 1⟩, 0⟩, ⟨0, 1⟩, ?_, ?_, fun x => ?_, fun a b c e h => ?_,
    starRingEnd (Q2 m), τ, ?_, ?_, ?_, ?_⟩⟩⟩
  · ext <;> simp
  · ext <;> simp
  · refine ⟨x.re.re, x.re.im, x.im.re, x.im.im, ?_⟩
    simp only [hc]
    ext <;> simp
  · simp only [hc] at h
    have h1 := congrArg (fun z : (Q2 m) => z.re.re) h
    have h2 := congrArg (fun z : (Q2 m) => z.re.im) h
    have h3 := congrArg (fun z : (Q2 m) => z.im.re) h
    have h4 := congrArg (fun z : (Q2 m) => z.im.im) h
    simp at h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  · rw [starRingEnd_apply]; ext <;> simp
  · rw [starRingEnd_apply]; ext <;> simp
  · ext <;> simp [τ]
  · ext <;> simp [τ]

end Exists

namespace Biq

variable {F : Type} [Field F] [CharZero F] {m : ℕ} (B : Biq F m)

theorem int_of_integral {q : ℚ} (h : IsIntegral ℤ (q : F)) : ∃ n : ℤ, q = n := by
  have h' : IsIntegral ℤ (algebraMap ℚ F q) := by simpa using h
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (isIntegral_algebraMap_iff (algebraMap ℚ F).injective |>.1 h')
  exact ⟨n, by simpa using hn.symm⟩

omit [CharZero F] in
theorem of_eq {x y : F} (h : IsIntegral ℤ x) (e : y = x) : IsIntegral ℤ y := e ▸ h

omit [CharZero F] in
theorem integral_map {x : F} (f : F →+* F) (h : IsIntegral ℤ x) : IsIntegral ℤ (f x) := h.map f.toIntAlgHom

omit [CharZero F] in
theorem integral_int (n : ℤ) : IsIntegral ℤ (n : F) := by
  simpa using isIntegral_algebraMap (R := ℤ) (A := F) (x := n)

theorem integral_w : IsIntegral ℤ B.w :=
  ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), by monicity!, by
    simp [Polynomial.eval₂_add, Polynomial.eval₂_sub]; linear_combination B.w_sq⟩

theorem integral_i : IsIntegral ℤ B.i :=
  ⟨Polynomial.X ^ 2 + 1, by monicity!, by simp; linear_combination B.i_sq⟩

theorem gauss {u v : ℚ} (h : IsIntegral ℤ ((u : F) + v * B.i)) : (∃ n : ℤ, u = n) ∧ ∃ n : ℤ, v = n := by
  have h' := integral_map B.σ h
  simp only [map_add, map_mul, map_ratCast, B.σi] at h'
  obtain ⟨p, hp⟩ := int_of_integral (F := F) (q := 2 * u) (by
    refine of_eq (h.add h') ?_; push_cast; ring)
  obtain ⟨q, hq⟩ := int_of_integral (F := F) (q := 2 * v) (by
    refine of_eq ((h'.sub h).mul B.integral_i) ?_; push_cast; linear_combination (2 * v : F) * B.i_sq)
  obtain ⟨n, hn⟩ := int_of_integral (F := F) (q := u ^ 2 + v ^ 2) (by
    refine of_eq (h.mul h') ?_; push_cast; linear_combination (v : F) ^ 2 * B.i_sq)
  have e : p ^ 2 + q ^ 2 = 4 * n := by
    have : (p : ℚ) ^ 2 + q ^ 2 = 4 * n := by rw [← hp, ← hq, ← hn]; ring
    exact_mod_cast this
  have hpq : Even p ∧ Even q := by
    rcases Int.even_or_odd' p with ⟨s, rfl | rfl⟩ <;> rcases Int.even_or_odd' q with ⟨t, rfl | rfl⟩
    · simp
    · exfalso; have : 4 * (s ^ 2 + t ^ 2 + t - n) + 1 = 0 := by linear_combination e
      omega
    · exfalso; have : 4 * (s ^ 2 + t ^ 2 + s - n) + 1 = 0 := by linear_combination e
      omega
    · exfalso; have : 4 * (s ^ 2 + t ^ 2 + s + t - n) + 2 = 0 := by linear_combination e
      omega
  obtain ⟨⟨s, rfl⟩, ⟨t, rfl⟩⟩ := hpq
  push_cast at hp hq
  exact ⟨⟨s, by linarith⟩, t, by linarith⟩

theorem quad {d : ℕ} (hd : d + 1 = 4 * m) (hp : d.Prime) {a b : ℚ} {r s : ℤ} (hr : d * a = r) (hs : d * b = s)
    (h : IsIntegral ℤ ((a : F) + b * B.w)) : (∃ n : ℤ, a = n) ∧ ∃ n : ℤ, b = n := by
  have h' := integral_map B.τ h
  simp only [map_add, map_mul, map_ratCast, B.τw] at h'
  obtain ⟨p, hp'⟩ := int_of_integral (F := F) (q := 2 * a + b) (by
    refine of_eq (h.add h') ?_; push_cast; ring)
  obtain ⟨n, hn⟩ := int_of_integral (F := F) (q := a ^ 2 + a * b + m * b ^ 2) (by
    refine of_eq (h.mul h') ?_; push_cast; linear_combination (b : F) ^ 2 * B.w_sq)
  have hdq : (d : ℚ) + 1 = 4 * m := by exact_mod_cast hd
  have e : s ^ 2 = d * (4 * n - p ^ 2) := by
    have : (s : ℚ) ^ 2 = d * (4 * n - p ^ 2) := by
      rw [← hs, ← hn, ← hp']; linear_combination (d * b ^ 2 : ℚ) * hdq
    exact_mod_cast this
  obtain ⟨t, rfl⟩ : (d : ℤ) ∣ s := (Nat.prime_iff_prime_int.1 hp).dvd_of_dvd_pow ⟨_, e⟩
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hb : b = t := by push_cast at hs; exact mul_left_cancel₀ hd0 hs
  refine ⟨⟨2 * m * (p - t) - r, ?_⟩, t, hb⟩
  push_cast
  rw [← hp', ← hr, ← hb]
  linear_combination a * hdq

theorem coords {d : ℕ} (hd : d + 1 = 4 * m) (hp : d.Prime) {x : F} (h : IsIntegral ℤ x) :
    ∃ a b c e : ℤ, x = a + b * B.w + c * B.i + e * (B.w * B.i) := by
  obtain ⟨a, b, c, e, rfl⟩ := B.span x
  have hdF : (d : F) = 4 * m - 1 := by
    have : (d : F) + 1 = 4 * m := by exact_mod_cast hd
    linear_combination this
  have h1 := integral_map B.τ h
  have h2 := integral_map B.σ h
  simp only [map_add, map_mul, map_ratCast, B.τw, B.τi, B.σw, B.σi] at h1 h2
  have hw := B.integral_w
  have hi := B.integral_i
  obtain ⟨⟨b', hb⟩, e', he⟩ := B.gauss (u := d * b) (v := d * e) (by
    refine of_eq ((h1.sub h).mul ((hw.add hw).sub isIntegral_one)) ?_
    push_cast; rw [hdF]; linear_combination (4 * (b + e * B.i) : F) * B.w_sq)
  have hbF : (b' : F) = d * b := by exact_mod_cast congrArg (fun q : ℚ => (q : F)) hb.symm
  have heF : (e' : F) = d * e := by exact_mod_cast congrArg (fun q : ℚ => (q : F)) he.symm
  obtain ⟨⟨a', ha⟩, c', hc⟩ := B.gauss (u := d * a) (v := d * c) (by
    refine of_eq ((((integral_int (d : ℤ)).mul h).sub ((integral_int b').mul hw)).sub
      ((integral_int e').mul (hw.mul hi))) ?_
    push_cast; rw [hbF, heF]; ring)
  have haF : (a' : F) = d * a := by exact_mod_cast congrArg (fun q : ℚ => (q : F)) ha.symm
  have hα : IsIntegral ℤ ((a : F) + b * B.w) := by
    refine of_eq (((integral_int (2 * m : ℤ)).mul (h.add h2)).sub ((integral_int a').add ((integral_int b').mul hw))) ?_
    push_cast; rw [haF, hbF, hdF]; ring
  have hβ : IsIntegral ℤ ((c : F) + e * B.w) := by
    refine of_eq ((hα.sub h).mul hi) ?_
    linear_combination (c + e * B.w : F) * B.i_sq
  obtain ⟨⟨a, rfl⟩, b, rfl⟩ := B.quad hd hp ha hb hα
  obtain ⟨⟨c, rfl⟩, e, rfl⟩ := B.quad hd hp hc he hβ
  exact ⟨a, b, c, e, by simp⟩

include B in
theorem numberField : NumberField F := by
  classical
  have : Module.Finite ℚ F := by
    refine ⟨⟨{1, B.w, B.i, B.w * B.i}, eq_top_iff.2 fun x _ => ?_⟩⟩
    obtain ⟨a, b, c, e, rfl⟩ := B.span x
    have k : ∀ (q : ℚ) (y : F), y ∈ ({1, B.w, B.i, B.w * B.i} : Finset F) →
        (q : F) * y ∈ Submodule.span ℚ (({1, B.w, B.i, B.w * B.i} : Finset F) : Set F) := fun q y hy => by
      rw [← Rat.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hy)
    refine add_mem (add_mem (add_mem ?_ (k _ _ (by simp))) (k _ _ (by simp))) (k _ _ (by simp))
    simpa using k a 1 (by simp)
  exact {}

theorem conj_w (hm : 0 < m) (φ : F →+* ℂ) : starRingEnd ℂ (φ B.w) = 1 - φ B.w := by
  have h := congrArg φ B.w_sq
  simp only [map_mul, map_sub, map_natCast] at h
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp at h1 h2
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hv : (φ B.w).im ≠ 0 := fun h0 => by
    rw [h0] at h1
    nlinarith [sq_nonneg ((φ B.w).re - 1 / 2)]
  have : (φ B.w).im * (2 * (φ B.w).re - 1) = 0 := by linear_combination h2
  have hu := (mul_eq_zero.1 this).resolve_left hv
  apply Complex.ext <;> simp
  linarith

theorem conj_i (φ : F →+* ℂ) : starRingEnd ℂ (φ B.i) = -φ B.i := by
  have h := congrArg φ B.i_sq
  simp only [map_mul, map_neg, map_one] at h
  have : (φ B.i - Complex.I) * (φ B.i + Complex.I) = 0 := by linear_combination h - Complex.I_mul_I
  rcases mul_eq_zero.1 this with h | h
  · rw [sub_eq_zero.1 h, Complex.conj_I]
  · rw [eq_neg_of_add_eq_zero_left h, map_neg, Complex.conj_I]

theorem conj_eq (hm : 0 < m) (φ : F →+* ℂ) (x : F) : φ (B.σ (B.τ x)) = starRingEnd ℂ (φ x) := by
  obtain ⟨a, b, c, e, rfl⟩ := B.span x
  simp only [map_add, map_mul, map_ratCast, B.τw, B.τi, B.σw, B.σi, map_sub, map_one, map_neg, B.conj_w hm, B.conj_i]

theorem mem_real (hm : 0 < m) {x : F} (h : B.σ (B.τ x) = x) : x ∈ maximalRealSubfield F := by
  rw [mem_maximalRealSubfield_iff]
  intro φ
  rw [RCLike.star_def, ← B.conj_eq hm, h]

theorem i_ne_zero : B.i ≠ 0 := fun h => by simpa [h] using B.i_sq

include B in
theorem isCMField (hm : 0 < m) : IsCMField F := by
  have := B.numberField
  have hT : IsTotallyComplex F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff]
    intro h
    have h1 := RingHom.congr_fun h B.i
    rw [ComplexEmbedding.conjugate_coe_eq, B.conj_i] at h1
    exact B.i_ne_zero (v.embedding.injective (by rw [map_zero]; linear_combination (-1 / 2 : ℂ) * h1))⟩
  have hc : ∀ x, B.σ (B.τ (B.σ (B.τ x))) = x := fun x => by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    apply φ.injective
    rw [B.conj_eq hm, B.conj_eq hm, Complex.conj_conj]
  have hli : LinearIndependent (maximalRealSubfield F) ![(1 : F), B.i] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 : (s : F) + t * B.i = 0 := by simpa [Subfield.smul_def] using h
    have h1 := congrArg φ h0
    have h2 := congrArg (starRingEnd ℂ) h1
    have hs := (mem_maximalRealSubfield_iff _).1 s.2 φ
    have ht := (mem_maximalRealSubfield_iff _).1 t.2 φ
    rw [RCLike.star_def] at hs ht
    simp only [map_add, map_mul, map_zero, hs, ht, B.conj_i] at h1 h2
    have e1 : (s : F) = 0 := φ.injective (by rw [map_zero]; linear_combination (1 / 2 : ℂ) * (h1 + h2))
    rw [e1, zero_add] at h0
    exact ⟨Subtype.ext e1, Subtype.ext ((mul_eq_zero.1 h0).resolve_right B.i_ne_zero)⟩
  have hsp : ⊤ ≤ Submodule.span (maximalRealSubfield F) (Set.range ![(1 : F), B.i]) := fun x _ => by
    rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair]
    refine ⟨⟨(x + B.σ (B.τ x)) / 2, B.mem_real hm ?_⟩, ⟨(B.σ (B.τ x) - x) * B.i / 2, B.mem_real hm ?_⟩, ?_⟩
    · simp only [map_div₀, map_add, map_ofNat, hc]; ring
    · simp only [map_div₀, map_sub, map_mul, map_ofNat, hc, B.τi, B.σi]; ring
    · simp only [Subfield.smul_def, smul_eq_mul]
      linear_combination ((B.σ (B.τ x) - x) / 2) * B.i_sq
  have : Algebra.IsQuadraticExtension (maximalRealSubfield F) F :=
    { finrank_eq_two' := by simpa using Module.finrank_eq_card_basis (Module.Basis.mk hli hsp) }
  exact {}

end Biq

end PositivityTheory.HtPt.Kftwo
