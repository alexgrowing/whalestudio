import Mathlib

namespace GlobalTheory.PerfectCompletion

section General

variable {V : Type} [CommRing V] (x : V)

theorem eval_eq_zero_iff (n : ℕ) (y : AdicCompletion (Ideal.span {x}) V) :
    AdicCompletion.eval (Ideal.span {x}) V n y = 0 ↔
      (algebraMap V (AdicCompletion (Ideal.span {x}) V) x) ^ n ∣ y := by
  rw [← LinearMap.mem_ker, ← AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton x),
    Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨b, -, rfl⟩
    exact ⟨b, by rw [Algebra.smul_def, map_pow]⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, trivial, by rw [Algebra.smul_def, map_pow]⟩

theorem complete :
    IsAdicComplete (Ideal.span {algebraMap V (AdicCompletion (Ideal.span {x}) V) x})
      (AdicCompletion (Ideal.span {x}) V) := by
  have h := AdicCompletion.isAdicComplete (M := V) (Submodule.fg_span_singleton x)
  rw [← IsAdicComplete.map_algebraMap_iff (S := AdicCompletion (Ideal.span {x}) V),
    Ideal.map_span, Set.image_singleton] at h
  exact h

theorem dense (y : AdicCompletion (Ideal.span {x}) V) (r : ℕ) :
    ∃ (s : V) (z : AdicCompletion (Ideal.span {x}) V),
      y = algebraMap V _ s + (algebraMap V (AdicCompletion (Ideal.span {x}) V) x) ^ r * z := by
  obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (Ideal.span {x}) V r y)
  have : AdicCompletion.eval (Ideal.span {x}) V r (y - algebraMap V _ s) = 0 := by
    rw [map_sub, ← hs, sub_eq_zero]
    rfl
  obtain ⟨z, hz⟩ := (eval_eq_zero_iff x r _).1 this
  exact ⟨s, z, by rw [← hz]; ring⟩

theorem dvd_iff (s : V) (r : ℕ) :
    (algebraMap V (AdicCompletion (Ideal.span {x}) V) x) ^ r ∣ algebraMap V _ s ↔ x ^ r ∣ s := by
  rw [← eval_eq_zero_iff]
  have : AdicCompletion.eval (Ideal.span {x}) V r (algebraMap V _ s) =
      Submodule.Quotient.mk s := rfl
  rw [this, Submodule.Quotient.mk_eq_zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]

theorem sModEq_iff {C : Type} [CommRing C] (c : C) (n : ℕ) (u v : C) :
    u ≡ v [SMOD (Ideal.span {c} ^ n • ⊤ : Submodule C C)] ↔ c ^ n ∣ u - v := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]

end General

section Perfect

variable (l : ℕ) [Fact l.Prime] {V : Type} [CommRing V] [CharP V l] [PerfectRing V l]

theorem pow_root (c : V) : ((frobeniusEquiv V l).symm c) ^ l = c := by
  have := (frobeniusEquiv V l).apply_symm_apply c
  rwa [frobeniusEquiv_apply, frobenius_def] at this

theorem dvd_of_pow_dvd_pow (x s : V) (n : ℕ) (h : x ^ (l * n) ∣ s ^ l) : x ^ n ∣ s := by
  obtain ⟨c, hc⟩ := h
  refine ⟨(frobeniusEquiv V l).symm c, (frobeniusEquiv V l).injective ?_⟩
  rw [frobeniusEquiv_apply, frobeniusEquiv_apply, frobenius_def, frobenius_def, hc, mul_pow,
    pow_root, ← pow_mul, mul_comm n l]

end Perfect

theorem perfect : ∀ (l : ℕ) [Fact l.Prime] (V : Type) [CommRing V] [CharP V l]
    [PerfectRing V l] (x : V), ((l : ℕ) : AdicCompletion (Ideal.span {x}) V) = 0 ∧
      Function.Bijective fun y : AdicCompletion (Ideal.span {x}) V => y ^ l := by
  intro l hl V _ _ _ x
  set C := AdicCompletion (Ideal.span {x}) V
  set X := algebraMap V C x with hX
  have h0 : ((l : ℕ) : C) = 0 := by
    rw [← map_natCast (algebraMap V C), CharP.cast_eq_zero, map_zero]
  refine ⟨h0, ?_⟩
  rcases subsingleton_or_nontrivial C with hC | hC
  · exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨y, Subsingleton.elim _ _⟩⟩
  haveI : CharP C l := (CharP.charP_iff_prime_eq_zero hl.out).mpr h0
  have hl0 : l ≠ 0 := hl.out.ne_zero
  have hle : ∀ n : ℕ, n ≤ l * n := fun n => Nat.le_mul_of_pos_left n hl.out.pos
  refine ⟨fun y z hyz => ?_, fun y => ?_⟩
  ·
    have hw : (y - z) ^ l = 0 := by
      simp only at hyz
      rw [sub_pow_char, hyz, sub_self]
    rw [← sub_eq_zero]
    set w := y - z
    refine AdicCompletion.ext fun n => ?_
    rw [← AdicCompletion.eval_apply, ← AdicCompletion.eval_apply, map_zero, eval_eq_zero_iff]
    obtain ⟨s, t, hst⟩ := dense x w (l * n)
    have h1 : X ^ (l * n) ∣ algebraMap V C (s ^ l) := by
      have e : algebraMap V C (s ^ l) = -((X ^ (l * n)) ^ l * t ^ l) := by
        rw [map_pow, eq_neg_iff_add_eq_zero, ← mul_pow, ← add_pow_char, ← hst, hw]
      rw [e, dvd_neg]
      exact dvd_mul_of_dvd_left (dvd_pow_self _ hl0) _
    rw [dvd_iff] at h1
    have h2 := dvd_of_pow_dvd_pow l x s n h1
    rw [hst]
    refine dvd_add ?_ (dvd_mul_of_dvd_left (pow_dvd_pow X (hle n)) _)
    rw [dvd_iff]
    exact h2
  ·
    choose s t hst using fun n => dense x y (l * n)
    set b : ℕ → V := fun n => (frobeniusEquiv V l).symm (s n) with hb
    have hbs : ∀ n, b n ^ l = s n := fun n => pow_root l (s n)
    have hcau : ∀ {m n : ℕ}, m ≤ n →
        algebraMap V C (b m) ≡ algebraMap V C (b n) [SMOD (Ideal.span {X} ^ m • ⊤ : Submodule C C)] := by
      intro m n hmn
      rw [sModEq_iff, ← map_sub, dvd_iff]
      refine dvd_of_pow_dvd_pow l x _ m ?_
      rw [sub_pow_char, hbs, hbs, ← dvd_iff, map_sub]
      have e : algebraMap V C (s m) - algebraMap V C (s n) = X ^ (l * n) * t n - X ^ (l * m) * t m := by
        have := hst m; have := hst n; linear_combination hst n - hst m
      rw [e]
      exact dvd_sub (dvd_mul_of_dvd_left (pow_dvd_pow X (Nat.mul_le_mul_left l hmn)) _)
        (dvd_mul_right _ _)
    obtain ⟨L, hL⟩ := (complete x).toIsPrecomplete.prec hcau
    refine ⟨L, ?_⟩
    simp only
    rw [← sub_eq_zero]
    refine (complete x).toIsHausdorff.haus _ fun n => ?_
    rw [sModEq_iff, sub_zero]
    obtain ⟨u, hu⟩ := (sModEq_iff _ _ _ _).1 (hL n)
    have e : L ^ l - y = -((X ^ n) ^ l * u ^ l) - X ^ (l * n) * t n := by
      have hL' : L = algebraMap V C (b n) - X ^ n * u := by rw [← hu]; ring
      rw [hL', sub_pow_char, ← map_pow, hbs, mul_pow]
      linear_combination -(hst n)
    rw [e]
    exact dvd_sub (dvd_neg.2 (dvd_mul_of_dvd_left (dvd_pow_self _ hl0) _))
      (dvd_mul_of_dvd_left (pow_dvd_pow X (hle n)) _)

end GlobalTheory.PerfectCompletion
