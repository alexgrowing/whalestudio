import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Target
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowLeSpanPowSup
open Polynomial

namespace GlobalTheory.CurveCompletion

theorem residue_exists (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (Q : Ideal A) (hQ : Q.IsMaximal) (c : A) :
    ∃ a : k, c - algebraMap k A a ∈ Q := by
  letI := Ideal.Quotient.field Q
  haveI : Module.Finite k (A ⧸ Q) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ Q)
  obtain ⟨a, ha⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := A ⧸ Q)).2
    (Ideal.Quotient.mk Q c)
  refine ⟨a, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← ha]
  simp [Ideal.Quotient.algebraMap_eq]

section Dedekind
variable {A : Type} [CommRing A] [IsDedekindDomain A]

theorem pow_le_span_sup {Q : Ideal A} [Q.IsPrime] (hQ : Q ≠ ⊥) {π : A} (hπ : π ∈ Q)
    (hπ2 : π ∉ Q ^ 2) : ∀ m : ℕ, Q ^ m ≤ Ideal.span {π ^ m} ⊔ Q ^ (m + 1) := by
  first
  | exact @_root_.GlobalTheory.SpanPowerSupremum.pow_le_span_pow_sup
  | exact _root_.GlobalTheory.SpanPowerSupremum.pow_le_span_pow_sup
  | (apply _root_.GlobalTheory.SpanPowerSupremum.pow_le_span_pow_sup <;> assumption)
  | (intros; apply _root_.GlobalTheory.SpanPowerSupremum.pow_le_span_pow_sup <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SpanPowerSupremum.pow_le_span_pow_sup <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SpanPowerSupremum.pow_le_span_pow_sup ..)

theorem pow_not_mem {Q : Ideal A} [Q.IsPrime] (hQ : Q ≠ ⊥) {π : A} (hπ : π ∈ Q)
    (hπ2 : π ∉ Q ^ 2) (m : ℕ) : π ^ m ∉ Q ^ (m + 1) := by
  first
  | exact @_root_.GlobalTheory.AlgebraicIntegerNormBound.main
  | exact _root_.GlobalTheory.AlgebraicIntegerNormBound.main
  | (apply _root_.GlobalTheory.AlgebraicIntegerNormBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AlgebraicIntegerNormBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AlgebraicIntegerNormBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AlgebraicIntegerNormBound.main ..)

end Dedekind

section Series
variable {k A : Type} [Field k] [CommRing A] [Algebra k A] (Q : Ideal A) (π : A)

theorem aeval_mem_of_dvd (hπ : π ∈ Q) (m : ℕ) (r : k[X]) (h : X ^ m ∣ r) :
    aeval π r ∈ Q ^ m := by
  obtain ⟨s, rfl⟩ := h
  rw [map_mul, map_pow, aeval_X]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hπ m)

theorem dvd_of_aeval_mem (hπ : π ∈ Q) (hnot : ∀ m : ℕ, π ^ m ∉ Q ^ (m + 1)) :
    ∀ (m : ℕ) (r : k[X]), aeval π r ∈ Q ^ m → X ^ m ∣ r := by
  intro m
  induction m with
  | zero => intro r _; simp
  | succ m ih =>
    intro r hr
    obtain ⟨s, rfl⟩ := ih r (Ideal.pow_le_pow_right (Nat.le_succ m) hr)
    obtain ⟨s', hs'⟩ := Polynomial.X_dvd_sub_C (p := s)
    have hs : s = C (s.coeff 0) + X * s' := by rw [← hs']; ring
    by_cases h0 : s.coeff 0 = 0
    · rw [hs, h0, map_zero, zero_add, ← mul_assoc, ← pow_succ]
      exact dvd_mul_right _ _
    · exfalso
      apply hnot m
      have e0 : aeval π s = algebraMap k A (s.coeff 0) + π * aeval π s' := by
        conv_lhs => rw [hs]
        simp [aeval_C]
      have e : aeval π (X ^ m * s) =
          π ^ m * algebraMap k A (s.coeff 0) + π ^ (m + 1) * aeval π s' := by
        rw [map_mul, map_pow, aeval_X, e0]; ring
      rw [e] at hr
      have h2 : π ^ m * algebraMap k A (s.coeff 0) ∈ Q ^ (m + 1) := by
        have h3 : π ^ (m + 1) * aeval π s' ∈ Q ^ (m + 1) :=
          Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hπ _)
        have := Ideal.sub_mem _ hr h3
        simpa using this
      have h4 := Ideal.mul_mem_right (algebraMap k A (s.coeff 0)⁻¹) _ h2
      rwa [mul_assoc, ← map_mul, mul_inv_cancel₀ h0, map_one, mul_one] at h4

theorem aeval_mem_iff (hπ : π ∈ Q) (hnot : ∀ m : ℕ, π ^ m ∉ Q ^ (m + 1)) (m : ℕ) (r : k[X]) :
    aeval π r ∈ Q ^ m ↔ X ^ m ∣ r :=
  ⟨dvd_of_aeval_mem Q π hπ hnot m r, aeval_mem_of_dvd Q π hπ m r⟩

theorem coe_dvd_iff (m : ℕ) (r : k[X]) :
    (PowerSeries.X : PowerSeries k) ^ m ∣ (r : PowerSeries k) ↔ X ^ m ∣ r := by
  rw [PowerSeries.X_pow_dvd_iff, Polynomial.X_pow_dvd_iff]
  simp [Polynomial.coeff_coe]

theorem eq_of_forall_dvd (f g : PowerSeries k)
    (h : ∀ m : ℕ, (PowerSeries.X : PowerSeries k) ^ m ∣ f - g) : f = g := by
  ext n
  have := PowerSeries.X_pow_dvd_iff.mp (h (n + 1)) n (Nat.lt_succ_self n)
  rw [map_sub, sub_eq_zero] at this
  exact this

end Series

section Construction
variable {k A : Type} [Field k] [CommRing A] [Algebra k A] (Q : Ideal A) (π : A)
  (hex : ∀ (m : ℕ) (u : A), ∃ p : k[X], u - aeval π p ∈ Q ^ m)

noncomputable def approx (m : ℕ) (u : A) : k[X] := Classical.choose (hex m u)

theorem approx_spec (m : ℕ) (u : A) : u - aeval π (approx Q π hex m u) ∈ Q ^ m :=
  Classical.choose_spec (hex m u)

noncomputable def ser (u : A) : PowerSeries k :=
  PowerSeries.mk fun n => (approx Q π hex (n + 1) u).coeff n

variable {Q π} (hπ : π ∈ Q) (hnot : ∀ m : ℕ, π ^ m ∉ Q ^ (m + 1))
include hπ hnot

theorem ser_sub_approx (m : ℕ) (u : A) :
    (PowerSeries.X : PowerSeries k) ^ m ∣ ser Q π hex u - (approx Q π hex m u : PowerSeries k) := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro n hn
  rw [map_sub, Polynomial.coeff_coe, ser, PowerSeries.coeff_mk, sub_eq_zero]
  have hmem : aeval π (approx Q π hex m u - approx Q π hex (n + 1) u) ∈ Q ^ (n + 1) := by
    have e : aeval π (approx Q π hex m u - approx Q π hex (n + 1) u) =
        (u - aeval π (approx Q π hex (n + 1) u)) - (u - aeval π (approx Q π hex m u)) := by
      rw [map_sub]; ring
    rw [e]
    exact Ideal.sub_mem _ (approx_spec Q π hex _ u)
      (Ideal.pow_le_pow_right hn (approx_spec Q π hex m u))
  have hd := (Polynomial.X_pow_dvd_iff).mp (dvd_of_aeval_mem Q π hπ hnot _ _ hmem) n
    (Nat.lt_succ_self n)
  rw [Polynomial.coeff_sub, sub_eq_zero] at hd
  exact hd.symm

theorem mem_iff_dvd (m : ℕ) (u : A) (p : k[X]) :
    u - aeval π p ∈ Q ^ m ↔
      (PowerSeries.X : PowerSeries k) ^ m ∣ ser Q π hex u - (p : PowerSeries k) := by
  set q := approx Q π hex m u
  have e1 : u - aeval π p = (u - aeval π q) + aeval π (q - p) := by rw [map_sub]; ring
  have e2 : ser Q π hex u - (p : PowerSeries k) =
      (ser Q π hex u - (q : PowerSeries k)) + ((q - p : k[X]) : PowerSeries k) := by
    rw [Polynomial.coe_sub]; ring
  rw [e1, Ideal.add_mem_iff_right _ (approx_spec Q π hex m u), e2,
    (dvd_add_right (ser_sub_approx hex hπ hnot m u)), coe_dvd_iff,
    aeval_mem_iff Q π hπ hnot]

theorem ser_eq (u : A) (f : PowerSeries k)
    (h : ∀ m : ℕ, ∃ p : k[X], u - aeval π p ∈ Q ^ m ∧
      (PowerSeries.X : PowerSeries k) ^ m ∣ f - (p : PowerSeries k)) :
    ser Q π hex u = f := by
  apply eq_of_forall_dvd
  intro m
  obtain ⟨p, hp, hd⟩ := h m
  have := dvd_sub ((mem_iff_dvd hex hπ hnot m u p).mp hp) hd
  rwa [sub_sub_sub_cancel_right] at this

noncomputable def serHom : A →ₐ[k] PowerSeries k where
  toFun := ser Q π hex
  map_one' := ser_eq hex hπ hnot 1 1 fun m => ⟨1, by simp, by simp⟩
  map_zero' := ser_eq hex hπ hnot 0 0 fun m => ⟨0, by simp, by simp⟩
  map_add' u v := by
    apply ser_eq hex hπ hnot
    intro m
    refine ⟨approx Q π hex m u + approx Q π hex m v, ?_, ?_⟩
    · have e : u + v - aeval π (approx Q π hex m u + approx Q π hex m v) =
          (u - aeval π (approx Q π hex m u)) + (v - aeval π (approx Q π hex m v)) := by
        rw [map_add]; ring
      rw [e]
      exact Ideal.add_mem _ (approx_spec Q π hex m u) (approx_spec Q π hex m v)
    · have e : ser Q π hex u + ser Q π hex v -
          ((approx Q π hex m u + approx Q π hex m v : k[X]) : PowerSeries k) =
          (ser Q π hex u - (approx Q π hex m u : PowerSeries k)) +
            (ser Q π hex v - (approx Q π hex m v : PowerSeries k)) := by
        rw [Polynomial.coe_add]; ring
      rw [e]
      exact dvd_add (ser_sub_approx hex hπ hnot m u) (ser_sub_approx hex hπ hnot m v)
  map_mul' u v := by
    apply ser_eq hex hπ hnot
    intro m
    refine ⟨approx Q π hex m u * approx Q π hex m v, ?_, ?_⟩
    · have e : u * v - aeval π (approx Q π hex m u * approx Q π hex m v) =
          (u - aeval π (approx Q π hex m u)) * v +
            aeval π (approx Q π hex m u) * (v - aeval π (approx Q π hex m v)) := by
        rw [map_mul]; ring
      rw [e]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (approx_spec Q π hex m u))
        (Ideal.mul_mem_left _ _ (approx_spec Q π hex m v))
    · have e : ser Q π hex u * ser Q π hex v -
          ((approx Q π hex m u * approx Q π hex m v : k[X]) : PowerSeries k) =
          (ser Q π hex u - (approx Q π hex m u : PowerSeries k)) * ser Q π hex v +
            (approx Q π hex m u : PowerSeries k) *
              (ser Q π hex v - (approx Q π hex m v : PowerSeries k)) := by
        rw [Polynomial.coe_mul]; ring
      rw [e]
      exact dvd_add (Dvd.dvd.mul_right (ser_sub_approx hex hπ hnot m u) _)
        (Dvd.dvd.mul_left (ser_sub_approx hex hπ hnot m v) _)
  commutes' c := by
    apply ser_eq hex hπ hnot
    intro m
    exact ⟨C c, by simp, by simp⟩

end Construction

section Existence
variable {k A : Type} [Field k] [CommRing A] [Algebra k A] {Q : Ideal A} {π : A}

theorem exists_approx (hπ : π ∈ Q) (hres : ∀ c : A, ∃ a : k, c - algebraMap k A a ∈ Q)
    (hsup : ∀ m : ℕ, Q ^ m ≤ Ideal.span {π ^ m} ⊔ Q ^ (m + 1)) :
    ∀ (m : ℕ) (u : A), ∃ p : k[X], u - aeval π p ∈ Q ^ m := by
  first
  | exact @_root_.GlobalTheory.IntegralNormBound.target
  | exact _root_.GlobalTheory.IntegralNormBound.target
  | (apply _root_.GlobalTheory.IntegralNormBound.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralNormBound.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralNormBound.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralNormBound.target ..)

end Existence

theorem exists_completion_embedding : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k]
    [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (Q : Ideal A),
    Q.IsMaximal → Q ≠ ⊥ → ∃ (σ : A →ₐ[k] PowerSeries k) (π : A), σ π = PowerSeries.X ∧
      Function.Injective σ ∧
      (∀ (m : ℕ) (u : A), u ∈ Q ^ m ↔ (PowerSeries.X : PowerSeries k) ^ m ∣ σ u) ∧
      ∀ (m : ℕ) (φ : PowerSeries k), ∃ u : A,
        (PowerSeries.X : PowerSeries k) ^ m ∣ φ - σ u := by
  intro k A _ _ _ _ _ _ _ Q hQ hQ0
  haveI : Q.IsPrime := hQ.isPrime
  obtain ⟨π, hπ1, hπ2⟩ := SetLike.exists_of_lt (Ideal.pow_succ_lt_pow hQ0 1)
  have hπ : π ∈ Q := by simpa using hπ1
  have hnot := pow_not_mem hQ0 hπ hπ2
  have hex := exists_approx (k := k) hπ (residue_exists k A Q hQ) (pow_le_span_sup hQ0 hπ hπ2)
  have hmem : ∀ (m : ℕ) (u : A),
      u ∈ Q ^ m ↔ (PowerSeries.X : PowerSeries k) ^ m ∣ serHom hex hπ hnot u := by
    intro m u
    have := mem_iff_dvd hex hπ hnot m u 0
    change u ∈ Q ^ m ↔ (PowerSeries.X : PowerSeries k) ^ m ∣ ser Q π hex u
    simpa using this
  refine ⟨serHom hex hπ hnot, π, ?_, ?_, hmem, ?_⟩
  · exact ser_eq hex hπ hnot π PowerSeries.X fun m => ⟨X, by simp, by simp⟩
  · rw [injective_iff_map_eq_zero]
    intro u hu
    have hall : ∀ m : ℕ, u ∈ Q ^ m := fun m => (hmem m u).mpr (by rw [hu]; exact dvd_zero _)
    have hbot := Ideal.iInf_pow_eq_bot_of_isDomain Q hQ.ne_top
    have : u ∈ ⨅ i, Q ^ i := Submodule.mem_iInf _ |>.mpr hall
    rw [hbot] at this
    exact (Submodule.mem_bot A).mp this
  · intro m φ
    refine ⟨aeval π (PowerSeries.trunc m φ), ?_⟩
    have h1 := (mem_iff_dvd hex hπ hnot m (aeval π (PowerSeries.trunc m φ))
      (PowerSeries.trunc m φ)).mp (by simp)
    have h2 : (PowerSeries.X : PowerSeries k) ^ m ∣ φ - (PowerSeries.trunc m φ : PowerSeries k) := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro n hn
      rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hn, sub_self]
    have := dvd_sub h2 h1
    rwa [sub_sub_sub_cancel_right] at this

end GlobalTheory.CurveCompletion
