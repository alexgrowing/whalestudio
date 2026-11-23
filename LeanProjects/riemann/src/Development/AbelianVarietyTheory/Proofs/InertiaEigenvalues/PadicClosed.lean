import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixFrobeniusSubOneBijectiveModSubring

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Decompl

namespace GlobalTheory.HWL.Rational

section Abstract

variable {R E B : Type} [CommRing R] [CommRing E] [CommRing B] {p : ℕ}

theorem sat_pow (j : E →+* R) (htf : ∀ x : R, (p : R) * x = 0 → x = 0)
    (hs : ∀ (x : E) (y : R), j x = (p : R) * y → ∃ x', x = (p : E) * x')
    (k : ℕ) : ∀ (x : E) (y : R), j x = (p : R) ^ k * y → ∃ x', x = (p : E) ^ k * x' := by
  induction k with
  | zero => intro x _ _; exact ⟨x, by ring⟩
  | succ k ih =>
    intro x y h
    obtain ⟨x', rfl⟩ := hs x ((p : R) ^ k * y) (by rw [h]; ring)
    rw [map_mul, map_natCast] at h
    obtain ⟨x'', rfl⟩ := ih x' y (sub_eq_zero.mp (htf _ (by linear_combination h)))
    exact ⟨x'', by ring⟩

theorem sat_range (j : E →+* R) (htf : ∀ x : R, (p : R) * x = 0 → x = 0)
    (hs : ∀ (x : E) (y : R), j x = (p : R) * y → ∃ x', x = (p : E) * x')
    (x : R) (e : E) (he : (p : R) * x = j e) : ∃ e', x = j e' := by
  obtain ⟨e', rfl⟩ := hs e x he.symm
  refine ⟨e', sub_eq_zero.mp (htf _ ?_)⟩
  rw [map_mul, map_natCast] at he
  linear_combination he

private theorem pow_top_lemma (m : ℕ) (z : E) :
    z ∈ (Ideal.span {(p : E)} ^ m • ⊤ : Submodule E E) ↔ ∃ c, z = (p : E) ^ m * c := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact Iff.rfl

theorem padic_closed (j : E →+* R) (htf : ∀ x : R, (p : R) * x = 0 → x = 0)
    (hsep : ∀ x : R, (∀ k : ℕ, ∃ r, x = (p : R) ^ k * r) → x = 0)
    (hs : ∀ (x : E) (y : R), j x = (p : R) * y → ∃ x', x = (p : E) * x')
    (hc : IsAdicComplete (Ideal.span {(p : E)}) E)
    (x : R) (hx : ∀ k : ℕ, ∃ e r, x - j e = (p : R) ^ k * r) : ∃ e, x = j e := by
  choose e r hr using hx
  have hcs : ∀ {m n : ℕ}, m ≤ n →
      e m ≡ e n [SMOD (Ideal.span {(p : E)} ^ m • ⊤ : Submodule E E)] := by
    intro m n hmn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [SModEq.sub_mem, pow_top_lemma]
    exact sat_pow j htf hs m _ (r (m + k) * (p : R) ^ k - r m)
      (by rw [map_sub]; linear_combination hr (m + k) - hr m)
  obtain ⟨L, hL⟩ := hc.toIsPrecomplete.prec hcs
  refine ⟨L, sub_eq_zero.mp (hsep _ fun k => ?_)⟩
  have hk := hL k
  rw [SModEq.sub_mem, pow_top_lemma] at hk
  obtain ⟨c, hc'⟩ := hk
  have hjc := congrArg j hc'
  rw [map_sub, map_mul, map_pow, map_natCast] at hjc
  exact ⟨r k + j c, by linear_combination hr k + hjc⟩

theorem idem_pow {ε : R} (h : ε * ε = ε) (n : ℕ) : ε ^ (n + 1) = ε := by
  induction n with
  | zero => exact pow_one ε
  | succ n ih => rw [pow_succ, ih, h]

theorem idem_eq_zero (ι : B →+* R) (τ : B) (hu : IsUnit (ι τ)) (hinj : Function.Injective ι)
    (htf : ∀ x : R, (p : R) * x = 0 → x = 0)
    (hsep : ∀ x : R, (∀ k : ℕ, ∃ r, x = (p : R) ^ k * r) → x = 0)
    (hsat : ∀ (y : B) (x : R), ι y = (p : R) * x → ∃ y', ι y' = x)
    (hnear : ∀ x : R, (∀ m, Near ι p (ι τ) m x) → ∃ r, x = (p : R) * r)
    (ε c d w : B) (N : ℕ) (hε : ε * ε = ε) (hcd : (p : B) = c * d) (hd : d ^ (N + 1) = (p : B) * w)
    (h : Near ι p (ι τ) 1 (ι (c * ε))) : ε = 0 := by
  obtain ⟨u, hu'⟩ := hu
  have hinv : (↑u⁻¹ : R) * ι τ = 1 := by rw [← hu', Units.inv_mul]
  have hinv2 : ι τ * (↑u⁻¹ : R) = 1 := by rw [← hu', Units.mul_inv]
  obtain ⟨a, r, har⟩ := h
  obtain ⟨r0, hr0⟩ := hsat (c * ε - τ * a) r (by rw [map_sub, har, map_mul]; ring)
  have h1 : c * ε = τ * a + (p : B) * r0 := hinj (by
    rw [har]
    simp only [map_add, map_mul, map_natCast, hr0]
    ring)
  have h2 : (p : B) * ε = τ * (d * a) + (p : B) * (d * r0) := by
    linear_combination d * h1 + ε * hcd
  have h3 := congrArg ι h2
  simp only [map_add, map_mul, map_natCast] at h3
  obtain ⟨s, hs⟩ := hsat (d * a) (↑u⁻¹ * (ι ε - ι d * ι r0)) (by
    rw [map_mul]
    linear_combination (-(↑u⁻¹ : R)) * h3 - ι d * ι a * hinv)
  have h5 : ε = d * r0 + τ * s := by
    have h4 : ι ε = ι (d * r0 + τ * s) := by
      rw [map_add, map_mul, map_mul, hs]
      linear_combination -(ι ε - ι d * ι r0) * hinv2
    exact hinj h4
  obtain ⟨k, hk⟩ := sub_dvd_pow_sub_pow (d * r0 + τ * s) (d * r0) (N + 1)
  rw [← h5] at hk
  have e1 := idem_pow hε N
  have h6 : ε = τ * (s * k) + (p : B) * (w * r0 ^ (N + 1)) := by
    linear_combination -e1 + hk + r0 ^ (N + 1) * hd + k * h5
  have hN : ∀ m, Near ι p (ι τ) m (ι ε) := by
    intro m
    obtain ⟨k2, hk2⟩ := sub_dvd_pow_sub_pow (τ * (s * k) + (p : B) * (w * r0 ^ (N + 1)))
      (τ * (s * k)) (m + 1)
    rw [← h6] at hk2
    have e2 := idem_pow hε m
    have e3 : ε = τ ^ m * (τ * (s * k) ^ (m + 1)) + (p : B) * (w * r0 ^ (N + 1) * k2) := by
      linear_combination -e2 + hk2 + k2 * h6
    refine ⟨τ * (s * k) ^ (m + 1), ι (w * r0 ^ (N + 1) * k2), ?_⟩
    have e4 := congrArg ι e3
    simpa only [map_add, map_mul, map_pow, map_natCast] using e4
  obtain ⟨r1, hr1⟩ := hnear (ι ε) hN
  obtain ⟨e5, he5⟩ := hsat ε r1 hr1
  have h7 : ε = (p : B) * e5 := hinj (by rw [map_mul, map_natCast, he5, hr1])
  have h8 : ∀ k : ℕ, ε = (p : B) ^ k * (e5 ^ k * ε) := by
    intro k
    have e6 := idem_pow hε k
    rw [pow_succ] at e6
    calc ε = ε ^ k * ε := e6.symm
      _ = ((p : B) * e5) ^ k * ε := by rw [← h7]
      _ = (p : B) ^ k * (e5 ^ k * ε) := by ring
  have h9 : ι ε = 0 := hsep (ι ε) fun k => ⟨ι (e5 ^ k * ε), by
    conv_lhs => rw [h8 k]
    simp only [map_mul, map_pow, map_natCast]⟩
  exact hinj (h9.trans (map_zero ι).symm)

private theorem coeff_tail_lemma {O : Type} [CommRing O] (f : ℕ → PowerSeries O) (j M : ℕ) (h : j < M) :
    PowerSeries.coeff j (∑ k ∈ Finset.range M, PowerSeries.X ^ k * f k) =
      PowerSeries.coeff j (∑ k ∈ Finset.range (j + 1), PowerSeries.X ^ k * f k) := by
  rw [map_sum, map_sum]
  symm
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k _ hk
    simp only [Finset.mem_range, not_lt] at hk
    rw [PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

variable {O : Type} [CommRing O] {n : ℕ}

theorem exists_tail (b : ℕ → LetA O n) : ∃ σ : LetA O n, ∀ m, ∃ t,
    σ - ∑ k ∈ Finset.range m, letπ ^ k * b k = letπ ^ m * t := by
  refine ⟨fun i => PowerSeries.mk fun j => PowerSeries.coeff j
      (∑ k ∈ Finset.range (j + 1), PowerSeries.X ^ k * b k i), fun m => ?_⟩
  have hd : ∀ i, (PowerSeries.X : PowerSeries O) ^ m ∣ (PowerSeries.mk fun j => PowerSeries.coeff j
      (∑ k ∈ Finset.range (j + 1), PowerSeries.X ^ k * b k i)) -
        ∑ k ∈ Finset.range m, PowerSeries.X ^ k * b k i := by
    intro i
    rw [PowerSeries.X_pow_dvd_iff]
    intro j hj
    rw [map_sub, PowerSeries.coeff_mk, coeff_tail_lemma (fun k => b k i) j m hj, sub_self]
  choose t ht using hd
  refine ⟨t, funext fun i => ?_⟩
  simp only [Pi.sub_apply, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply]
  exact ht i

private theorem near_mono_lemma {A : Type} [CommRing A] (ι : A →+* R) (τ : A) {m : ℕ} {x : R}
    (h : Near ι p (ι τ) (m + 1) x) : Near ι p (ι τ) m x := by
  obtain ⟨a, r, hx⟩ := h
  exact ⟨τ * a, r, by rw [hx, map_mul, pow_succ]; ring⟩

theorem near_series (ι : B →+* R) (io : LetA O n →+* B) (hu : IsUnit (ι (io letπ)))
    (h0 : ∀ c : ZMod n → O, Near ι p (ι (io letπ)) 1 (ι (io fun i => PowerSeries.C (c i))) →
      ∀ i, (p : O) ∣ c i) (m : ℕ) :
    ∀ a : LetA O n, Near ι p (ι (io letπ)) m (ι (io a)) →
      ∃ a1 a2 : LetA O n, a = letπ ^ m * a1 + (p : LetA O n) * a2 := by
  obtain ⟨u, hu'⟩ := hu
  induction m with
  | zero => intro a _; exact ⟨a, 0, by ring⟩
  | succ m ih =>
    intro a ha
    obtain ⟨a1, a2, h12⟩ := ih a (near_mono_lemma ι (io letπ) ha)
    obtain ⟨b, r, hb⟩ := ha
    obtain ⟨c, hc⟩ : ∃ c : ZMod n → O, c = fun i => PowerSeries.constantCoeff (a1 i) := ⟨_, rfl⟩
    obtain ⟨s, hs⟩ : ∃ s : LetA O n,
        a1 = letπ * s + (fun i => PowerSeries.C (c i) : LetA O n) :=
      ⟨fun i => PowerSeries.mk fun j => PowerSeries.coeff (j + 1) (a1 i), funext fun i => by
        rw [hc]; exact PowerSeries.eq_X_mul_shift_add_const (a1 i)⟩
    have h12' : a = letπ ^ m * (letπ * s + (fun i => PowerSeries.C (c i) : LetA O n)) +
        (p : LetA O n) * a2 := by
      rw [← hs]; exact h12
    have E2 := congrArg (fun z => ι (io z)) h12'
    simp only [map_add, map_mul, map_pow, map_natCast] at E2
    have hVm : (↑u⁻¹ : R) ^ m * ι (io letπ) ^ m = 1 := by
      rw [← mul_pow, ← hu', Units.inv_mul, one_pow]
    have hnear1 : Near ι p (ι (io letπ)) 1 (ι (io fun i => PowerSeries.C (c i))) := by
      refine ⟨b - io s, ↑u⁻¹ ^ m * (r - ι (io a2)), ?_⟩
      rw [map_sub]
      linear_combination (↑u⁻¹ : R) ^ m * hb - (↑u⁻¹ : R) ^ m * E2 -
        (ι (io fun i => PowerSeries.C (c i)) - ι (io letπ) * ι b + ι (io letπ) * ι (io s)) * hVm
    choose c' hc' using h0 c hnear1
    have hC : (fun i => PowerSeries.C (c i) : LetA O n) =
        (p : LetA O n) * (fun i => PowerSeries.C (c' i) : LetA O n) := funext fun i => by
      show PowerSeries.C (c i) = (p : PowerSeries O) * PowerSeries.C (c' i)
      rw [hc' i, map_mul, map_natCast]
    refine ⟨s, letπ ^ m * (fun i => PowerSeries.C (c' i) : LetA O n) + a2, ?_⟩
    linear_combination h12 + letπ ^ m * hs + letπ ^ m * hC

private theorem near_mono_lemma_2 {A : Type} [CommRing A] (ι : A →+* R) (τ : A) {m : ℕ} {x : R}
    (h : Near ι p (ι τ) (m + 1) x) : Near ι p (ι τ) m x := by
  obtain ⟨a, r, hx⟩ := h
  exact ⟨τ * a, r, by rw [hx, map_mul, pow_succ]; ring⟩

theorem near_closed (ι : B →+* R) (io : LetA O n →+* B) (al : LetA O n →+* E) (j : E →+* R)
    (hj : ∀ a, j (al a) = ι (io a)) (hu : IsUnit (ι (io letπ)))
    (hd : ∀ e, ∃ a m r, e * al (letπ ^ m) - al a = (p : E) * r)
    (hnear : ∀ x : R, (∀ m, Near ι p (ι (io letπ)) m x) → ∃ r, x = (p : R) * r)
    (h0 : ∀ c : ZMod n → O, Near ι p (ι (io letπ)) 1 (ι (io fun i => PowerSeries.C (c i))) →
      ∀ i, (p : O) ∣ c i) (x : R) (hx : ∀ m, ∃ e, Near ι p (ι (io letπ)) m (x - j e)) :
    ∃ e r, x - j e = (p : R) * r := by
  obtain ⟨u, hu'⟩ := hu
  have key : ∀ (e : E) (m : ℕ), Near ι p (ι (io letπ)) m (j e) →
      ∃ a1 r, j e = ι (io (letπ ^ m * a1)) + (p : R) * r := by
    intro e m hm
    obtain ⟨a, k, r, her⟩ := hd e
    obtain ⟨b, r2, hb⟩ := hm
    have E1 : j e * ι (io letπ) ^ k = ι (io a) + (p : R) * j r := by
      have h1 := congrArg j her
      simp only [map_sub, map_mul, map_natCast, hj, map_pow] at h1
      linear_combination h1
    obtain ⟨a1, a2, ha⟩ := near_series ι io ⟨u, hu'⟩ h0 (m + k) a
      ⟨b, r2 * ι (io letπ) ^ k - j r, by linear_combination -E1 + ι (io letπ) ^ k * hb⟩
    have E2 := congrArg (fun z => ι (io z)) ha
    simp only [map_add, map_mul, map_pow, map_natCast] at E2
    have hV : (↑u⁻¹ : R) ^ k * ι (io letπ) ^ k = 1 := by
      rw [← mul_pow, ← hu', Units.inv_mul, one_pow]
    refine ⟨a1, ↑u⁻¹ ^ k * (ι (io a2) + j r), ?_⟩
    simp only [map_mul, map_pow]
    linear_combination (↑u⁻¹ : R) ^ k * E1 + (↑u⁻¹ : R) ^ k * E2 - j e * hV +
      ι (io letπ) ^ m * ι (io a1) * hV
  choose e he using hx
  have hstep : ∀ m, ∃ b r, j (e (m + 1) - e m) = ι (io (letπ ^ m * b)) + (p : R) * r := by
    intro m
    apply key
    have h2 : j (e (m + 1) - e m) = (x - j (e m)) + -(x - j (e (m + 1))) := by
      rw [map_sub]; ring
    rw [h2]
    exact Near.add (he m) (Near.neg (near_mono_lemma_2 ι (io letπ) (he (m + 1))))
  choose b r hbr using hstep
  obtain ⟨σ, hσ⟩ := exists_tail b
  obtain ⟨r0, hr0⟩ := hnear (x - j (e 0) - ι (io σ)) fun M => by
    obtain ⟨tM, htM⟩ := hσ M
    have S0 : ∑ k ∈ Finset.range M, (j (e (k + 1)) - j (e k)) = j (e M) - j (e 0) :=
      Finset.sum_range_sub (fun k => j (e k)) M
    have S1 : j (e M) - j (e 0) = ι (io (∑ k ∈ Finset.range M, letπ ^ k * b k)) +
        (p : R) * ∑ k ∈ Finset.range M, r k := by
      rw [← S0, map_sum, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [← map_sub]; exact hbr k
    have H := congrArg (fun z => ι (io z)) htM
    simp only [map_sub, map_mul, map_pow] at H
    have hy : x - j (e 0) - ι (io σ) = (x - j (e M)) + (ι (io letπ) ^ M * ι (io (-tM)) +
        (p : R) * ∑ k ∈ Finset.range M, r k) := by
      rw [map_neg, map_neg]
      linear_combination S1 - H
    rw [hy]
    exact Near.add (he M) ⟨io (-tM), _, rfl⟩
  refine ⟨e 0 + al σ, r0, ?_⟩
  rw [map_add, hj]
  linear_combination hr0

def perf (j : E →+* R) (φ : R →+* R) (hφ : ∀ e, ∃ e', φ (j e) = j e') (p : ℕ) : Subring R where
  carrier := {x | ∃ n : ℕ, ∃ e r, φ^[n] x = j e + (p : R) * r}
  zero_mem' := ⟨0, 0, 0, by simp⟩
  one_mem' := ⟨0, 1, 0, by simp⟩
  neg_mem' := by
    rintro x ⟨n, e, r, h⟩
    exact ⟨n, -e, -r, by rw [iterate_map_neg, h, map_neg]; ring⟩
  add_mem' := by
    rintro x y ⟨n, hx⟩ ⟨m, hy⟩
    obtain ⟨e, r, h⟩ := GlobalTheory.DecomplMat.iterate_persist j φ hφ (le_max_left n m) hx
    obtain ⟨e', r', h'⟩ := GlobalTheory.DecomplMat.iterate_persist j φ hφ (le_max_right n m) hy
    exact ⟨max n m, e + e', r + r', by rw [iterate_map_add, h, h', map_add]; ring⟩
  mul_mem' := by
    rintro x y ⟨n, hx⟩ ⟨m, hy⟩
    obtain ⟨e, r, h⟩ := GlobalTheory.DecomplMat.iterate_persist j φ hφ (le_max_left n m) hx
    obtain ⟨e', r', h'⟩ := GlobalTheory.DecomplMat.iterate_persist j φ hφ (le_max_right n m) hy
    exact ⟨max n m, e * e', j e * r' + r * (j e' + p * r'), by
      rw [iterate_map_mul, h, h', map_mul]; ring⟩

theorem matrix_eq (j : E →+* R) (φ : R →+* R) {a b : ℕ} (A : Matrix (Fin a) (Fin a) E)
    (A' C : Matrix (Fin b) (Fin b) E) (Y : Matrix (Fin a) (Fin b) E) (U : Matrix (Fin a) (Fin b) R)
    (hC : A' * C = 1) (h : A.map j * U.map φ = U * A'.map j + Y.map j) {D : Type} [Fintype D]
    (σ : D ≃ Fin a × Fin b) (x : D) :
    ∑ y, j (A (σ x).1 (σ y).1 * C (σ y).2 (σ x).2) * φ (U (σ y).1 (σ y).2) - U (σ x).1 (σ x).2 =
      j ((Y * C) (σ x).1 (σ x).2) := by
  have key : A.map j * U.map φ * C.map j = U + (Y * C).map j := by
    rw [h, Matrix.add_mul, Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul, hC,
      Matrix.map_one _ (map_zero j) (map_one j), Matrix.mul_one]
  have e2 : ∑ q, ∑ k, j (A (σ x).1 k * C q (σ x).2) * φ (U k q) =
      (A.map j * U.map φ * C.map j) (σ x).1 (σ x).2 := by
    simp only [Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul, map_mul]
    exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun k _ => by ring
  rw [key, Matrix.add_apply, Matrix.map_apply] at e2
  rw [Equiv.sum_comp σ (fun z : Fin a × Fin b => j (A (σ x).1 z.1 * C z.2 (σ x).2) * φ (U z.1 z.2)),
    Fintype.sum_prod_type, Finset.sum_comm]
  linear_combination e2

end Abstract

end GlobalTheory.HWL.Rational
