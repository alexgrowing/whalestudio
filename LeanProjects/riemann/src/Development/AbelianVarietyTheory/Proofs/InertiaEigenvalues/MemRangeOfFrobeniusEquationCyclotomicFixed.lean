import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RootEqOfNormLt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicLevelSubgroupMemWachSubgroups
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InclWFrobIter

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Decompl
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FrobDescent

section Abstract

variable {E A R : Type} [CommRing E] [CommRing A] [CommRing R]

def modSub (io : E →+* R) (p : ℕ) : Subring R where
  carrier := {x | ∃ e r, x = io e + (p : R) * r}
  mul_mem' := by
    rintro _ _ ⟨a, r, rfl⟩ ⟨b, s, rfl⟩
    exact ⟨a * b, io a * s + r * (io b + p * s), by rw [map_mul]; ring⟩
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨a, r, rfl⟩ ⟨b, s, rfl⟩
    exact ⟨a + b, r + s, by rw [map_add]; ring⟩
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by
    rintro _ ⟨a, r, rfl⟩
    exact ⟨-a, -r, by rw [map_neg]; ring⟩

theorem io_mem (io : E →+* R) (p : ℕ) (e : E) : io e ∈ modSub io p := ⟨e, 0, by simp⟩

theorem pow_mem_of_le {φ : R →+* R} {D : Subring R} (hD : ∀ x ∈ D, φ x ∈ D) {N N' : ℕ}
    (h : N ≤ N') {x : R} (hx : (φ ^ N) x ∈ D) : (φ ^ N') x ∈ D := by
  induction h with
  | refl => exact hx
  | step _ ih => rw [pow_succ']; exact hD _ ih

def perfSub (φ : R →+* R) (D : Subring R) (hD : ∀ x ∈ D, φ x ∈ D) : Subring R where
  carrier := {x | ∃ N : ℕ, (φ ^ N) x ∈ D}
  mul_mem' := by
    rintro a b ⟨N, h⟩ ⟨N', h'⟩
    refine ⟨max N N', ?_⟩
    rw [map_mul]
    exact mul_mem (pow_mem_of_le hD (le_max_left _ _) h) (pow_mem_of_le hD (le_max_right _ _) h')
  one_mem' := ⟨0, by rw [map_one]; exact one_mem _⟩
  add_mem' := by
    rintro a b ⟨N, h⟩ ⟨N', h'⟩
    refine ⟨max N N', ?_⟩
    rw [map_add]
    exact add_mem (pow_mem_of_le hD (le_max_left _ _) h) (pow_mem_of_le hD (le_max_right _ _) h')
  zero_mem' := ⟨0, by rw [map_zero]; exact zero_mem _⟩
  neg_mem' := by
    rintro a ⟨N, h⟩
    exact ⟨N, by rw [map_neg]; exact neg_mem h⟩

theorem modSub_stable {io : E →+* R} {φ : R →+* R} {φE : E → E} (p : ℕ)
    (hφ : ∀ e, io (φE e) = φ (io e)) : ∀ x ∈ modSub io p, φ x ∈ modSub io p := by
  rintro _ ⟨e, r, rfl⟩
  exact ⟨φE e, φ r, by rw [map_add, map_mul, map_natCast, hφ]⟩

theorem approx_step {ι : A →+* R} {p : ℕ} {t : R} {τ : A} (hτ : ι τ = t) (ht : IsUnit t)
    (hp : 2 ≤ p) {φ : R →+* R} {D : Subring R} (hD : ∀ x ∈ D, φ x ∈ D)
    (h3 : ∀ m x, Near ι p t m x → Near ι p t (p * m) (φ x))
    {I : Type} [Fintype I] (M : I → I → R) (c w : I → R) (hM : ∀ i j, M i j ∈ D)
    (hc : ∀ i, c i ∈ D) (h4 : ∀ i j, ∃ k, Near ι p t 0 (t ^ k * M i j))
    (hw : ∀ i, w i = ∑ j, M i j * φ (w j) + c i)
    (h2 : ∀ m i, ∃ u ∈ perfSub φ D hD, Near ι p t m (w i - u)) (m : ℕ) (i : I) :
    ∃ u ∈ D, Near ι p t m (w i - u) := by
  choose k hk using h4
  obtain ⟨K, hK⟩ : ∃ K, ∀ i j, k i j ≤ K :=
    ⟨Finset.univ.sup fun q : I × I => k q.1 q.2, fun i j =>
      Finset.le_sup (f := fun q : I × I => k q.1 q.2) (Finset.mem_univ (i, j))⟩
  have key : ∀ (N : ℕ) (u : I → R), (∀ i, (φ ^ N) (u i) ∈ D) →
      (∀ i, Near ι p t (m + K) (w i - u i)) →
      ∃ u' : I → R, ∀ i, u' i ∈ D ∧ Near ι p t (m + K) (w i - u' i) := by
    intro N
    induction N with
    | zero => exact fun u h1 h2 => ⟨u, fun i => ⟨h1 i, h2 i⟩⟩
    | succ N ih =>
      intro u h1 h2
      refine ih (fun i => ∑ j, M i j * φ (u j) + c i) (fun i => ?_) (fun i => ?_)
      · rw [map_add, map_sum]
        refine add_mem (sum_mem fun j _ => ?_) (pow_mem_of_le hD (Nat.zero_le N) (hc i))
        rw [map_mul]
        exact mul_mem (pow_mem_of_le hD (Nat.zero_le N) (hM i j)) (h1 j)
      · have e : w i - (∑ j, M i j * φ (u j) + c i) = ∑ j, M i j * φ (w j - u j) := by
          rw [hw i]
          simp only [map_sub, mul_sub, Finset.sum_sub_distrib]
          ring
        rw [e]
        refine Near.sum _ fun j _ => Near.cancel ht (k := k i j) ?_
        rw [← mul_assoc]
        refine ((hk i j).mul (h3 _ _ (h2 j))).mono hτ ?_
        have := hK i j
        nlinarith
  choose u hu hu' using h2 (m + K)
  choose N hN using hu
  obtain ⟨u', h⟩ := key (Finset.univ.sup N) u
    (fun i => pow_mem_of_le hD (Finset.le_sup (f := N) (Finset.mem_univ i)) (hN i)) hu'
  exact ⟨u' i, (h i).1, (h i).2.mono hτ (Nat.le_add_right _ _)⟩

theorem padic_step {io : E →+* R} {φ : R →+* R} {φE : E → E} {p : ℕ}
    (hφ : ∀ e, io (φE e) = φ (io e)) (tf : ∀ x : R, (p : R) * x = 0 → x = 0)
    (sep : ∀ x : R, (∀ k : ℕ, (p : R) ^ k ∣ x) → x = 0)
    [IsPrecomplete (Ideal.span {(p : E)}) E]
    (sat : ∀ e r, io e = (p : R) * r → ∃ e', e = (p : E) * e')
    (S : Subring R) (hS : ∀ e, io e ∈ S) (hS' : ∀ x, (p : R) * x ∈ S → x ∈ S)
    {I : Type} [Fintype I] (M : I → I → E)
    (H : ∀ (c : I → E) (w : I → R), (∀ i, w i ∈ S) →
      (∀ i, w i = ∑ j, io (M i j) * φ (w j) + io (c i)) → ∀ i, w i ∈ modSub io p)
    (c : I → E) (w : I → R) (hw : ∀ i, w i ∈ S)
    (hc : ∀ i, w i = ∑ j, io (M i j) * φ (w j) + io (c i)) (i : I) : ∃ e, io e = w i := by
  have key : ∀ (N : ℕ) (c : I → E) (w : I → R), (∀ i, w i ∈ S) →
      (∀ i, w i = ∑ j, io (M i j) * φ (w j) + io (c i)) →
      ∀ i, ∃ e r, w i = io e + (p : R) ^ N * r := by
    intro N
    induction N with
    | zero => exact fun c w _ _ i => ⟨0, w i, by simp⟩
    | succ N ih =>
      intro c w hw hc
      choose e r her using H c w hw hc
      have h1 : ∀ i, io (∑ j, M i j * φE (e j) + c i - e i) =
          (p : R) * (r i - ∑ j, io (M i j) * φ (r j)) := by
        intro i
        have := hc i
        simp only [her, map_add, map_mul, map_natCast, mul_add, Finset.sum_add_distrib] at this
        simp only [map_sub, map_add, map_sum, map_mul, hφ, mul_sub, Finset.mul_sum]
        have e2 : ∑ j, (p : R) * (io (M i j) * φ (r j)) = ∑ j, io (M i j) * (p * φ (r j)) :=
          Finset.sum_congr rfl fun j _ => by ring
        rw [e2]
        linear_combination -this
      choose c' hc' using fun i => sat _ _ (h1 i)
      intro i
      obtain ⟨e', r', h⟩ := ih c' r (fun i => hS' _ (by
          have := sub_mem (hw i) (hS (e i))
          rwa [her, add_sub_cancel_left] at this)) (fun i => by
          have := h1 i
          rw [hc', map_mul, map_natCast] at this
          rw [← sub_eq_zero]
          apply tf
          linear_combination -this) i
      exact ⟨e i + p * e', r', by rw [her, h, map_add, map_mul, map_natCast]; ring⟩
  have satk : ∀ (k : ℕ) e r, io e = (p : R) ^ k * r → ∃ e', e = (p : E) ^ k * e' := by
    intro k
    induction k with
    | zero => exact fun e _ _ => ⟨e, by simp⟩
    | succ k ih =>
      intro e r h
      obtain ⟨e', rfl⟩ := sat e ((p : R) ^ k * r) (by rw [h]; ring)
      obtain ⟨e'', rfl⟩ := ih e' r (by
        rw [map_mul, map_natCast] at h
        rw [← sub_eq_zero]
        apply tf
        linear_combination h)
      exact ⟨e'', by ring⟩
  choose e r her using fun N => key N c w hw hc i
  have hI : ∀ (k : ℕ) (a b : E), a ≡ b [SMOD (Ideal.span {(p : E)} ^ k • ⊤ : Submodule E E)] ↔
      (p : E) ^ k ∣ a - b := by
    intro k a b
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : E)}) e (fun {m n} hmn => by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [hI]
    refine satk m _ ((p : R) ^ d * r (m + d) - r m) ?_
    rw [map_sub]
    linear_combination her (m + d) - her m)
  refine ⟨L, ?_⟩
  rw [← sub_eq_zero]
  refine sep _ fun k => ?_
  obtain ⟨d, hd⟩ := (hI k _ _).1 (hL k)
  have := congrArg io hd
  rw [map_sub, map_mul, map_pow, map_natCast] at this
  exact ⟨-io d - r k, by linear_combination -this - her k⟩

end Abstract

section Series

open GlobalTheory.TorsionBoundCompare PowerSeries

variable {O E A R : Type} [CommRing O] [CommRing E] [CommRing A] [CommRing R] {n p : ℕ}

theorem eq_pow_mul_add (f : LetA O n) (m : ℕ) (h : ∀ i, ∀ j < m, (p : O) ∣ coeff j (f i)) :
    ∃ b b' : LetA O n, f = letπ ^ m * b + (p : LetA O n) * b' := by
  have h' : ∀ i j, ∃ d, j < m → coeff j (f i) = (p : O) * d := fun i j => by
    by_cases hj : j < m
    · obtain ⟨d, hd⟩ := h i j hj
      exact ⟨d, fun _ => hd⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose d hd using h'
  have h2 : ∀ i, (X : O⟦X⟧) ^ m ∣ f i - (p : O⟦X⟧) * mk (d i) := fun i => by
    rw [X_pow_dvd_iff]
    intro j hj
    rw [map_sub, hd i j hj, ← nsmul_eq_mul, ← nsmul_eq_mul, map_nsmul, coeff_mk, sub_self]
  choose b hb using h2
  exact ⟨b, fun i => mk (d i), funext fun i => eq_add_of_sub_eq (hb i)⟩

theorem eq_natCast_mul (f : LetA O n) (h : ∀ i j, (p : O) ∣ coeff j (f i)) :
    ∃ b : LetA O n, f = (p : LetA O n) * b := by
  choose d hd using h
  refine ⟨fun i => mk (d i), funext fun i => ?_⟩
  ext j
  change _ = coeff j ((p : O⟦X⟧) * mk (d i))
  rw [hd, ← nsmul_eq_mul, ← nsmul_eq_mul, map_nsmul, coeff_mk]

theorem exists_series_sum (a : ℕ → LetA O n) :
    ∃ b : LetA O n, ∀ m, letπ ^ m ∣ b - ∑ j ∈ Finset.range m, letπ ^ j * a j := by
  refine ⟨fun i => mk fun k => coeff k (∑ j ∈ Finset.range (k + 1), X ^ j * a j i), fun m => ?_⟩
  have h2 : ∀ i, (X : O⟦X⟧) ^ m ∣ (mk fun k => coeff k (∑ j ∈ Finset.range (k + 1), X ^ j * a j i))
      - ∑ j ∈ Finset.range m, X ^ j * a j i := fun i => by
    rw [X_pow_dvd_iff]
    intro k hk
    rw [map_sub, coeff_mk, map_sum, map_sum, sub_eq_zero]
    refine Finset.sum_subset (Finset.range_subset_range.2 hk) fun j _ hj => ?_
    rw [coeff_X_pow_mul', if_neg]
    simpa using hj
  choose b hb using h2
  refine ⟨b, funext fun i => ?_⟩
  have := hb i
  simpa [Finset.sum_apply, letπ] using this

variable {ι : A →+* R} {t : R} {σ : LetA O n →+* R}

theorem const_dvd [Nontrivial O] (hn : 0 < n) (hp : 2 ≤ p) {τ : A} (hτ : ι τ = t) {φ : R → R}
    (h3 : ∀ m x, Near ι p t m x → Near ι p t (p * m) (φ x))
    (meet : ∀ x, (∀ m, Near ι p t m x) → ∃ r, x = (p : R) * r)
    (tf : ∀ x : R, (p : R) * x = 0 → x = 0)
    (sep : ∀ x : R, (∀ k : ℕ, (p : R) ^ k ∣ x) → x = 0)
    (hO : ∀ c : O, (p : O) ∣ c ∨ ∃ (d : O) (k : ℕ), (p : O) = c * d ∧ (p : O) ∣ d ^ k)
    (hσ : Function.Injective σ) (c : ZMod n → O) (hc : φ^[n] (σ (cst c)) = σ (cst c))
    (h1 : Near ι p t 1 (σ (cst c))) (i : ZMod n) : (p : O) ∣ c i := by
  classical
  have hit : ∀ k m x, Near ι p t (m + 1) x → Near ι p t (m + 1 + k) (φ^[k] x) := by
    intro k m x hx
    induction k with
    | zero => exact hx
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact (h3 _ _ ih).mono hτ (by nlinarith)
  have hall : ∀ m, Near ι p t (m + 1) (σ (cst c)) := by
    intro m
    induction m with
    | zero => exact h1
    | succ m ih =>
      have := hit n m _ ih
      rw [hc] at this
      exact this.mono hτ (by omega)
  obtain ⟨r, hr⟩ := meet _ fun m => (hall m).mono hτ (Nat.le_succ m)
  refine (hO (c i)).resolve_right ?_
  rintro ⟨d, k, hd, e, he⟩
  let j : O →+* R := σ.comp ((Pi.constRingHom (ZMod n) O⟦X⟧).comp C)
  have h2 : σ (letE i) * σ (cst c) = j (c i) * σ (letE i) := by
    change _ = σ (Function.const _ (C (c i))) * _
    rw [← map_mul, ← map_mul]
    congr 1
    funext k
    by_cases hk : k = i
    · subst hk; simp [letE, cst]
    · simp [letE, hk]
  have hid : IsIdempotentElem (σ (letE i)) := by
    rw [IsIdempotentElem, ← map_mul]
    congr 1
    funext k
    by_cases hk : k = i
    · subst hk; simp [letE]
    · simp [letE, hk]
  have hd' := congrArg j hd
  have he' := congrArg j he
  rw [map_natCast, map_mul] at hd'
  rw [map_pow, map_mul, map_natCast] at he'
  have h4 : σ (letE i) = j d * (σ (letE i) * r) := by
    rw [← sub_eq_zero]
    apply tf
    rw [hr] at h2
    linear_combination (-j d) * h2 + σ (letE i) * hd'
  have h5 : (p : R) ∣ σ (letE i) := by
    rw [← hid.pow_succ_eq k, h4, mul_pow, pow_succ, he']
    exact ((dvd_mul_right _ _).mul_right _).mul_right _
  have h6 : σ (letE i) = 0 := by
    refine sep _ fun r => ?_
    have := pow_dvd_pow_of_dvd h5 (r + 1)
    rw [hid.pow_succ_eq] at this
    exact (pow_dvd_pow _ (Nat.le_succ r)).trans this
  have h7 := congrFun (hσ (h6.trans (map_zero σ).symm)) i
  simp [letE] at h7

theorem coeff_dvd {σ₀ : LetA O n → A} (hσ₀ : ∀ f, σ f = ι (σ₀ f)) (ht : σ letπ = t) (hu : IsUnit t)
    (h0 : ∀ c, Near ι p t 1 (σ (cst c)) → ∀ i, (p : O) ∣ c i) (m : ℕ) (f : LetA O n)
    (hf : Near ι p t m (σ f)) : ∀ i, ∀ j < m, (p : O) ∣ coeff j (f i) := by
  have hτ : ι (σ₀ letπ) = t := (hσ₀ _).symm.trans ht
  induction m generalizing f with
  | zero => simp
  | succ m ih =>
    obtain ⟨g, hg⟩ : ∃ g : LetA O n, g = fun i => mk fun p => coeff (p + 1) (f i) := ⟨_, rfl⟩
    have ha : f = cst (fun i => constantCoeff (f i)) + letπ * g := by
      funext i
      rw [Pi.add_apply, add_comm, hg]
      exact eq_X_mul_shift_add_const (f i)
    have hb := congrArg σ ha
    rw [map_add, map_mul, ht] at hb
    have h1 : Near ι p t 1 (σ (cst fun i => constantCoeff (f i))) := by
      have := (hf.mono hτ (Nat.le_add_left 1 m)).sub (Near.pow_mul 1 (σ₀ g))
      rwa [← hσ₀, hb, pow_one, add_sub_cancel_right] at this
    have h2 := h0 _ h1
    choose d hd using h2
    have h3 : cst (fun i => constantCoeff (f i)) = (p : LetA O n) * cst d := by
      funext i
      simp [cst, hd]
    have h4 : Near ι p t m (σ g) := by
      refine Near.cancel hu (k := 1) ?_
      have := hf.sub (Near.of_mul (m + 1) (σ (cst d)))
      rw [pow_one, add_comm]
      rwa [hb, h3, map_mul, map_natCast, add_sub_cancel_left] at this
    intro i j hj
    rcases j with _ | j
    · exact ⟨d i, by rw [← hd, coeff_zero_eq_constantCoeff]⟩
    · have := ih g h4 i j (by omega)
      rwa [hg, coeff_mk] at this

variable {a : LetA O n →+* E} {io : E →+* R}

theorem sat_of (hπ : IsUnit (a letπ))
    (hd : ∀ e : E, ∃ f k e', e * a (letπ ^ k) - a f = (p : E) * e')
    (hc : ∀ m f, Near ι p t m (io (a f)) → ∀ i, ∀ j < m, (p : O) ∣ coeff j (f i))
    (e : E) (r : R) (h : io e = (p : R) * r) : ∃ e', e = (p : E) * e' := by
  obtain ⟨f, k, e', hf⟩ := hd e
  have h1 := congrArg io hf
  rw [map_sub, map_mul, map_mul, map_natCast, h] at h1
  have h2 : io (a f) = (p : R) * (r * io (a (letπ ^ k)) - io e') := by linear_combination -h1
  obtain ⟨b, rfl⟩ := eq_natCast_mul (p := p) f fun i j =>
    hc (j + 1) f (h2 ▸ Near.of_mul _ _) i j (Nat.lt_succ_self j)
  rw [map_mul, map_natCast, map_pow] at hf
  obtain ⟨u, hu⟩ := (hπ.pow k).exists_right_inv
  exact ⟨(e' + a b) * u, by linear_combination u * hf - e * hu⟩

theorem near_zero_of {σ₀ : LetA O n → A} (hσ₀ : ∀ f, io (a f) = ι (σ₀ f)) (ht : io (a letπ) = t)
    (hd : ∀ e : E, ∃ f k e', e * a (letπ ^ k) - a f = (p : E) * e') (e : E) :
    ∃ k, Near ι p t 0 (t ^ k * io e) := by
  obtain ⟨f, k, e', hf⟩ := hd e
  have h1 := congrArg io hf
  rw [map_sub, map_mul, map_mul, map_natCast, map_pow, map_pow, ht, hσ₀] at h1
  exact ⟨k, σ₀ f, io e', by linear_combination h1⟩

theorem eq_of_near {σ₀ : LetA O n → A} (hσ₀ : ∀ f, io (a f) = ι (σ₀ f)) (ht : io (a letπ) = t)
    (hπ : IsUnit (a letπ)) (hd : ∀ e : E, ∃ f k e', e * a (letπ ^ k) - a f = (p : E) * e')
    (hc : ∀ m f, Near ι p t m (io (a f)) → ∀ i, ∀ j < m, (p : O) ∣ coeff j (f i))
    (m : ℕ) (e : E) (h : Near ι p t m (io e)) :
    ∃ b e', e = a (letπ ^ m * b) + (p : E) * e' := by
  obtain ⟨f, k, e', hf⟩ := hd e
  have h1 := congrArg io hf
  rw [map_sub, map_mul, map_mul, map_natCast, map_pow, map_pow, ht] at h1
  have h2 : Near ι p t (m + k) (io (a f)) := by
    have := (h.mul (Near.pow_mul k 1)).sub (Near.of_mul _ (io e'))
    rwa [map_one, mul_one, ← h1, sub_sub_cancel] at this
  obtain ⟨b, b', rfl⟩ := eq_pow_mul_add f (m + k) (hc _ _ h2)
  simp only [map_add, map_mul, map_natCast, map_pow, pow_add] at hf ⊢
  obtain ⟨u, hu⟩ := (hπ.pow k).exists_right_inv
  exact ⟨b, (e' + a b') * u, by linear_combination u * hf - (e - a letπ ^ m * a b) * hu⟩

theorem mem_modSub_of_limit {σ₀ : LetA O n → A} (hσ₀ : ∀ f, io (a f) = ι (σ₀ f))
    (ht : io (a letπ) = t)
    (hE : ∀ m e, Near ι p t m (io e) → ∃ b e', e = a (letπ ^ m * b) + (p : E) * e')
    (meet : ∀ x, (∀ m, Near ι p t m x) → ∃ r, x = (p : R) * r) (x : R)
    (hx : ∀ m, ∃ u ∈ modSub io p, Near ι p t m (x - u)) : x ∈ modSub io p := by
  have hτ : ι (σ₀ letπ) = t := (hσ₀ _).symm.trans ht
  have hx' : ∀ m, ∃ e, Near ι p t m (x - io e) := fun m => by
    obtain ⟨_, ⟨e, r, rfl⟩, h⟩ := hx m
    refine ⟨e, ?_⟩
    have := h.add (Near.of_mul m r)
    rwa [show x - (io e + p * r) + p * r = x - io e by ring] at this
  choose e he using hx'
  have h1 : ∀ m, Near ι p t m (io (e (m + 1) - e m)) := fun m => by
    have := (he m).sub ((he (m + 1)).mono hτ (Nat.le_succ m))
    rwa [sub_sub_sub_cancel_left, ← map_sub] at this
  choose b e' hb using fun m => hE m _ (h1 m)
  obtain ⟨c, hc⟩ := exists_series_sum b
  have h2 : ∀ m, e m = e 0 + a (∑ j ∈ Finset.range m, letπ ^ j * b j) +
      (p : E) * ∑ j ∈ Finset.range m, e' j := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, map_add]
      linear_combination ih + hb m
  obtain ⟨r, hr⟩ := meet (x - io (e 0 + a c)) fun m => by
    obtain ⟨d, hd⟩ := hc m
    have h3 := congrArg (fun y => io (a y)) hd
    have h4 := congrArg io (h2 m)
    simp only [map_sub, map_add, map_mul, map_pow, map_natCast, ht] at h3 h4
    have := ((he m).add (Near.of_mul m (io (∑ j ∈ Finset.range m, e' j)))).sub
      (Near.pow_mul m (σ₀ d))
    rw [← hσ₀] at this
    convert this using 1
    rw [map_add]
    linear_combination h4 - h3
  exact ⟨_, r, eq_add_of_sub_eq' hr⟩

end Series

section Concrete

open GlobalTheory.Cyc

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem coeff_pow_pow (x : OCb l) (k : ℕ) :
    PreTilt.coeff k (x ^ l ^ k) = PreTilt.coeff 0 x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_mul, map_pow, PreTilt.coeff_pow_p, ih]

theorem εroot_pow (j : ℕ) : AI.εroot j ^ l ^ j = AI.ε := by
  induction j with
  | zero => simp [LocAinf.εroot]
  | succ j ih =>
    rw [pow_succ', pow_mul, LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
    exact ih

theorem εroot_sub_pow (j : ℕ) : (AI.εroot j - 1) ^ l ^ j = AI.ε - 1 := by
  rw [sub_pow_char_pow, εroot_pow, one_pow]

theorem eq_zero_of_dvd (s : ℕ) (b : OCb l) (hb : ∀ m : ℕ, (AI.εroot s - 1) ^ m ∣ b) : b = 0 := by
  have h0 : PreTilt.coeff 0 (AI.ε - 1) = 0 := by
    rw [map_sub, AI.ε_coeff, AI.ζ_zero, map_one, map_one, sub_self]
  refine Perfection.ext fun k => ?_
  obtain ⟨c, hc⟩ := hb (l ^ s * l ^ k)
  change PreTilt.coeff k b = PreTilt.coeff k 0
  rw [hc, map_mul, pow_mul, εroot_sub_pow, coeff_pow_pow, h0, zero_mul, map_zero]

theorem exists_pow_mul (s : ℕ) (y : Cb l) : ∃ k, ∀ k' ≥ k, ∃ z : OCb l,
    algebraMap (OCb l) (Cb l) ((AI.εroot s - 1) ^ k') * y = algebraMap (OCb l) (Cb l) z := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) y
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨k, hk⟩ : ∃ k, b ∣ (AI.εroot s - 1) ^ k := by
    by_contra h
    exact hb0 (eq_zero_of_dvd AI s b fun m =>
      (ValuationRing.dvd_total _ _).resolve_right fun h' => h ⟨m, h'⟩)
  refine ⟨k, fun k' hk' => ?_⟩
  obtain ⟨d, hd⟩ := hk.trans (pow_dvd_pow _ hk')
  have : algebraMap (OCb l) (Cb l) b ≠ 0 := fun h =>
    hb0 (IsFractionRing.injective (OCb l) (Cb l) (h.trans (map_zero _).symm))
  refine ⟨d * a, ?_⟩
  rw [hd, map_mul, map_mul]
  field_simp

theorem tf_RW (LL : FinExt l) (x : RW LL) (hx : (l : RW LL) * x = 0) : x = 0 := by
  refine ext_crd (basisO LL) fun i => ?_
  have := congrArg (crd (basisO LL) i) hx
  rw [crd_natCast_mul, LinearMap.map_zero] at this
  rw [LinearMap.map_zero]
  exact (mul_eq_zero.1 this).resolve_left (WittVector.p_nonzero l (Cb l))

theorem meet_RW (LL : FinExt l) (s : ℕ) (x : RW LL) (hx : ∀ m, NearPi AI LL s m x) :
    ∃ r, x = (l : RW LL) * r := by
  refine (dvd_iff_crd LL x).2 fun i => ?_
  choose c hc using fun m => (nearPi_iff_crd AI LL s m x).1 (hx m) i
  have : (AI.εroot s - 1) ^ 0 * c 0 = 0 := eq_zero_of_dvd AI s _ fun m =>
    ⟨c m, IsFractionRing.injective (OCb l) (Cb l) ((hc 0).symm.trans (hc m))⟩
  rw [hc 0, this, map_zero]

theorem near_φ (LL : FinExt l) (s m : ℕ) (x : RW LL) (hx : NearPi AI LL s m x) :
    NearPi AI LL s (l * m) (φRW LL x) := by
  refine (nearPi_iff_crd AI LL s _ _).2 fun i => ?_
  obtain ⟨c, hc⟩ := (nearPi_iff_crd AI LL s m x).1 hx i
  refine ⟨c ^ l, ?_⟩
  rw [crd_φRW, coeff_frobW, hc, ← map_pow, mul_pow, ← pow_mul, mul_comm m]

theorem dvd_or (P : LocPrime l) (LL : FinExt l) (c : ↥(OL LL)) : ((l : ℕ) : ↥(OL LL)) ∣ c ∨
    ∃ (d : ↥(OL LL)) (k : ℕ), ((l : ℕ) : ↥(OL LL)) = c * d ∧ ((l : ℕ) : ↥(OL LL)) ∣ d ^ k := by
  have hl0 : ((l : ℕ) : ↥LL.1) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  by_cases hc0 : c = 0
  · exact Or.inl (hc0 ▸ dvd_zero _)
  have hc0' : (c : ↥LL.1) ≠ 0 := fun h => hc0 (Subtype.ext h)
  have hne : P.v LL c ≠ ⊤ := by simpa using hc0'
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.1 hne
  rcases le_total 1 q with h | h
  · left
    have hmem : (c : ↥LL.1) / (l : ↥LL.1) ∈ OL LL := by
      rw [← P.v_O, AddValuation.map_div, P.v_l, ← hq]
      have : ((q : WithTop ℚ) - 1 : WithTop ℚ) = ((q - 1 : ℚ) : WithTop ℚ) := by norm_cast
      rw [this]
      exact_mod_cast sub_nonneg.2 h
    refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
    simp only [MulMemClass.coe_mul, SubringClass.coe_natCast]
    rw [mul_div_cancel₀ _ hl0]
  · have hmem : (l : ↥LL.1) / (c : ↥LL.1) ∈ OL LL := by
      rw [← P.v_O, AddValuation.map_div, P.v_l, ← hq]
      have : (1 - (q : WithTop ℚ) : WithTop ℚ) = ((1 - q : ℚ) : WithTop ℚ) := by norm_cast
      rw [this]
      exact_mod_cast sub_nonneg.2 h
    have he : ((l : ℕ) : ↥(OL LL)) = c * ⟨_, hmem⟩ := by
      refine Subtype.ext ?_
      simp only [MulMemClass.coe_mul, SubringClass.coe_natCast]
      rw [mul_div_cancel₀ _ hc0']
    rcases GlobalTheory.EtaleExact.isUnit_or_dvd_pow P LL ⟨_, hmem⟩ with hu | ⟨k, hk⟩
    · left
      rw [he]
      exact hu.mul_right_dvd.2 dvd_rfl
    · exact Or.inr ⟨_, k, he, hk⟩

theorem crd_piR_pow (LL : FinExt l) (s k : ℕ) (x : RW LL) (i) :
    (crd (basisO LL) i (piR AI LL s ^ k * x)).coeff 0 =
      algebraMap (OCb l) (Cb l) ((AI.εroot s - 1) ^ k) * (crd (basisO LL) i x).coeff 0 := by
  have h1 : piR AI LL s ^ k = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (inclW l (piW AI s) ^ k) := by
    rw [piR_eq, Algebra.TensorProduct.tmul_pow, one_pow]
  have h4 : (inclW l (piW AI s) ^ k).coeff 0 = (inclW l (piW AI s)).coeff 0 ^ k :=
    map_pow (WittVector.constantCoeff : WCb l →+* Cb l) _ _
  rw [h1, crd_mul, WittVector.mul_coeff_zero, h4, coeff_zero_piW, map_pow]

theorem ennreal_volume_ratio_step_cancel {R : Type} [CommRing R] {t u : R} (h : t * u = 1) (k : ℕ) (x y : R) :
    t ^ k * x - y = t ^ k * (x - u ^ k * y) := by
  rw [mul_sub, ← mul_assoc, ← mul_pow, h, one_pow, one_mul]

theorem sum_tmul_mem {Z O W : Type} [CommRing Z] [CommRing O] [CommRing W] [Algebra Z O]
    [Algebra Z W] (D : Subring (O ⊗[Z] W)) (hO : ∀ o, algebraMap O (O ⊗[Z] W) o ∈ D) {I : Type}
    [Fintype I] (b : I → O) (w : I → W) (hw : ∀ i, (1 : O) ⊗ₜ[Z] w i ∈ D) :
    ∑ i, b i ⊗ₜ[Z] w i ∈ D :=
  sum_mem fun i _ => by simpa using mul_mem (hO (b i)) (hw i)

theorem exists_near (K LL : FinExt l) (s : ℕ) (D : Subring (RW LL))
    (hO : ∀ o, algebraMap ↥(OL LL) (RW LL) o ∈ D) (u : RW LL) (hu : u ∈ D)
    (hu' : piR AI LL s * u = 1)
    (hgen : ∀ y ∈ GlobalTheory.TiltInvariants.gen AI K, ∃ w : Ainf l, w.coeff 0 = y ∧
      ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] inclW l w : RW LL) ∈ D)
    (hπ : ∀ g ∈ Hinf K, AI.gRW LL g (piR AI LL s) = piR AI LL s)
    (x : RW LL) (hx : ∀ g ∈ Hinf K, AI.gRW LL g x = x) (m : ℕ) :
    ∃ y ∈ D, NearPi AI LL s m (x - y) := by
  choose k hk using fun i => exists_pow_mul AI s ((crd (basisO LL) i x).coeff 0)
  obtain ⟨N, hN⟩ : ∃ N, ∀ i, k i ≤ N :=
    ⟨Finset.univ.sup k, fun i => Finset.le_sup (f := k) (Finset.mem_univ i)⟩
  choose z hz using fun i => hk i N (hN i)
  obtain ⟨x', hx'⟩ : ∃ x', x' = piR AI LL s ^ N * x := ⟨_, rfl⟩
  have hz' : ∀ i, (crd (basisO LL) i x').coeff 0 = algebraMap (OCb l) (Cb l) (z i) := fun i =>
    hx' ▸ (crd_piR_pow AI LL s N x i).trans (hz i)
  have hfix : ∀ g ∈ Hinf K, AI.gRW LL g x' = x' := fun g hg => by
    have h1 := (map_mul (AI.gRW LL g) (piR AI LL s ^ N) x).trans
      (congrArg₂ (· * ·) ((map_pow (AI.gRW LL g) _ N).trans (congrArg (· ^ N) (hπ g hg))) (hx g hg))
    rw [hx']
    exact h1
  have hzf : ∀ i, ∀ g ∈ Hinf K, AI.actT g (z i) = z i := fun i g hg => by
    apply IsFractionRing.injective (OCb l) (Cb l)
    rw [← autCb_alg, ← hz', ← coeff_actWCbHom, ← crd_gRW, hfix g hg]
  choose y hy hy' using fun i =>
    GlobalTheory.TiltInvariants.invariant_approx l P AI K (z i) (hzf i) (N + m)
  choose w hw hw' using fun i => hgen (y i) (hy i)
  have hmem := sum_tmul_mem D hO (basisO LL) (fun i => inclW l (w i)) hw'
  refine ⟨u ^ N * ∑ i, basisO LL i ⊗ₜ[ℤ_[l]] inclW l (w i), mul_mem (pow_mem hu N) hmem,
    Near.cancel (isUnit_iff_exists_inv.2 ⟨u, hu'⟩) (k := N) ?_⟩
  refine ennreal_volume_ratio_step_cancel hu' N x _ ▸ hx' ▸ (nearPi_iff_crd AI LL s _ _).2 fun i => ?_
  have hd : AI.εroot s - 1 ∣ AI.ε - 1 :=
    εroot_sub_pow AI s ▸ dvd_pow_self _ (pow_pos (Fact.out : l.Prime).pos s).ne'
  obtain ⟨c, hc⟩ := (pow_dvd_pow_of_dvd hd (N + m)).trans (hy' i)
  refine ⟨c, ?_⟩
  rw [LinearMap.map_sub, sub_coeff_zero, hz', crd_sum, coeff_inclW, hw, ← map_sub, hc]

end Concrete

section Generic

open GlobalTheory.TorsionBoundCompare

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW inclR φR gR πA)

theorem ioE_fixed (hO : Function.Injective (algebraMap O LL)) (g : G) (hg : W.resΓ g = 1)
    (e : W.EE) : gR g (E.ioE e) = E.ioE e := by
  rw [← ioE_γ E hO, hg, map_one, AlgHom.one_apply]

theorem ioE_π : E.ioE (algebraMap (LetA O n) W.EE letπ) = inclR πA := by
  rw [E.ioE_ext, E.io_π]

def perfE (hO : Function.Injective (algebraMap O LL)) (p : ℕ) : Subring RW :=
  perfSub (φR : RW →+* RW) (modSub (E.ioE : W.EE →+* RW) p) (modSub_stable p (ioE_φ E hO))

theorem ioE_mem_perfE (hO : Function.Injective (algebraMap O LL)) (p : ℕ) (e : W.EE) :
    E.ioE e ∈ perfE E hO p := ⟨0, io_mem (E.ioE : W.EE →+* RW) p e⟩

theorem algebraMap_mem_perfE (hO : Function.Injective (algebraMap O LL)) (p : ℕ) (o : O) :
    algebraMap O RW o ∈ perfE E hO p := E.ioE.commutes o ▸ ioE_mem_perfE E hO p _

theorem io_mem_perfE (hO : Function.Injective (algebraMap O LL)) (p : ℕ) (a : LetA O n) :
    inclR (E.io a) ∈ perfE E hO p := E.ioE_ext a ▸ ioE_mem_perfE E hO p _

theorem mem_perfE_of_io (hO : Function.Injective (algebraMap O LL)) (p : ℕ) {a : LetA O n} {b : RA}
    (h : E.io a = b) : inclR b ∈ perfE E hO p := h ▸ io_mem_perfE E hO p a

theorem exists_inv_perfE (hO : Function.Injective (algebraMap O LL)) (p : ℕ) :
    ∃ u ∈ perfE E hO p, inclR πA * u = 1 := by
  obtain ⟨u, hu⟩ := W.EE_π.exists_right_inv
  exact ⟨E.ioE u, ioE_mem_perfE E hO p u, by rw [← ioE_π E, ← map_mul, hu, map_one]⟩

theorem mem_perfE_of_iterate (hO : Function.Injective (algebraMap O LL)) (p N k : ℕ) (x : RW)
    (hx : φR^[N] x = (inclR πA + 1) ^ k) : x ∈ perfE E hO p := by
  refine ⟨N, ?_⟩
  rw [RingHom.coe_pow]
  change φR^[N] x ∈ _
  rw [hx, ← ioE_π E]
  exact pow_mem (add_mem (io_mem (E.ioE : W.EE →+* RW) p _) (one_mem _)) k

theorem descent_of_tie (hO : Function.Injective (algebraMap O LL)) {p : ℕ} (hp : PD.p = p)
    (hp2 : 2 ≤ p)
    (h3 : ∀ m x, Near (inclR : RA →+* RW) p (inclR πA) m x →
      Near (inclR : RA →+* RW) p (inclR πA) (p * m) (φR x))
    (meet : ∀ x, (∀ m, Near (inclR : RA →+* RW) p (inclR πA) m x) → ∃ r, x = (p : RW) * r)
    (tf : ∀ x : RW, (p : RW) * x = 0 → x = 0)
    (sep : ∀ x : RW, (∀ k : ℕ, (p : RW) ^ k ∣ x) → x = 0)
    (hO' : ∀ c : O, (p : O) ∣ c ∨ ∃ (d : O) (k : ℕ), (p : O) = c * d ∧ (p : O) ∣ d ^ k)
    (h2 : ∀ x, (∀ g, W.resΓ g = 1 → gR g x = x) → ∀ m,
      ∃ u ∈ perfE E hO p, Near (inclR : RA →+* RW) p (inclR πA) m (x - u))
    {I : Type} [Fintype I] (M : I → I → W.EE) (c : I → W.EE) (w : I → RW)
    (hw : ∀ g, W.resΓ g = 1 → ∀ i, gR g (w i) = w i)
    (hc : ∀ i, w i = ∑ j, E.ioE (M i j) * φR (w j) + E.ioE (c i)) (i : I) :
    ∃ e, E.ioE e = w i := by
  subst hp
  haveI := PD.finK₀
  haveI : Nontrivial O := (algebraMap O LL).domain_nontrivial
  have hn : 0 < n := by rw [W.n_eq]; exact Module.finrank_pos
  haveI := W.EE_complete
  let io : W.EE →+* RW := E.ioE
  let a : LetA O n →+* W.EE := algebraMap _ _
  have hσ₀ : ∀ f, io (a f) = (inclR : RA →+* RW) (E.io f) := E.ioE_ext
  have ht : io (a letπ) = inclR πA := ioE_π E
  have hu : IsUnit (inclR πA) := ht ▸ W.EE_π.map io
  have hd : ∀ e : W.EE, ∃ f k e', e * a (letπ ^ k) - a f = (PD.p : W.EE) * e' := fun e => by
    obtain ⟨f, k, h⟩ := W.EE_dense e 1
    rw [pow_one, Ideal.mem_span_singleton] at h
    exact ⟨f, k, h⟩
  have hcoef : ∀ m f, Near (inclR : RA →+* RW) PD.p (inclR πA) m (io (a f)) →
      ∀ i, ∀ j < m, (PD.p : O) ∣ PowerSeries.coeff j (f i) := by
    refine coeff_dvd (σ := io.comp a) hσ₀ ht hu fun c h => ?_
    refine const_dvd (σ := io.comp a) hn hp2 (τ := πA) rfl h3 meet tf sep hO'
      ((GlobalTheory.EtaleExact.ioE_injective E).comp W.EE_inj) c ?_ h
    have := iter_sc_cst E hO c n
    simp only [CharP.cast_eq_zero, sub_zero] at this
    rw [RingHom.comp_apply, hσ₀]
    exact this
  let S : Subring RW := ⨅ g ∈ {g | W.resΓ g = 1},
    RingHom.eqLocus (gR g : RW →+* RW) (RingHom.id _)
  have hS : ∀ x, x ∈ S ↔ ∀ g, W.resΓ g = 1 → gR g x = x := fun x => by
    simp only [S, Subring.mem_iInf]
    rfl
  refine padic_step (io := io) (φ := (φR : RW →+* RW)) (ioE_φ E hO) tf sep
    (sat_of W.EE_π hd hcoef) S (fun e => (hS _).2 fun g hg => ioE_fixed E hO g hg e)
    (fun x hx => (hS _).2 fun g hg => ?_) M (fun c w hw hc i => ?_) c w
    (fun i => (hS _).2 fun g hg => hw g hg i) hc i
  · have := (hS _).1 hx g hg
    rw [map_mul, map_natCast] at this
    rw [← sub_eq_zero]
    apply tf
    rw [mul_sub, this, sub_self]
  · refine mem_modSub_of_limit hσ₀ ht (eq_of_near hσ₀ ht W.EE_π hd hcoef) meet _ fun m => ?_
    exact approx_step (τ := πA) rfl hu hp2 (modSub_stable PD.p (ioE_φ E hO)) h3
      (fun i j => io (M i j)) (fun i => io (c i)) w (fun i j => io_mem io _ _)
      (fun i => io_mem io _ _) (fun i j => near_zero_of hσ₀ ht hd _) hc
      (fun m i => h2 _ ((hS _).1 (hw i)) m) m i

end Generic

section Main

open GlobalTheory.Cyc

variable {l : ℕ} [Fact l.Prime]

theorem Hinf_le_GK {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL) : Hinf K ≤ GK K := by
  refine IntermediateField.fixingSubgroup_antitone (h.2.2.1.trans ?_)
  refine sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ ?_) _
  exact fun x hx => ⟨s, hx⟩

theorem resΓ_eq_one (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL) (g : ↥(GK K))
    (hg : (g : GQ l) ∈ Hinf K) : W.resΓ g = 1 := by
  have hK0 : (g : GQ l) ∈ (K0 K).fixingSubgroup :=
    IntermediateField.fixingSubgroup_antitone (inf_le_left : K0 K ≤ K.1) g.2
  have h1 : P.χQ (g : GQ l) = 1 := ((cyc_basic l P.χQ P.χQ_cyc).2.2 K g hK0).2.1 hg
  apply W.χΓ_inj
  rw [map_one]
  apply Units.ext
  apply Subtype.ext
  have := W.χΓ_res g
  rw [P.PD_χ, h1, Units.val_one, map_one] at this
  exact this

theorem frob_iter_teich (j : ℕ) (x : OCb l) :
    (frobW l)^[j] (inclW l (WittVector.teichmuller l x)) =
      inclW l (WittVector.teichmuller l (x ^ l ^ j)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, ← GlobalTheory.TorsionBoundCompare.inclW_frob,
      GlobalTheory.TorsionBoundCompare.frob_teich, ← pow_mul, pow_succ]

theorem piR_add_one_pow {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (s : ℕ) :
    ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] inclW l (WittVector.teichmuller l AI.ε) : RW LL) =
      (piR AI LL s + 1) ^ l ^ s := by
  have h1 : piR AI LL s + 1 =
      (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] inclW l (WittVector.teichmuller l (AI.εroot s)) := by
    rw [piR_eq, Algebra.TensorProduct.one_def, ← TensorProduct.tmul_add, piW, map_sub, map_one,
      sub_add_cancel]
  rw [h1, Algebra.TensorProduct.tmul_pow, one_pow, ← map_pow, ← map_pow, εroot_pow]

theorem lift_closure {LL : FinExt l} (D : Subring (RW LL)) (T : Set (OCb l))
    (h : ∀ y ∈ T, ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] inclW l (WittVector.teichmuller l y) : RW LL) ∈ D) :
    ∀ y ∈ Subring.closure T, ∃ w : Ainf l, w.coeff 0 = y ∧
      ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] inclW l w : RW LL) ∈ D := by
  let j : Ainf l →+* RW LL :=
    (Algebra.TensorProduct.includeRight : WCb l →ₐ[ℤ_[l]] RW LL).toRingHom.comp (inclW l)
  have : Subring.closure T ≤ (D.comap j).map (WittVector.constantCoeff : Ainf l →+* OCb l) :=
    Subring.closure_le.2 fun y hy =>
      ⟨WittVector.teichmuller l y, h y hy, WittVector.teichmuller_coeff_zero l y⟩
  intro y hy
  obtain ⟨w, hw, e⟩ := this hy
  exact ⟨w, e, hw⟩

set_option synthInstance.maxHeartbeats 400000 in

theorem mem_range_of_fixed : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))) (E : EtSit P AI K s LL h W) (ι : Type) [Fintype ι] (M : ι → ι → W.EE) (c : ι → W.EE) (w : ι → RW LL), (∀ g : ↥(GK K), W.resΓ g = 1 → ∀ i, AI.gRW LL (g : GQ l) (w i) = w i) → (∀ i, w i = ∑ j, E.tie.ioE (M i j) * φRW LL (w j) + E.tie.ioE (c i)) → ∀ i, ∃ e : W.EE, E.tie.ioE e = w i := by
  intro l _ P AI K s LL h W E I _ M c w hw hc i
  have hO : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  refine descent_of_tie E.tie hO (P.PD_p K) (Fact.out : l.Prime).two_le (near_φ AI LL s)
    (meet_RW AI LL s) (tf_RW LL) (GlobalTheory.EtaleExact.sep_RW LL) (dvd_or P LL) (fun x hx m => ?_)
    M c w hw hc i
  obtain ⟨u, hu, hu'⟩ := exists_inv_perfE E.tie hO l
  refine exists_near AI K LL s _ (algebraMap_mem_perfE E.tie hO l) u hu hu'
    (lift_closure _ _ ?_) (fun g hg => ?_)
    x (fun g hg => hx ⟨g, Hinf_le_GK h hg⟩ (resΓ_eq_one P K LL W _ hg)) m
  · rintro y (⟨j, rfl⟩ | ⟨z, hz, k, hk, hl, hzk, hy⟩)
    · refine mem_perfE_of_iterate E.tie hO l j (l ^ s) _ ?_
      refine (GlobalTheory.TorsionBoundCompare.tmul_iter LL j _).trans ?_
      rw [frob_iter_teich, εroot_pow]
      exact piR_add_one_pow AI LL s
    · have hint : ∀ i, W.emb i ⟨z, hz⟩ ∈ OL LL := fun i => by
        refine IsIntegral.of_pow hk ?_
        have : (⟨z, hz⟩ : ↥(K0 K)) ^ k = 1 := Subtype.ext hzk
        rw [← map_pow, this, map_one]
        exact isIntegral_one
      have h1 := E.inertia_action_on_roots ⟨z, hz⟩ k hk hl hzk y hy (fun i => ⟨_, hint i⟩) fun _ => rfl
      exact mem_perfE_of_io E.tie hO l h1
  · have h1 := ioE_fixed E.tie hO ⟨g, Hinf_le_GK h hg⟩ (resΓ_eq_one P K LL W _ hg)
      (algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) W.EE letπ)
    rw [ioE_π E.tie] at h1
    exact h1

end Main

end GlobalTheory.FrobDescent
