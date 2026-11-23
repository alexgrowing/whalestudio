import Mathlib

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation

open MvPolynomial

variable {S : Type} [CommRing S] {d : ℕ}

abbrev Io (S σ : Type) [CommRing S] : Ideal (MvPolynomial σ S) := idealOfVars σ S

def xs (S : Type) [CommRing S] {n : ℕ} (d : ℕ) (k : Fin n) : Fin d → MvPolynomial (Fin n × Fin d) S :=
  fun i => X (k, i)

def lin {n : ℕ} (A : Fin d → Fin d → S) (k : Fin n) : Fin d → MvPolynomial (Fin n × Fin d) S :=
  fun i => ∑ l, C (A i l) * X (k, l)

def ev2 {τ : Type} (h : MvPolynomial (Fin 2 × Fin d) S) (u v : Fin d → MvPolynomial τ S) : MvPolynomial τ S :=
  aeval (fun p : Fin 2 × Fin d => ![u, v] p.1 p.2) h

lemma eval_pair_coordinates (h : MvPolynomial (Fin 2 × Fin d) S) : ev2 h (xs S d 0) (xs S d 1) = h := by
  have hf : (fun p : Fin 2 × Fin d => ![xs S d 0, xs S d 1] p.1 p.2) = X := by
    funext p
    rcases p with ⟨k, i⟩
    fin_cases k <;> simp [xs]
  unfold ev2
  rw [hf, aeval_X_left_apply]

lemma aeval_eval_pair {τ τ' : Type} (g : τ → MvPolynomial τ' S) (h : MvPolynomial (Fin 2 × Fin d) S)
    (u v : Fin d → MvPolynomial τ S) :
    aeval g (ev2 h u v) = ev2 h (fun i => aeval g (u i)) (fun i => aeval g (v i)) := by
  have hf : (fun p : Fin 2 × Fin d => aeval g (![u, v] p.1 p.2)) =
      (fun p : Fin 2 × Fin d => ![fun i => aeval g (u i), fun i => aeval g (v i)] p.1 p.2) := by
    funext p
    rcases p with ⟨k, i⟩
    fin_cases k <;> simp
  unfold ev2
  rw [← AlgHom.comp_apply, comp_aeval, hf]

lemma eval_pair_one {τ : Type} (u v : Fin d → MvPolynomial τ S) : ev2 (1 : MvPolynomial (Fin 2 × Fin d) S) u v = 1 := by
  simp [ev2]

lemma eval_pair_sub {τ : Type} (h h' : MvPolynomial (Fin 2 × Fin d) S) (u v : Fin d → MvPolynomial τ S) :
    ev2 (h - h') u v = ev2 h u v - ev2 h' u v := by
  simp [ev2]

section Sub

variable {σ τ : Type}

lemma aeval_mem_pow (g : σ → MvPolynomial τ S) (hg : ∀ i, g i ∈ Io S τ) (k : ℕ) {p : MvPolynomial σ S}
    (hp : p ∈ Io S σ ^ k) : aeval g p ∈ Io S τ ^ k := by
  have h1 : Io S σ ≤ (Io S τ).comap (aeval g) := by
    show Ideal.span (Set.range X) ≤ _
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simpa using hg i
  exact (Ideal.le_comap_pow (f := aeval g) k) (Ideal.pow_right_mono h1 k hp)

lemma sub_C_mem (p : MvPolynomial σ S) : p - C (coeff 0 p) ∈ Io S σ := by
  have h := (mem_pow_idealOfVars_iff' (σ := σ) (R := S) 1 (p - C (coeff 0 p))).2 (fun x hx => by
    have hx0 : x = 0 := (Finsupp.degree_eq_zero_iff x).1 (by omega)
    subst hx0
    simp)
  simpa using h

lemma aeval_sub_aeval_mem (g g' : σ → MvPolynomial τ S) (hg : ∀ i, g i ∈ Io S τ) (hg' : ∀ i, g' i ∈ Io S τ)
    (p : MvPolynomial σ S) : aeval g p - aeval g' p ∈ Io S τ := by
  have h0 : p - C (coeff 0 p) ∈ Io S σ ^ 1 := by simpa using sub_C_mem p
  have h1 := aeval_mem_pow g hg 1 h0
  have h2 := aeval_mem_pow g' hg' 1 h0
  have h3 := sub_mem (by simpa using h1) (by simpa using h2)
  simpa [map_sub, aeval_C] using h3

lemma aeval_sub_mem_sq (g g' : σ → MvPolynomial τ S) (hg : ∀ i, g i ∈ Io S τ) (hg' : ∀ i, g' i ∈ Io S τ)
    (hgg : ∀ i, g i - g' i ∈ Io S τ ^ 2) {p : MvPolynomial σ S} (hp : p ∈ Io S σ) :
    aeval g p - aeval g' p ∈ Io S τ ^ 2 := by
  have hp' : p ∈ Ideal.span (Set.range (X : σ → MvPolynomial σ S)) := hp
  clear hp
  induction hp' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    simpa using hgg i
  | zero => simp
  | add x y _ _ hx hy =>
    have e : aeval g (x + y) - aeval g' (x + y) = (aeval g x - aeval g' x) + (aeval g y - aeval g' y) := by
      simp only [map_add]; ring
    rw [e]; exact add_mem hx hy
  | smul r x hxm hx =>
    have e : aeval g (r • x) - aeval g' (r • x) =
        (aeval g r - aeval g' r) * aeval g x + aeval g' r * (aeval g x - aeval g' x) := by
      simp only [smul_eq_mul, map_mul]; ring
    rw [e]
    refine add_mem ?_ (Ideal.mul_mem_left _ _ hx)
    rw [pow_two]
    have hx1 : x ∈ Io S σ ^ 1 := by simpa using hxm
    exact Ideal.mul_mem_mul (aeval_sub_aeval_mem g g' hg hg' r) (by simpa using aeval_mem_pow g hg 1 hx1)

lemma aeval_sub_mem_pow (g g' : σ → MvPolynomial τ S) (hg : ∀ i, g i ∈ Io S τ) (hg' : ∀ i, g' i ∈ Io S τ)
    (hgg : ∀ i, g i - g' i ∈ Io S τ ^ 2) : ∀ (k : ℕ) (p : MvPolynomial σ S), p ∈ Io S σ ^ k →
    aeval g p - aeval g' p ∈ Io S τ ^ (k + 1)
  | 0, p, _ => by simpa using aeval_sub_aeval_mem g g' hg hg' p
  | k + 1, p, hp => by
    rw [pow_succ] at hp
    refine Submodule.mul_induction_on (C := fun p => aeval g p - aeval g' p ∈ Io S τ ^ (k + 1 + 1)) hp ?_ ?_
    · intro a ha b hb
      have e : aeval g (a * b) - aeval g' (a * b) =
          (aeval g a - aeval g' a) * aeval g b + aeval g' a * (aeval g b - aeval g' b) := by
        simp only [map_mul]; ring
      rw [e]
      refine add_mem ?_ ?_
      · rw [pow_succ]
        have hb1 : b ∈ Io S σ ^ 1 := by simpa using hb
        exact Ideal.mul_mem_mul (aeval_sub_mem_pow g g' hg hg' hgg k a ha)
          (by simpa using aeval_mem_pow g hg 1 hb1)
      · have e2 : Io S τ ^ (k + 1 + 1) = Io S τ ^ k * Io S τ ^ 2 := by rw [← pow_add]
        rw [e2]
        exact Ideal.mul_mem_mul (aeval_mem_pow g' hg' k ha) (aeval_sub_mem_sq g g' hg hg' hgg hb)
    · intro x y hx hy
      have e : aeval g (x + y) - aeval g' (x + y) = (aeval g x - aeval g' x) + (aeval g y - aeval g' y) := by
        simp only [map_add]; ring
      rw [e]; exact add_mem hx hy

lemma eq_zero_of_isHomogeneous {h : MvPolynomial σ S} {j : ℕ} (hh : h.IsHomogeneous j)
    (hm : h ∈ Io S σ ^ (j + 1)) : h = 0 := by
  ext e
  rw [coeff_zero]
  by_contra hne
  have h1 := (mem_pow_idealOfVars_iff (j + 1) h).1 hm e (mem_support_iff.2 hne)
  have h2 : e.degree = j := by
    have := hh hne
    rw [Finsupp.degree_eq_weight_one]
    exact this
  omega

lemma sub_homogeneousComponent_mem {W : MvPolynomial σ S} {j : ℕ} (hW : W ∈ Io S σ ^ j) :
    W - homogeneousComponent j W ∈ Io S σ ^ (j + 1) := by
  rw [mem_pow_idealOfVars_iff'] at hW ⊢
  intro x hx
  rw [coeff_sub, coeff_homogeneousComponent]
  split_ifs with h
  · simp
  · have : x.degree < j := by omega
    simp [hW x this]

lemma aeval_double {h : MvPolynomial σ S} {j : ℕ} (hh : h.IsHomogeneous j) :
    aeval (fun i => X i + X i) h = C ((2 : S) ^ j) * h := by
  conv_lhs => rw [h.as_sum]
  conv_rhs => rw [h.as_sum]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hdeg : e.degree = j := by
    have := hh (mem_support_iff.1 he)
    rw [Finsupp.degree_eq_weight_one]
    exact this
  have h2 : ∀ i (k : ℕ), (X i + X i : MvPolynomial σ S) ^ k = C 2 ^ k * X i ^ k := by
    intro i k; rw [← two_mul, mul_pow, ← map_ofNat C 2]
  have key : e.prod (fun i k => (X i + X i : MvPolynomial σ S) ^ k) =
      C ((2 : S) ^ e.degree) * e.prod (fun i k => (X i : MvPolynomial σ S) ^ k) := by
    unfold Finsupp.prod
    simp_rw [h2]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_pow]
    rfl
  rw [aeval_monomial, monomial_eq, key, ← hdeg, algebraMap_eq]
  ring

end Sub

lemma eval_pair_homogeneous {τ : Type} {h : MvPolynomial (Fin 2 × Fin d) S} {j : ℕ} (hh : h.IsHomogeneous j)
    (u v : Fin d → MvPolynomial τ S) (hu : ∀ i, (u i).IsHomogeneous 1) (hv : ∀ i, (v i).IsHomogeneous 1) :
    (ev2 h u v).IsHomogeneous j := by
  have := hh.aeval (fun p : Fin 2 × Fin d => ![u, v] p.1 p.2) (n := 1)
    (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [hu, hv])
  rw [one_mul] at this
  exact this

lemma xs_hom {n : ℕ} (k : Fin n) (i : Fin d) : (xs S d k i).IsHomogeneous 1 := isHomogeneous_X S _

lemma lin_hom {n : ℕ} (A : Fin d → Fin d → S) (k : Fin n) (i : Fin d) : (lin A k i).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun _ _ => (isHomogeneous_X S _).C_mul _

lemma xs_mem {n : ℕ} (k : Fin n) (i : Fin d) : xs S d k i ∈ Io S (Fin n × Fin d) :=
  Ideal.subset_span ⟨_, rfl⟩

lemma lin_mem {n : ℕ} (A : Fin d → Fin d → S) (k : Fin n) (i : Fin d) : lin A k i ∈ Io S (Fin n × Fin d) :=
  Ideal.sum_mem _ fun _ _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩)

section Main

variable [Algebra ℚ S]

lemma eval_pair_additive_first {h : MvPolynomial (Fin 2 × Fin d) S}
    (hA : ev2 h (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) =
      ev2 h (xs S d 0) (xs S d 2) + ev2 h (xs S d 1) (xs S d 2))
    {τ : Type} (u u' v : Fin d → MvPolynomial τ S) :
    ev2 h (fun i => u i + u' i) v = ev2 h u v + ev2 h u' v := by
  have := congrArg (aeval (fun p : Fin 3 × Fin d => ![u, u', v] p.1 p.2)) hA
  rw [map_add, aeval_eval_pair, aeval_eval_pair, aeval_eval_pair] at this
  have e0 : (fun i => aeval (fun p : Fin 3 × Fin d => ![u, u', v] p.1 p.2) (xs S d (0 : Fin 3) i + xs S d 1 i)) =
      fun i => u i + u' i := by funext i; simp [xs]
  have e1 : (fun i => aeval (fun p : Fin 3 × Fin d => ![u, u', v] p.1 p.2) (xs S d (0 : Fin 3) i)) = u := by
    funext i; simp [xs]
  have e2 : (fun i => aeval (fun p : Fin 3 × Fin d => ![u, u', v] p.1 p.2) (xs S d (1 : Fin 3) i)) = u' := by
    funext i; simp [xs]
  have e3 : (fun i => aeval (fun p : Fin 3 × Fin d => ![u, u', v] p.1 p.2) (xs S d (2 : Fin 3) i)) = v := by
    funext i; simp [xs]
  rw [e0, e1, e2, e3] at this
  exact this

lemma symm_of {h : MvPolynomial (Fin 2 × Fin d) S} (hs : ev2 h (xs S d 1) (xs S d 0) = h) {τ : Type}
    (u v : Fin d → MvPolynomial τ S) : ev2 h u v = ev2 h v u := by
  have := aeval_eval_pair (fun p : Fin 2 × Fin d => ![u, v] p.1 p.2) h (xs S d 1) (xs S d 0)
  rw [hs] at this
  change aeval (fun p : Fin 2 × Fin d => ![u, v] p.1 p.2) h = _
  rw [this]
  congr 1 <;> funext i <;> simp [xs]

lemma lin_add_lin (A Ab : Fin d → Fin d → S) (hAA : ∀ i l, A i l + Ab i l = if i = l then 1 else 0) {n : ℕ}
    (k : Fin n) : (fun i => lin A k i + lin Ab k i) = xs S d k := by
  funext i
  simp only [lin, xs, ← Finset.sum_add_distrib, ← add_mul, ← map_add, hAA]
  simp

theorem step {P : MvPolynomial (Fin 2 × Fin d) S} {m j : ℕ} (hj1 : 1 ≤ j) (hjm : j ≤ m)
    (fF : Fin d → MvPolynomial (Fin 3 × Fin d) S)
    (hF : ∀ i, fF i - (xs S d 0 i + xs S d 1 i) ∈ Io S (Fin 3 × Fin d) ^ 2)
    (hph1 : ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2) ∈
      Io S (Fin 3 × Fin d) ^ (m + 1))
    (hsym : ev2 P (xs S d 1) (xs S d 0) - P ∈ Io S (Fin 2 × Fin d) ^ (m + 1))
    (A Ab : Fin d → Fin d → S) (hAA : ∀ i l, A i l + Ab i l = if i = l then 1 else 0)
    (aW0 aB1 : Fin d → MvPolynomial (Fin 2 × Fin d) S)
    (hW0 : ∀ i, aW0 i - lin A 0 i ∈ Io S (Fin 2 × Fin d) ^ 2)
    (hB1 : ∀ i, aB1 i - lin Ab 1 i ∈ Io S (Fin 2 × Fin d) ^ 2)
    (hbal : ev2 P aW0 (xs S d 1) - ev2 P (xs S d 0) aB1 ∈ Io S (Fin 2 × Fin d) ^ (m + 1))
    (aW : Fin d → MvPolynomial (Fin 1 × Fin d) S) (hW : ∀ i, aW i - lin A 0 i ∈ Io S (Fin 1 × Fin d) ^ 2)
    (hdiag : ev2 P (xs S d 0) aW - 1 ∈ Io S (Fin 1 × Fin d) ^ (m + 1))
    (hP : P - 1 ∈ Io S (Fin 2 × Fin d) ^ j) : P - 1 ∈ Io S (Fin 2 × Fin d) ^ (j + 1) := by
  set W := P - 1 with hWdef
  set h := homogeneousComponent j W with hhdef
  have hR : W - h ∈ Io S _ ^ (j + 1) := sub_homogeneousComponent_mem hP
  have hh : h.IsHomogeneous j := homogeneousComponent_isHomogeneous j W
  have hhI : h ∈ Io S _ ^ j := by
    have := sub_mem hP (Ideal.pow_le_pow_right (Nat.le_succ j) hR)
    simpa using this
  have hmj : ∀ {σ : Type} {p : MvPolynomial σ S}, p ∈ Io S σ ^ (m + 1) → p ∈ Io S σ ^ (j + 1) :=
    fun hp => Ideal.pow_le_pow_right (by omega) hp
  have hsq : ∀ {τ : Type} {p : MvPolynomial τ S}, p ∈ Io S τ ^ 2 → p ∈ Io S τ :=
    fun hp => Ideal.pow_le_self two_ne_zero hp
  have hPW : ∀ {τ : Type} (u v : Fin d → MvPolynomial τ S), ev2 P u v = 1 + ev2 W u v := by
    intro τ u v; rw [hWdef, eval_pair_sub, eval_pair_one]; ring
  have hTr : ∀ {τ : Type} (u v : Fin d → MvPolynomial τ S), (∀ i, u i ∈ Io S τ) → (∀ i, v i ∈ Io S τ) →
      ev2 W u v - ev2 h u v ∈ Io S τ ^ (j + 1) := by
    intro τ u v hu hv
    rw [← eval_pair_sub]
    exact aeval_mem_pow _ (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [hu, hv]) _ hR
  have hEvW : ∀ {τ : Type} (u v : Fin d → MvPolynomial τ S), (∀ i, u i ∈ Io S τ) → (∀ i, v i ∈ Io S τ) →
      ev2 W u v ∈ Io S τ ^ j := fun u v hu hv =>
    aeval_mem_pow _ (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [hu, hv]) _ hP
  have hRep : ∀ {τ : Type} (u v u' v' : Fin d → MvPolynomial τ S), (∀ i, u i ∈ Io S τ) → (∀ i, v i ∈ Io S τ) →
      (∀ i, u' i ∈ Io S τ) → (∀ i, v' i ∈ Io S τ) → (∀ i, u i - u' i ∈ Io S τ ^ 2) →
      (∀ i, v i - v' i ∈ Io S τ ^ 2) → ev2 h u v - ev2 h u' v' ∈ Io S τ ^ (j + 1) := by
    intro τ u v u' v' hu hv hu' hv' huu hvv
    exact aeval_sub_mem_pow _ _ (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [hu, hv])
      (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [hu', hv'])
      (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [huu, hvv]) j h hhI
  have hx : ∀ {n : ℕ} (k : Fin n) (i : Fin d), xs S d k i ∈ Io S (Fin n × Fin d) := fun k i => xs_mem k i
  have hl : ∀ {n : ℕ} (B : Fin d → Fin d → S) (k : Fin n) (i : Fin d), lin B k i ∈ Io S (Fin n × Fin d) :=
    fun B k i => lin_mem B k i

  have hA1 : ev2 h (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) =
      ev2 h (xs S d 0) (xs S d 2) + ev2 h (xs S d 1) (xs S d 2) := by
    have hfF : ∀ i, fF i ∈ Io S _ := fun i => by
      have := add_mem (hsq (hF i)) (add_mem (hx 0 i) (hx 1 i)); simpa using this
    have k1 : ev2 W fF (xs S d 2) - ev2 W (xs S d 0) (xs S d 2) - ev2 W (xs S d 1) (xs S d 2) ∈
        Io S _ ^ (j + 1) := by
      have e : ev2 W fF (xs S d 2) - ev2 W (xs S d 0) (xs S d 2) - ev2 W (xs S d 1) (xs S d 2) =
          (ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2)) +
            ev2 W (xs S d 0) (xs S d 2) * ev2 W (xs S d 1) (xs S d 2) := by
        rw [hPW, hPW, hPW]; ring
      rw [e]
      refine add_mem (hmj hph1) (Ideal.pow_le_pow_right (by omega : j + 1 ≤ j + j) ?_)
      rw [pow_add]
      exact Ideal.mul_mem_mul (hEvW _ _ (hx 0) (hx 2)) (hEvW _ _ (hx 1) (hx 2))
    have k3 := hRep fF (xs S d 2) (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) hfF (hx 2)
      (fun i => add_mem (hx 0 i) (hx 1 i)) (hx 2) hF (fun i => by simp)
    have hE : ev2 h (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) - ev2 h (xs S d 0) (xs S d 2) -
        ev2 h (xs S d 1) (xs S d 2) ∈ Io S _ ^ (j + 1) := by
      have e : ev2 h (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) - ev2 h (xs S d 0) (xs S d 2) -
          ev2 h (xs S d 1) (xs S d 2) =
          (ev2 W fF (xs S d 2) - ev2 W (xs S d 0) (xs S d 2) - ev2 W (xs S d 1) (xs S d 2)) -
            (ev2 W fF (xs S d 2) - ev2 h fF (xs S d 2)) + (ev2 W (xs S d 0) (xs S d 2) - ev2 h (xs S d 0) (xs S d 2)) +
            (ev2 W (xs S d 1) (xs S d 2) - ev2 h (xs S d 1) (xs S d 2)) -
            (ev2 h fF (xs S d 2) - ev2 h (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2)) := by ring
      rw [e]
      exact sub_mem (add_mem (add_mem (sub_mem k1 (hTr _ _ hfF (hx 2))) (hTr _ _ (hx 0) (hx 2)))
        (hTr _ _ (hx 1) (hx 2))) k3
    have hom : (ev2 h (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) - ev2 h (xs S d 0) (xs S d 2) -
        ev2 h (xs S d 1) (xs S d 2)).IsHomogeneous j :=
      ((eval_pair_homogeneous hh _ _ (fun i => (xs_hom 0 i).add (xs_hom 1 i)) (xs_hom 2)).sub
        (eval_pair_homogeneous hh _ _ (xs_hom 0) (xs_hom 2))).sub (eval_pair_homogeneous hh _ _ (xs_hom 1) (xs_hom 2))
    have := eq_zero_of_isHomogeneous hom hE
    rw [sub_sub, sub_eq_zero] at this
    exact this

  have hs : ev2 h (xs S d 1) (xs S d 0) = h := by
    have k : ev2 h (xs S d 1) (xs S d 0) - h ∈ Io S _ ^ (j + 1) := by
      have e : ev2 h (xs S d 1) (xs S d 0) - h = (ev2 P (xs S d 1) (xs S d 0) - P) -
          (ev2 W (xs S d 1) (xs S d 0) - ev2 h (xs S d 1) (xs S d 0)) + (W - h) := by
        rw [hPW, hWdef]; ring
      rw [e]
      exact add_mem (sub_mem (hmj hsym) (hTr _ _ (hx 1) (hx 0))) hR
    have := eq_zero_of_isHomogeneous ((eval_pair_homogeneous hh _ _ (xs_hom 1) (xs_hom 0)).sub hh) k
    exact sub_eq_zero.1 this
  have add1 : ∀ {τ : Type} (u u' v : Fin d → MvPolynomial τ S),
      ev2 h (fun i => u i + u' i) v = ev2 h u v + ev2 h u' v := fun u u' v => eval_pair_additive_first hA1 u u' v
  have symm : ∀ {τ : Type} (u v : Fin d → MvPolynomial τ S), ev2 h u v = ev2 h v u :=
    fun u v => symm_of hs u v
  have add2 : ∀ {τ : Type} (u v v' : Fin d → MvPolynomial τ S),
      ev2 h u (fun i => v i + v' i) = ev2 h u v + ev2 h u v' := by
    intro τ u v v'
    rw [symm, add1, symm v u, symm v' u]
  suffices h0 : h = 0 by
    have := add_mem hR (show h ∈ Io S _ ^ (j + 1) by rw [h0]; exact zero_mem _)
    simpa using this
  by_cases hj2 : j = 2
  · have haW : ∀ i, aW i ∈ Io S _ := fun i => by
      have := add_mem (hsq (hW i)) (hl A 0 i); simpa using this
    have haW0 : ∀ i, aW0 i ∈ Io S _ := fun i => by
      have := add_mem (hsq (hW0 i)) (hl A 0 i); simpa using this
    have haB1 : ∀ i, aB1 i ∈ Io S _ := fun i => by
      have := add_mem (hsq (hB1 i)) (hl Ab 1 i); simpa using this
    have hd1 : ev2 h (xs S d (0 : Fin 1)) (lin A 0) = 0 := by
      have k : ev2 h (xs S d (0 : Fin 1)) (lin A 0) ∈ Io S _ ^ (j + 1) := by
        have e : ev2 h (xs S d (0 : Fin 1)) (lin A 0) = (ev2 P (xs S d 0) aW - 1) -
            (ev2 W (xs S d 0) aW - ev2 h (xs S d 0) aW) - (ev2 h (xs S d 0) aW - ev2 h (xs S d 0) (lin A 0)) := by
          rw [hPW]; ring
        rw [e]
        exact sub_mem (sub_mem (hmj hdiag) (hTr _ _ (hx 0) haW))
          (hRep _ _ _ _ (hx 0) haW (hx 0) (hl A 0) (fun i => by simp) hW)
      exact eq_zero_of_isHomogeneous (eval_pair_homogeneous hh _ _ (xs_hom 0) (lin_hom A 0)) k
    have hb1 : ev2 h (lin A (0 : Fin 2)) (xs S d (1 : Fin 2)) = ev2 h (xs S d (0 : Fin 2)) (lin Ab (1 : Fin 2)) := by
      have k : ev2 h (lin A (0 : Fin 2)) (xs S d (1 : Fin 2)) - ev2 h (xs S d (0 : Fin 2)) (lin Ab (1 : Fin 2)) ∈ Io S _ ^ (j + 1) := by
        have e : ev2 h (lin A (0 : Fin 2)) (xs S d (1 : Fin 2)) - ev2 h (xs S d (0 : Fin 2)) (lin Ab (1 : Fin 2)) =
            (ev2 P aW0 (xs S d 1) - ev2 P (xs S d 0) aB1) -
            (ev2 W aW0 (xs S d 1) - ev2 h aW0 (xs S d 1)) + (ev2 W (xs S d 0) aB1 - ev2 h (xs S d 0) aB1) -
            (ev2 h aW0 (xs S d 1) - ev2 h (lin A (0 : Fin 2)) (xs S d (1 : Fin 2))) +
            (ev2 h (xs S d 0) aB1 - ev2 h (xs S d (0 : Fin 2)) (lin Ab (1 : Fin 2))) := by
          rw [hPW, hPW]; ring
        rw [e]
        exact add_mem (sub_mem (add_mem (sub_mem (hmj hbal) (hTr _ _ haW0 (hx 1))) (hTr _ _ (hx 0) haB1))
          (hRep _ _ _ _ haW0 (hx 1) (hl A 0) (hx 1) hW0 (fun i => by simp)))
          (hRep _ _ _ _ (hx 0) haB1 (hx 0) (hl Ab 1) (fun i => by simp) hB1)
      exact sub_eq_zero.1 (eq_zero_of_isHomogeneous
        ((eval_pair_homogeneous hh _ _ (lin_hom A 0) (xs_hom 1)).sub (eval_pair_homogeneous hh _ _ (xs_hom 0) (lin_hom Ab 1))) k)
    have hsub : ∀ (g : Fin 1 × Fin d → MvPolynomial (Fin 2 × Fin d) S),
        ev2 h (fun i => aeval g (xs S d (0 : Fin 1) i)) (fun i => aeval g (lin A (0 : Fin 1) i)) = 0 := by
      intro g; rw [← aeval_eval_pair, hd1, map_zero]
    have hd0 : ev2 h (xs S d (0 : Fin 2)) (lin A 0) = 0 := by
      have := hsub (fun p => xs S d (0 : Fin 2) p.2); simp [xs, lin] at this; exact this
    have hd1' : ev2 h (xs S d (1 : Fin 2)) (lin A 1) = 0 := by
      have := hsub (fun p => xs S d (1 : Fin 2) p.2); simp [xs, lin] at this; exact this
    have hd01 : ev2 h (fun i => xs S d (0 : Fin 2) i + xs S d 1 i) (fun i => lin A 0 i + lin A 1 i) = 0 := by
      have := hsub (fun p => xs S d (0 : Fin 2) p.2 + xs S d 1 p.2)
      simpa [xs, lin, mul_add, Finset.sum_add_distrib] using this
    have e1 : ev2 h (xs S d (0 : Fin 2)) (lin A (1 : Fin 2)) + ev2 h (xs S d (1 : Fin 2)) (lin A (0 : Fin 2)) = 0 := by
      have := hd01
      rw [add1, add2, add2] at this
      linear_combination this - hd0 - hd1'
    rw [symm (xs S d (1 : Fin 2)) (lin A (0 : Fin 2)), hb1] at e1
    have e2 : ev2 h (xs S d (0 : Fin 2)) (fun i => lin A (1 : Fin 2) i + lin Ab (1 : Fin 2) i) = 0 := by
      rw [add2]; linear_combination e1
    rw [lin_add_lin A Ab hAA 1, eval_pair_coordinates] at e2
    exact e2
  · have h2x : ev2 h (fun i => xs S d (0 : Fin 2) i + xs S d 0 i) (xs S d 1) = h + h := by
      rw [add1, eval_pair_coordinates]
    have h4 : ev2 h (fun i => xs S d (0 : Fin 2) i + xs S d 0 i) (fun i => xs S d 1 i + xs S d 1 i) =
        h + h + (h + h) := by
      rw [add2, h2x]
    have hf : (fun p : Fin 2 × Fin d =>
        ![fun i => xs S d (0 : Fin 2) i + xs S d 0 i, fun i => xs S d 1 i + xs S d 1 i] p.1 p.2) =
        fun p => X p + X p := by
      funext p; rcases p with ⟨k, i⟩; fin_cases k <;> simp [xs]
    have hsc : ev2 h (fun i => xs S d (0 : Fin 2) i + xs S d 0 i) (fun i => xs S d 1 i + xs S d 1 i) =
        C ((2 : S) ^ j) * h := by
      rw [← aeval_double hh]
      show aeval _ h = _
      rw [hf]
    have h4' : C ((2 : S) ^ j - 4) * h = 0 := by
      have e4 : (C (4 : S) : MvPolynomial (Fin 2 × Fin d) S) = 4 := map_ofNat C 4
      rw [map_sub, sub_mul, ← hsc, h4, e4]; ring
    have hne : (2 : ℚ) ^ j - 4 ≠ 0 := by
      intro h0
      have h1 : ((2 ^ j : ℕ) : ℚ) = ((2 ^ 2 : ℕ) : ℚ) := by push_cast; linarith
      exact hj2 (Nat.pow_right_injective (le_refl 2) (by exact_mod_cast h1))
    have hu : IsUnit (C ((2 : S) ^ j - 4) : MvPolynomial (Fin 2 × Fin d) S) := by
      have e : ((2 : S) ^ j - 4) = algebraMap ℚ S ((2 : ℚ) ^ j - 4) := by
        rw [map_sub, map_pow, map_ofNat, map_ofNat]
      rw [e]; exact ((IsUnit.mk0 _ hne).map (algebraMap ℚ S)).map C
    exact hu.mul_right_eq_zero.1 h4'

theorem unit_eq_one {P : MvPolynomial (Fin 2 × Fin d) S} {m : ℕ}
    (fF : Fin d → MvPolynomial (Fin 3 × Fin d) S)
    (hF : ∀ i, fF i - (xs S d 0 i + xs S d 1 i) ∈ Io S (Fin 3 × Fin d) ^ 2)
    (hph1 : ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2) ∈
      Io S (Fin 3 × Fin d) ^ (m + 1))
    (hsym : ev2 P (xs S d 1) (xs S d 0) - P ∈ Io S (Fin 2 × Fin d) ^ (m + 1))
    (A Ab : Fin d → Fin d → S) (hAA : ∀ i l, A i l + Ab i l = if i = l then 1 else 0)
    (aW0 aB1 : Fin d → MvPolynomial (Fin 2 × Fin d) S)
    (hW0 : ∀ i, aW0 i - lin A 0 i ∈ Io S (Fin 2 × Fin d) ^ 2)
    (hB1 : ∀ i, aB1 i - lin Ab 1 i ∈ Io S (Fin 2 × Fin d) ^ 2)
    (hbal : ev2 P aW0 (xs S d 1) - ev2 P (xs S d 0) aB1 ∈ Io S (Fin 2 × Fin d) ^ (m + 1))
    (aW : Fin d → MvPolynomial (Fin 1 × Fin d) S) (hW : ∀ i, aW i - lin A 0 i ∈ Io S (Fin 1 × Fin d) ^ 2)
    (hdiag : ev2 P (xs S d 0) aW - 1 ∈ Io S (Fin 1 × Fin d) ^ (m + 1)) :
    P - 1 ∈ Io S (Fin 2 × Fin d) ^ (m + 1) := by
  have hbase : P - 1 ∈ Io S (Fin 2 × Fin d) ^ 1 := by
    have haW : ∀ i, aW i ∈ Io S _ := fun i => by
      have := add_mem (Ideal.pow_le_self two_ne_zero (hW i)) (lin_mem A 0 i); simpa using this
    set c := coeff 0 P with hcdef
    have h1 : ev2 (P - C c) (xs S d (0 : Fin 1)) aW ∈ Io S _ := by
      have h0 : P - C c ∈ Io S (Fin 2 × Fin d) ^ 1 := by simpa using sub_C_mem P
      have := aeval_mem_pow (fun p : Fin 2 × Fin d => ![xs S d (0 : Fin 1), aW] p.1 p.2)
        (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [xs_mem, haW]) 1 h0
      rw [pow_one] at this
      exact this
    have e : ev2 P (xs S d (0 : Fin 1)) aW = ev2 (P - C c) (xs S d (0 : Fin 1)) aW + C c := by
      rw [eval_pair_sub]; simp [ev2]
    have h3 : C (c - 1) ∈ Io S (Fin 1 × Fin d) := by
      have := sub_mem (Ideal.pow_le_self (by omega : m + 1 ≠ 0) hdiag) h1
      have e2 : ev2 P (xs S d (0 : Fin 1)) aW - 1 - ev2 (P - C c) (xs S d (0 : Fin 1)) aW = C (c - 1) := by
        rw [e, map_sub, map_one]; ring
      rw [e2] at this; exact this
    have hc : c - 1 = 0 := by
      have := (C_mem_pow_idealOfVars_iff 1 (c - 1)).1 (by rw [pow_one]; exact h3)
      simpa using this
    have hc1 : c = 1 := by linear_combination hc
    have : P - 1 = P - C c := by rw [hc1, map_one]
    rw [this, pow_one]; exact sub_C_mem P
  have key : ∀ j, 1 ≤ j → j ≤ m + 1 → P - 1 ∈ Io S (Fin 2 × Fin d) ^ j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => intro _; exact hbase
    | succ n hn ih =>
      intro hn'
      exact step hn (by omega) fF hF hph1 hsym A Ab hAA aW0 aB1 hW0 hB1 hbal aW hW hdiag (ih (by omega))
  exact key (m + 1) (by omega) le_rfl

end Main

end Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
