import Formalism.FormalGroupWitt.SubstInjectiveV

noncomputable section

universe u v w

namespace Formalism.FG.SolveVAux

open MvPowerSeries

section Low

variable {R : Type u} [CommRing R] {τ : Type w}

def Low (N : ℕ) (p : MvPowerSeries τ R) : Prop :=
  ∀ d : τ →₀ ℕ, d.degree < N → coeff d p = 0

theorem low_zero (p : MvPowerSeries τ R) : Low 0 p := fun _ hd => absurd hd (Nat.not_lt_zero _)

theorem low_mono {M N : ℕ} (h : M ≤ N) {p : MvPowerSeries τ R} (hp : Low N p) : Low M p :=
  fun d hd => hp d (lt_of_lt_of_le hd h)

theorem low_of_zero (N : ℕ) : Low N (0 : MvPowerSeries τ R) := fun d _ => by simp

theorem low_add {N : ℕ} {p q : MvPowerSeries τ R} (hp : Low N p) (hq : Low N q) :
    Low N (p + q) :=
  fun d hd => by rw [map_add, hp d hd, hq d hd, add_zero]

theorem low_neg {N : ℕ} {p : MvPowerSeries τ R} (hp : Low N p) : Low N (-p) :=
  fun d hd => by rw [map_neg, hp d hd, neg_zero]

theorem low_sub {N : ℕ} {p q : MvPowerSeries τ R} (hp : Low N p) (hq : Low N q) :
    Low N (p - q) :=
  fun d hd => by rw [map_sub, hp d hd, hq d hd, sub_zero]

theorem low_mul {M N : ℕ} {p q : MvPowerSeries τ R} (hp : Low M p) (hq : Low N q) :
    Low (M + N) (p * q) := by
  classical
  intro d hd
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have hdeg : (x.1 + x.2).degree = x.1.degree + x.2.degree := map_add _ _ _
  rw [hx] at hdeg
  rcases lt_or_ge x.1.degree M with h1 | h1
  · rw [hp _ h1, zero_mul]
  · rw [hq _ (by omega), mul_zero]

theorem low_one_iff (p : MvPowerSeries τ R) : Low 1 p ↔ constantCoeff p = 0 := by
  constructor
  · intro hp
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact hp 0 (by simp)
  · intro hp d hd
    have : d = 0 := (Finsupp.degree_eq_zero_iff d).1 (by omega)
    rw [this, coeff_zero_eq_constantCoeff_apply, hp]

theorem low_mul_sub {M : ℕ} {a a' b b' : MvPowerSeries τ R} (ha : Low M (a - a'))
    (hb : Low M (b - b')) : Low M (a * b - a' * b') := by
  have e : a * b - a' * b' = (a - a') * b + a' * (b - b') := by ring
  rw [e]
  refine low_add ?_ ?_
  · simpa using low_mul ha (low_zero b)
  · simpa using low_mul (low_zero a') hb

end Low

section Prod

variable {R : Type u} [CommRing R] {ι : Type v} {τ : Type w}

def P (k : ι → MvPowerSeries τ R) (e : ι →₀ ℕ) : MvPowerSeries τ R :=
  e.prod fun s n => k s ^ n

theorem P_add (k : ι → MvPowerSeries τ R) (e₁ e₂ : ι →₀ ℕ) :
    P k (e₁ + e₂) = P k e₁ * P k e₂ :=
  Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

theorem P_single (k : ι → MvPowerSeries τ R) (i : ι) (n : ℕ) :
    P k (Finsupp.single i n) = k i ^ n :=
  Finsupp.prod_single_index (pow_zero _)

theorem P_zero (k : ι → MvPowerSeries τ R) : P k 0 = 1 := Finsupp.prod_zero_index

theorem low_pow {p : MvPowerSeries τ R} (hp : Low 1 p) (n : ℕ) : Low n (p ^ n) := by
  induction n with
  | zero => exact low_zero _
  | succ n ih => rw [pow_succ]; exact low_mul ih hp

theorem low_P {k : ι → MvPowerSeries τ R} (hk : ∀ i, Low 1 (k i)) (e : ι →₀ ℕ) :
    Low e.degree (P k e) := by
  induction e using Finsupp.induction_linear with
  | zero => exact low_zero _
  | add e₁ e₂ h₁ h₂ =>
    rw [P_add, map_add]; exact low_mul h₁ h₂
  | single i n =>
    rw [P_single, Finsupp.degree_single]; exact low_pow (hk i) n

theorem low_pow_sub₂ {M : ℕ} {k k' : ι → MvPowerSeries τ R} (hkk : ∀ i, Low M (k i - k' i))
    (e : ι →₀ ℕ) : Low M (P k e - P k' e) := by
  induction e using Finsupp.induction_linear with
  | zero => rw [P_zero, P_zero, sub_self]; exact low_of_zero _
  | add e₁ e₂ h₁ h₂ =>
    rw [P_add, P_add]; exact low_mul_sub h₁ h₂
  | single i n =>
    rw [P_single, P_single]
    induction n with
    | zero => rw [pow_zero, pow_zero, sub_self]; exact low_of_zero _
    | succ n ih => rw [pow_succ, pow_succ]; exact low_mul_sub ih (hkk i)

theorem low_pow_sub_succ {M : ℕ} {k k' : ι → MvPowerSeries τ R} (hk : ∀ i, Low 1 (k i))
    (hk' : ∀ i, Low 1 (k' i)) (hkk : ∀ i, Low M (k i - k' i)) (e : ι →₀ ℕ)
    (he : 2 ≤ e.degree) : Low (M + 1) (P k e - P k' e) := by
  classical
  have hne : e ≠ 0 := by rintro rfl; simp at he
  obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
    by_contra! hc; exact hne (Finsupp.ext hc)
  have hle : Finsupp.single i 1 ≤ e := by
    rw [Finsupp.single_le_iff]; omega
  set e' := e - Finsupp.single i 1 with he'
  have hsplit : e = e' + Finsupp.single i 1 := (tsub_add_cancel_of_le hle).symm
  have hdeg : e.degree = e'.degree + 1 := by
    conv_lhs => rw [hsplit]
    rw [map_add, Finsupp.degree_single]
  have h1 : Low 1 (P k' e') := low_mono (by omega) (low_P hk' e')
  rw [hsplit, P_add, P_add, P_single, P_single, pow_one, pow_one]
  have e2 : P k e' * k i - P k' e' * k' i =
      (P k e' - P k' e') * k i + P k' e' * (k i - k' i) := by
    ring
  rw [e2]
  refine low_add (low_mul (low_pow_sub₂ hkk e') (hk i)) ?_
  rw [add_comm]
  exact low_mul h1 (hkk i)

end Prod

section Subst

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι] {τ : Type w}

theorem hasSubst_of_low {k : ι → MvPowerSeries τ R} (hk : ∀ i, Low 1 (k i)) : HasSubst k :=
  hasSubst_of_constantCoeff_zero fun i => (low_one_iff _).1 (hk i)

theorem low_subst {k : ι → MvPowerSeries τ R} (hk : ∀ i, Low 1 (k i)) {p : MvPowerSeries ι R}
    (hp : Low 1 p) : Low 1 (subst k p) :=
  (low_one_iff _).2 (constantCoeff_subst_eq_zero (hasSubst_of_low hk)
    (fun i => (low_one_iff _).1 (hk i)) ((low_one_iff _).1 hp))

theorem low_subst_sub {M : ℕ} {k k' : ι → MvPowerSeries τ R} (hk : ∀ i, Low 1 (k i))
    (hk' : ∀ i, Low 1 (k' i)) (hkk : ∀ i, Low M (k i - k' i)) {g : MvPowerSeries ι R}
    (hg : Low 2 g) : Low (M + 1) (subst k g - subst k' g) := by
  intro d hd
  have hs := hasSubst_of_low hk
  have hs' := hasSubst_of_low hk'
  rw [map_sub, coeff_subst hs, coeff_subst hs', ← finsum_sub_distrib (coeff_subst_finite hs g d)
    (coeff_subst_finite hs' g d)]
  refine finsum_eq_zero_of_forall_eq_zero fun e => ?_
  rw [← smul_sub]
  rcases lt_or_ge e.degree 2 with he | he
  · rw [hg e he, zero_smul]
  · have := low_pow_sub_succ hk hk' hkk e he d hd
    rw [map_sub] at this
    simp only [P] at this
    rw [this, smul_zero]

end Subst

theorem degree_eq_one {ι : Type v} (d : ι →₀ ℕ) (hd : d.degree = 1) :
    ∃ i, d = Finsupp.single i 1 := by
  classical
  have hne : d ≠ 0 := by rintro rfl; simp at hd
  obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
    by_contra! hc; exact hne (Finsupp.ext hc)
  have hi1 : d i ≤ 1 := hd ▸ Finsupp.le_degree i d
  have hle : Finsupp.single i 1 ≤ d := by
    rw [Finsupp.single_le_iff]; omega
  have hsplit : d = (d - Finsupp.single i 1) + Finsupp.single i 1 :=
    (tsub_add_cancel_of_le hle).symm
  have hdeg : d.degree = (d - Finsupp.single i 1).degree + 1 := by
    conv_lhs => rw [hsplit]
    rw [map_add, Finsupp.degree_single]
  have h0 : d - Finsupp.single i 1 = 0 := (Finsupp.degree_eq_zero_iff _).1 (by omega)
  refine ⟨i, ?_⟩
  rw [hsplit, h0, zero_add]

section Main

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι] {τ : Type w}

def phi (G : ι → MvPowerSeries τ R) (g : ι → MvPowerSeries ι R) (k : ι → MvPowerSeries τ R) :
    ι → MvPowerSeries τ R :=
  fun j => G j - subst k (g j)

def seq (G : ι → MvPowerSeries τ R) (g : ι → MvPowerSeries ι R) (n : ℕ) :
    ι → MvPowerSeries τ R :=
  (phi G g)^[n] 0

def lim (G : ι → MvPowerSeries τ R) (g : ι → MvPowerSeries ι R) : ι → MvPowerSeries τ R :=
  fun i d => coeff d (seq G g (d.degree + 1) i)

theorem seq_succ (G : ι → MvPowerSeries τ R) (g : ι → MvPowerSeries ι R) (n : ℕ) :
    seq G g (n + 1) = phi G g (seq G g n) :=
  Function.iterate_succ_apply' _ _ _

variable {G : ι → MvPowerSeries τ R} {g : ι → MvPowerSeries ι R}

theorem phi_low (hG : ∀ j, Low 1 (G j)) (hg : ∀ j, Low 2 (g j)) {k : ι → MvPowerSeries τ R}
    (hk : ∀ i, Low 1 (k i)) (j : ι) : Low 1 (phi G g k j) :=
  low_sub (hG j) (low_subst hk (low_mono (by omega) (hg j)))

theorem phi_sub (hg : ∀ j, Low 2 (g j)) {M : ℕ} {k k' : ι → MvPowerSeries τ R}
    (hk : ∀ i, Low 1 (k i)) (hk' : ∀ i, Low 1 (k' i)) (hkk : ∀ i, Low M (k i - k' i)) (j : ι) :
    Low (M + 1) (phi G g k j - phi G g k' j) := by
  have e : phi G g k j - phi G g k' j = subst k' (g j) - subst k (g j) := by
    simp only [phi]; abel
  rw [e]
  refine low_subst_sub hk' hk (fun i => ?_) (hg j)
  have := low_neg (hkk i)
  rwa [neg_sub] at this

theorem seq_low (hG : ∀ j, Low 1 (G j)) (hg : ∀ j, Low 2 (g j)) (n : ℕ) (i : ι) :
    Low 1 (seq G g n i) := by
  induction n generalizing i with
  | zero => exact low_of_zero _
  | succ n ih => rw [seq_succ]; exact phi_low hG hg ih i

theorem seq_step (hG : ∀ j, Low 1 (G j)) (hg : ∀ j, Low 2 (g j)) (n : ℕ) (i : ι) :
    Low n (seq G g (n + 1) i - seq G g n i) := by
  induction n generalizing i with
  | zero => exact low_zero _
  | succ n ih =>
    have := phi_sub (G := G) hg (seq_low hG hg (n + 1)) (seq_low hG hg n) ih i
    rwa [← seq_succ, ← seq_succ] at this

theorem seq_stable (hG : ∀ j, Low 1 (G j)) (hg : ∀ j, Low 2 (g j)) (n m : ℕ) (hnm : n ≤ m)
    (i : ι) : Low n (seq G g m i - seq G g n i) := by
  induction m, hnm using Nat.le_induction with
  | base => rw [sub_self]; exact low_of_zero _
  | succ m hnm ih =>
    have e : seq G g (m + 1) i - seq G g n i =
        (seq G g (m + 1) i - seq G g m i) + (seq G g m i - seq G g n i) := by abel
    rw [e]
    exact low_add (low_mono hnm (seq_step hG hg m i)) ih

theorem coeff_lim (d : τ →₀ ℕ) (i : ι) :
    coeff d (lim G g i) = coeff d (seq G g (d.degree + 1) i) :=
  rfl

theorem lim_close (hG : ∀ j, Low 1 (G j)) (hg : ∀ j, Low 2 (g j)) (n : ℕ) (i : ι) :
    Low n (lim G g i - seq G g n i) := by
  intro d hd
  have := seq_stable hG hg (d.degree + 1) n (by omega) i d (by omega)
  rw [map_sub, sub_eq_zero] at this
  rw [map_sub, coeff_lim, this, sub_self]

theorem lim_low (hG : ∀ j, Low 1 (G j)) (hg : ∀ j, Low 2 (g j)) (i : ι) :
    Low 1 (lim G g i) := by
  have := low_add (lim_close hG hg 1 i) (seq_low hG hg 1 i)
  rwa [sub_add_cancel] at this

theorem lim_fixed (hG : ∀ j, Low 1 (G j)) (hg : ∀ j, Low 2 (g j)) (j : ι) :
    phi G g (lim G g) j = lim G g j := by
  ext d
  have h1 := phi_sub (G := G) hg (lim_low hG hg) (seq_low hG hg _) (lim_close hG hg (d.degree + 1)) j d
    (by omega)
  have h2 := lim_close hG hg (d.degree + 2) j d (by omega)
  rw [← seq_succ] at h1
  rw [map_sub, sub_eq_zero] at h1 h2
  rw [h1, h2]

end Main

end Formalism.FG.SolveVAux

namespace Formalism.FG

open MvPowerSeries SolveVAux

theorem solve_exists_vector : Formalism.FG.SolveExistsV.{u, v, w} := by
  intro R _ ι _ _ τ _ f G hf hG
  classical
  obtain ⟨hf0, hf1⟩ := hf
  set g : ι → MvPowerSeries ι R := fun j => f j - X j with hgdef
  have hg : ∀ j, Low 2 (g j) := by
    intro j d hd
    simp only [hgdef, map_sub]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hd with h0 | h1
    · have : d = 0 := (Finsupp.degree_eq_zero_iff d).1 (by omega)
      subst this
      rw [coeff_zero_eq_constantCoeff_apply, hf0 j, coeff_X,
        if_neg (fun h => (Finsupp.single_ne_zero.2 one_ne_zero) h.symm), sub_zero]
    · obtain ⟨i, rfl⟩ := degree_eq_one d h1
      rw [hf1 j i, coeff_X]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Finsupp.single_left_inj one_ne_zero]
  have hGl : ∀ j, Low 1 (G j) := fun j => (low_one_iff _).2 (hG j)
  refine ⟨lim G g, fun i => (low_one_iff _).1 (lim_low hGl hg i), fun j => ?_⟩
  have hs := hasSubst_of_low (lim_low hGl hg)
  have hfix := lim_fixed hGl hg j
  simp only [phi] at hfix
  have hfj : f j = g j + X j := by simp [hgdef]
  rw [hfj, subst_add hs, subst_X hs, ← hfix]
  abel

end Formalism.FG
