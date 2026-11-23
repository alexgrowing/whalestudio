import Formalism.GaussJetBounds.GenLogInverse
import Formalism.GaussJetBounds.StatementB

noncomputable section
open scoped BigOperators

universe u v

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

theorem special_frob_sum {R : Type*} [CommRing R] {l : ℕ} (hl : l.Prime) {ι : Type*}
    (s : Finset ι) (x : ι → R) (β : ℕ) :
    ∃ r : R, (∑ a ∈ s, x a ^ (l ^ β)) - (∑ a ∈ s, x a) ^ (l ^ β) = (l : R) * r := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp [zero_pow (pow_ne_zero _ hl.ne_zero)]⟩
  | insert a s ha ih =>
    obtain ⟨r1, h1⟩ := ih
    obtain ⟨r2, h2⟩ := exists_add_pow_prime_pow_eq hl (x a) (∑ b ∈ s, x b) β
    refine ⟨r1 - x a * (∑ b ∈ s, x b) * r2, ?_⟩
    rw [Finset.sum_insert ha, Finset.sum_insert ha, h2]
    linear_combination h1

theorem frobenius_congruence : FrobCong.{u, v} := by
  intro R _ l hl ι _ u w j β
  obtain ⟨r, h⟩ := special_frob_sum hl Finset.univ (fun a => u a ^ (l ^ j) * w a) β
  refine ⟨r, ?_⟩
  rw [← h]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_pow, ← pow_mul, ← pow_add]

theorem special_det_monomial_ne_zero {n σ R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    [Nontrivial R] (E : n → n → σ →₀ ℕ)
    (hE : Function.Injective fun p : Equiv.Perm n => ∑ c, E (p c) c) :
    (Matrix.of fun r c => (MvPolynomial.monomial (E r c) (1 : R))).det ≠ 0 := by
  classical
  intro h
  have h2 := congrArg (MvPolynomial.coeff (∑ c, E c c)) h
  rw [Matrix.det_apply, MvPolynomial.coeff_sum, MvPolynomial.coeff_zero] at h2
  simp only [Matrix.of_apply, ← MvPolynomial.monomial_sum_one] at h2
  rw [Finset.sum_eq_single (1 : Equiv.Perm n)] at h2
  · simp [MvPolynomial.coeff_monomial] at h2
  · intro p _ hp
    have hne : ∑ c, E (p c) c ≠ ∑ c, E c c := fun he => hp (hE (by simpa using he))
    rcases Int.units_eq_one_or (Equiv.Perm.sign p) with hs | hs <;>
      simp [hs, MvPolynomial.coeff_monomial, hne]
  · simp

theorem special_independence : SpecialIndep := by
  intro l hl J j hj
  have hM : (Matrix.of fun (i a : Fin J) =>
      (MvPolynomial.X a : MvPolynomial (Fin J) (ZMod l)) ^ (l ^ j i)) =
      Matrix.of fun r c => MvPolynomial.monomial (Finsupp.single c (l ^ j r)) (1 : ZMod l) := by
    ext r c; simp [MvPolynomial.X_pow_eq_monomial]
  rw [hM]
  refine special_det_monomial_ne_zero _ ?_
  intro p q h
  simp only at h
  ext c
  have hc := DFunLike.congr_fun h c
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at hc
  exact congrArg _ (hj (Nat.pow_right_injective hl.out.two_le hc))

theorem special_rank : SpecialRank := by
  intro l hl T _ _ J j hj N0 hN
  have hcard : Fintype.card (Σ t, Fin (J t)) ≤ Fintype.card (Fin N0) := by
    simpa [Fintype.card_sigma] using hN
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine ⟨f, f.injective, ?_⟩
  set g : (Σ t, Fin (J t)) → ℕ := fun r => l ^ j r.1 r.2 with hg
  have hM : (Matrix.of fun (r c : Σ t, Fin (J t)) =>
      (MvPolynomial.X (r.1, f c) : MvPolynomial (T × Fin N0) (ZMod l)) ^ (l ^ j r.1 r.2)) =
      Matrix.of fun r c => MvPolynomial.monomial (Finsupp.single (r.1, f c) (g r)) (1 : ZMod l) := by
    ext r c; simp [MvPolynomial.X_pow_eq_monomial, hg]
  rw [hM]
  refine special_det_monomial_ne_zero _ ?_
  have hS : ∀ (p : Equiv.Perm (Σ t, Fin (J t))) (t : T) (c : Σ t, Fin (J t)),
      (∑ c', Finsupp.single ((p c').1, f c') (g (p c'))) (t, f c) =
        if (p c).1 = t then g (p c) else 0 := by
    intro p t c
    rw [Finsupp.finsetSum_apply, Finset.sum_eq_single c]
    · simp only [Finsupp.single_apply, Prod.mk.injEq, and_true]
    · intro c' _ hc'
      rw [Finsupp.single_apply, if_neg]
      intro he
      exact hc' (f.injective (Prod.mk.inj he).2)
    · simp
  have hgpos : ∀ r, g r ≠ 0 := fun r => pow_ne_zero _ hl.out.ne_zero
  have hginj : ∀ a b : (Σ t, Fin (J t)), a.1 = b.1 → g a = g b → a = b := by
    rintro ⟨t, x⟩ ⟨t', y⟩ h1 h2
    simp only at h1
    subst h1
    have h3 : j t x = j t y := Nat.pow_right_injective hl.out.two_le h2
    rw [hj t h3]
  intro p q h
  simp only at h
  ext1 c
  have hc := DFunLike.congr_fun h ((p c).1, f c)
  rw [hS p, hS q, if_pos rfl] at hc
  by_cases ht : (q c).1 = (p c).1
  · rw [if_pos ht] at hc
    exact hginj _ _ ht.symm hc
  · rw [if_neg ht] at hc
    exact absurd hc (hgpos _)

section Pure

variable {R : Type*} [CommRing R] {σ : Type*} [Fintype σ] [DecidableEq σ] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

def spLdeg (lt : ι → σ) (t : σ) (n : ι →₀ ℕ) : ℕ := ∑ k, if lt k = t then n k else 0

theorem spLdeg_add (lt : ι → σ) (t : σ) (n n' : ι →₀ ℕ) :
    spLdeg lt t (n + n') = spLdeg lt t n + spLdeg lt t n' := by
  unfold spLdeg
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

theorem spLdeg_single (lt : ι → σ) (t : σ) (k : ι) (c : ℕ) :
    spLdeg lt t (Finsupp.single k c) = if lt k = t then c else 0 := by
  unfold spLdeg
  rw [Finset.sum_eq_single k]
  · simp
  · intro k' _ hk'
    simp [Ne.symm hk']
  · simp

theorem spLdeg_zero (lt : ι → σ) (t : σ) : spLdeg lt t 0 = 0 := by
  simp [spLdeg]

theorem spLdeg_eq_zero (lt : ι → σ) (n : ι →₀ ℕ) (k : ι) (h : spLdeg lt (lt k) n = 0) :
    n k = 0 := by
  unfold spLdeg at h
  have := (Finset.sum_eq_zero_iff.mp h) k (Finset.mem_univ _)
  simpa using this

variable (lt : ι → σ) (N : σ → ι → R)

theorem spCoeff_lin (s : σ) (n : ι →₀ ℕ) :
    MvPowerSeries.coeff n (∑ k, MvPowerSeries.C (N s k) * MvPowerSeries.X k) =
      ∑ k, N s k * if n = Finsupp.single k 1 then 1 else 0 := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]

theorem spCoeff_lin_ne (s : σ) (n : ι →₀ ℕ)
    (h : MvPowerSeries.coeff n (∑ k, MvPowerSeries.C (N s k) * MvPowerSeries.X k) ≠ 0) :
    ∃ k, N s k ≠ 0 ∧ n = Finsupp.single k 1 := by
  rw [spCoeff_lin] at h
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  by_cases he : n = Finsupp.single k 1
  · rw [if_pos he, mul_one] at hk
    exact ⟨k, hk, he⟩
  · rw [if_neg he, mul_zero] at hk
    exact absurd rfl hk

variable {lt N} (hN : ∀ s k, N s k ≠ 0 → lt k = s)
include hN

theorem spPow_ldeg (s : σ) (e : ℕ) (n : ι →₀ ℕ)
    (h : MvPowerSeries.coeff n ((∑ k, MvPowerSeries.C (N s k) * MvPowerSeries.X k) ^ e) ≠ 0) :
    ∀ t, spLdeg lt t n = if t = s then e else 0 := by
  induction e generalizing n with
  | zero =>
    rw [pow_zero, MvPowerSeries.coeff_one] at h
    split_ifs at h with hn
    · intro t; subst hn; rw [spLdeg_zero]; split_ifs <;> rfl
    · exact absurd rfl h
  | succ e ih =>
    rw [pow_succ, MvPowerSeries.coeff_mul] at h
    obtain ⟨p, hp, hp'⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h1 : MvPowerSeries.coeff p.1 ((∑ k, MvPowerSeries.C (N s k) * MvPowerSeries.X k) ^ e) ≠ 0 :=
      left_ne_zero_of_mul hp'
    have h2 := right_ne_zero_of_mul hp'
    obtain ⟨k, hk, hk2⟩ := spCoeff_lin_ne N s p.2 h2
    have hks := hN s k hk
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    intro t
    rw [← hp, spLdeg_add, ih p.1 h1 t, hk2, spLdeg_single, hks]
    split_ifs with h3 h4 h4 <;> first | omega | (subst h3; exact absurd rfl h4) | exact absurd h4.symm h3

theorem spProd_ldeg (S : Finset σ) (e : σ → ℕ) (n : ι →₀ ℕ)
    (h : MvPowerSeries.coeff n
      (∏ t ∈ S, (∑ k, MvPowerSeries.C (N t k) * MvPowerSeries.X k) ^ e t) ≠ 0) :
    ∀ t, spLdeg lt t n = if t ∈ S then e t else 0 := by
  induction S using Finset.induction_on generalizing n with
  | empty =>
    rw [Finset.prod_empty, MvPowerSeries.coeff_one] at h
    split_ifs at h with hn
    · intro t; subst hn; rw [spLdeg_zero]; simp
    · exact absurd rfl h
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, MvPowerSeries.coeff_mul] at h
    obtain ⟨p, hp, hp'⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h1 := left_ne_zero_of_mul hp'
    have h2 := right_ne_zero_of_mul hp'
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    intro t
    rw [← hp, spLdeg_add, spPow_ldeg hN a (e a) p.1 h1 t, ih p.2 h2 t]
    by_cases hta : t = a
    · subst hta; simp [ha]
    · simp [hta]

theorem spPow_single (s : σ) (i : ι) (a : ℕ) :
    MvPowerSeries.coeff (Finsupp.single i a)
      ((∑ k, MvPowerSeries.C (N s k) * MvPowerSeries.X k) ^ a) = N s i ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ, MvPowerSeries.coeff_mul,
      Finset.sum_eq_single (Finsupp.single i a, Finsupp.single i 1)]
    · rw [ih, spCoeff_lin, pow_succ]
      congr 1
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hk
        rw [if_neg, mul_zero]
        intro he
        exact hk ((Finsupp.single_left_inj one_ne_zero).mp he).symm
      · simp
    · rintro ⟨p1, p2⟩ hp hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      by_cases h2 : MvPowerSeries.coeff p2 (∑ k, MvPowerSeries.C (N s k) * MvPowerSeries.X k) = 0
      · rw [h2, mul_zero]
      · exfalso
        obtain ⟨k, -, hk2⟩ := spCoeff_lin_ne N s p2 h2
        subst hk2
        have hki : k = i := by
          by_contra hki
          have := DFunLike.congr_fun hp k
          simp [Ne.symm hki] at this
        subst hki
        apply hne
        have : p1 = Finsupp.single k a := by
          rw [show a + 1 = a + 1 from rfl, Finsupp.single_add] at hp
          exact add_right_cancel hp
        rw [this]
    · intro h
      exfalso; apply h
      rw [Finset.HasAntidiagonal.mem_antidiagonal, ← Finsupp.single_add]

theorem spPair (i j : ι) (a b : ℕ) (hij : lt i ≠ lt j) :
    MvPowerSeries.coeff (Finsupp.single i a + Finsupp.single j b)
      ((∑ k, MvPowerSeries.C (N (lt i) k) * MvPowerSeries.X k) ^ a *
        (∑ k, MvPowerSeries.C (N (lt j) k) * MvPowerSeries.X k) ^ b) =
      N (lt i) i ^ a * N (lt j) j ^ b := by
  rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single (Finsupp.single i a, Finsupp.single j b)]
  · rw [spPow_single hN, spPow_single hN]
  · rintro ⟨p1, p2⟩ hp hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    by_cases h1 : MvPowerSeries.coeff p1
        ((∑ k, MvPowerSeries.C (N (lt i) k) * MvPowerSeries.X k) ^ a) = 0
    · rw [h1, zero_mul]
    by_cases h2 : MvPowerSeries.coeff p2
        ((∑ k, MvPowerSeries.C (N (lt j) k) * MvPowerSeries.X k) ^ b) = 0
    · rw [h2, mul_zero]
    exfalso
    have l1 := spPow_ldeg hN (lt i) a p1 h1
    have l2 := spPow_ldeg hN (lt j) b p2 h2
    have z1 : ∀ k, lt k ≠ lt i → p1 k = 0 := fun k hk =>
      spLdeg_eq_zero lt p1 k (by rw [l1, if_neg hk])
    have z2 : ∀ k, lt k ≠ lt j → p2 k = 0 := fun k hk =>
      spLdeg_eq_zero lt p2 k (by rw [l2, if_neg hk])
    have e1 : p1 = Finsupp.single i a := by
      ext k
      have hk := DFunLike.congr_fun hp k
      simp only [Finsupp.add_apply] at hk
      by_cases hki : lt k = lt i
      · have hkj : lt k ≠ lt j := hki ▸ hij
        have hkj' : j ≠ k := fun h => hkj (h ▸ rfl)
        rw [z2 k hkj, add_zero] at hk
        rw [hk]; simp [Finsupp.single_apply, hkj']
      · have hki' : i ≠ k := fun h => hki (h ▸ rfl)
        rw [z1 k hki, Finsupp.single_apply, if_neg hki']
    have e2 : p2 = Finsupp.single j b := by
      rw [e1] at hp; exact add_left_cancel hp
    exact hne (by rw [e1, e2])
  · intro h; exfalso; apply h; rw [Finset.HasAntidiagonal.mem_antidiagonal]

theorem spCore (f : MvPowerSeries σ R) (i j : ι) (a b : ℕ) (hij : lt i ≠ lt j) :
    MvPowerSeries.coeff (Finsupp.single i a + Finsupp.single j b)
      (MvPowerSeries.subst (fun s => ∑ k, MvPowerSeries.C (N s k) * MvPowerSeries.X k) f) =
      MvPowerSeries.coeff (Finsupp.single (lt i) a + Finsupp.single (lt j) b) f *
        (N (lt i) i ^ a * N (lt j) j ^ b) := by
  have hsub : MvPowerSeries.HasSubst
      (fun s => ∑ k, MvPowerSeries.C (N s k) * MvPowerSeries.X k : σ → MvPowerSeries ι R) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by simp
  rw [MvPowerSeries.coeff_subst hsub,
    finsum_eq_single _ (Finsupp.single (lt i) a + Finsupp.single (lt j) b)]
  · rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_single_index (by rw [pow_zero]), Finsupp.prod_single_index (by rw [pow_zero]),
      smul_eq_mul, spPair hN i j a b hij]
  · intro dd hdd
    have hz : MvPowerSeries.coeff (Finsupp.single i a + Finsupp.single j b)
        (dd.prod fun s e => (∑ k, MvPowerSeries.C (N s k) * MvPowerSeries.X k) ^ e) = 0 := by
      by_contra hne
      apply hdd
      have hl := spProd_ldeg hN dd.support dd _ hne
      ext t
      have ht := hl t
      rw [spLdeg_add, spLdeg_single, spLdeg_single] at ht
      have hdt : (if t ∈ dd.support then dd t else 0) = dd t := by
        split_ifs with hm
        · rfl
        · exact (Finsupp.notMem_support_iff.mp hm).symm
      rw [hdt] at ht
      rw [← ht, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
    rw [hz, smul_zero]

end Pure

theorem pure_weight_formula : PureFormula.{u, v} := by
  intro K _ l d N0 N1 _ _ ι _ _ lt M hM be i j α β hij
  unfold bSum pureMon
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ab _ => ?_
  exact spCore (N := fun s k => M (s, ab.1, ab.2) k) (fun s k h => hM _ _ h) be i j _ _ hij

section Minor

variable {R : Type*} [CommRing R] {m p : ℕ}

def spV (top : Fin (p + 1) → R) (o : Option (Fin m)) (c : Fin (p + 1)) :
    MvPolynomial (Fin m × Fin (p + 1)) R :=
  o.elim (MvPolynomial.C (top c)) (fun k => MvPolynomial.X (k, c))

def spEx (o : Option (Fin m)) (c : Fin (p + 1)) : Fin m × Fin (p + 1) →₀ ℕ :=
  o.elim 0 (fun k => Finsupp.single (k, c) 1)

def spCo (top : Fin (p + 1) → R) (o : Option (Fin m)) (c : Fin (p + 1)) : R :=
  o.elim (top c) (fun _ => 1)

theorem spV_eq (top : Fin (p + 1) → R) (o : Option (Fin m)) (c : Fin (p + 1)) :
    spV top o c = MvPolynomial.monomial (spEx o c) (spCo top o c) := by
  cases o
  · show MvPolynomial.C (top c) = MvPolynomial.monomial 0 (top c)
    exact MvPolynomial.C_apply
  · simp [spV, spEx, spCo, MvPolynomial.X]

theorem spEx_apply (o : Option (Fin m)) (c c' : Fin (p + 1)) (k : Fin m) :
    spEx o c (k, c') = if o = some k ∧ c = c' then 1 else 0 := by
  cases o
  · simp [spEx]
  · simp [spEx, Finsupp.single_apply]

theorem spMinor (top : Fin (p + 1) → R) (A : Matrix (Fin (p + 1)) (Fin (p + 1))
      (MvPolynomial (Fin m × Fin (p + 1)) R)) (cf : Fin (p + 1) → Option (Fin m) → R)
    (hA : ∀ i c, A i c = ∑ o, MvPolynomial.C (cf i o) * spV top o c) :
    ∀ mono ∈ A.det.support, ∀ k : Fin m, (∑ c : Fin (p + 1), mono (k, c)) ≤ 1 := by
  classical
  have hrow : A = fun i => ∑ o,
      (MvPolynomial.C (cf i o) : MvPolynomial (Fin m × Fin (p + 1)) R) • spV top o := by
    funext i c
    rw [hA]
    simp [Finset.sum_apply, smul_eq_mul]
  have hdet : A.det = ∑ r : Fin (p + 1) → Option (Fin m),
      (∏ i, (MvPolynomial.C (cf i (r i)) : MvPolynomial (Fin m × Fin (p + 1)) R)) •
        (Matrix.of fun i => spV top (r i)).det := by
    rw [hrow]
    show Matrix.detRowAlternating (fun i => ∑ o,
      (MvPolynomial.C (cf i o) : MvPolynomial (Fin m × Fin (p + 1)) R) • spV top o) = _
    rw [← AlternatingMap.coe_multilinearMap, MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [MultilinearMap.map_smul_univ]
    rfl
  intro mono hmono k
  rw [hdet] at hmono
  obtain ⟨r, -, hr⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hmono)
  have hr' : mono ∈ (Matrix.of fun i => spV top (r i)).det.support := by
    rw [← map_prod, smul_eq_mul, MvPolynomial.C_mul'] at hr
    exact MvPolynomial.support_smul hr
  by_cases hinj : Function.Injective r
  · rw [Matrix.det_apply] at hr'
    obtain ⟨s, -, hs⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hr')
    have hs' : mono ∈ (∏ c, (Matrix.of fun i => spV top (r i)) (s c) c).support := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h | h
      · rwa [h, one_smul] at hs
      · rwa [h, Units.neg_smul, one_smul, MvPolynomial.support_neg] at hs
    simp only [Matrix.of_apply, spV_eq, ← MvPolynomial.monomial_sum_prod] at hs'
    have he := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hs')
    subst he
    have hval : ∀ c, (∑ c', spEx (r (s c')) c') (k, c) = if r (s c) = some k then 1 else 0 := by
      intro c
      rw [Finsupp.finsetSum_apply, Finset.sum_eq_single c]
      · rw [spEx_apply]; simp
      · intro c' _ hc'
        rw [spEx_apply]; simp [hc']
      · simp
    simp only [hval]
    rw [Finset.sum_boole]
    simp only [Nat.cast_id]
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact s.injective (hinj (ha.trans hb.symm))
  · exfalso
    simp only [Function.Injective, not_forall] at hinj
    obtain ⟨i1, i2, h12, hne⟩ := hinj
    have h0 : (Matrix.of fun i => spV top (r i)).det = 0 :=
      Matrix.det_zero_of_row_eq hne (by show spV top (r i1) = spV top (r i2); rw [h12])
    rw [h0] at hr'
    simp at hr'

end Minor

theorem minor_degree_bound : MinorDeg.{u} := by
  intro R _ m p top T mono hmono k
  classical
  refine spMinor top _ (fun i o => Fin.cases (o.elim 1 (fun _ => 0)) (fun i' => o.elim 0 (T i')) i)
    ?_ mono hmono k
  intro i c
  refine Fin.cases ?_ (fun i' => ?_) i
  · simp [spV, Fintype.sum_option]
  · simp [spV, Fintype.sum_option]

end Formalism.DworkPowerSeriesWeights
