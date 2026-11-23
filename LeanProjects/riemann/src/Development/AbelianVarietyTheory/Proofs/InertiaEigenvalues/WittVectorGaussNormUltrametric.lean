import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UltraSumLe

namespace GlobalTheory.WittGauss
open WittVector

def scaleCoeff (p : ℕ) {S : Type} [CommRing S] (t : S) (x : WittVector p S) : WittVector p S :=
  WittVector.mk p fun n => t ^ p ^ n * x.coeff n

theorem ghostComponent_scaleCoeff (p : ℕ) [Fact p.Prime] {S : Type} [CommRing S] (t : S)
    (x : WittVector p S) (n : ℕ) :
    ghostComponent n (scaleCoeff p t x) = t ^ p ^ n * ghostComponent n x := by
  simp only [ghostComponent_apply, aeval_wittPolynomial, scaleCoeff, WittVector.coeff_mk,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have h : i + (n - i) = n := by
    have := Finset.mem_range.1 hi
    omega
  rw [mul_pow, ← pow_mul, ← pow_add, h]
  ring

theorem map_scaleCoeff (p : ℕ) [Fact p.Prime] {S S' : Type} [CommRing S] [CommRing S']
    (f : S →+* S') (t : S) (x : WittVector p S) :
    WittVector.map f (scaleCoeff p t x) = scaleCoeff p (f t) (WittVector.map f x) := by
  ext n
  simp [scaleCoeff, WittVector.map_coeff]

theorem teichmuller_mul_rat (p : ℕ) [Fact p.Prime] {S : Type} (t : MvPolynomial S ℚ)
    (x : WittVector p (MvPolynomial S ℚ)) : teichmuller p t * x = scaleCoeff p t x := by
  apply (ghostMap.bijective_of_invertible p (MvPolynomial S ℚ)).1
  ext1 n
  simp only [map_mul, ghostMap_apply, ghostComponent_teichmuller, ghostComponent_scaleCoeff]

theorem teichmuller_mul_int (p : ℕ) [Fact p.Prime] {S : Type} (t : MvPolynomial S ℤ)
    (x : WittVector p (MvPolynomial S ℤ)) : teichmuller p t * x = scaleCoeff p t x := by
  refine WittVector.map_injective (MvPolynomial.map (Int.castRingHom ℚ))
    (MvPolynomial.map_injective _ Int.cast_injective) ?_
  rw [map_mul, map_teichmuller, map_scaleCoeff, teichmuller_mul_rat]

theorem teichmuller_mul_eq (p : ℕ) [Fact p.Prime] {S : Type} [CommRing S] (t : S)
    (x : WittVector p S) : teichmuller p t * x = scaleCoeff p t x := by
  obtain ⟨t, rfl⟩ := MvPolynomial.counit_surjective S t
  obtain ⟨x, rfl⟩ := WittVector.map_surjective (p := p)
    (MvPolynomial.counit S) (MvPolynomial.counit_surjective S) x
  have := congrArg (WittVector.map (MvPolynomial.counit S)) (teichmuller_mul_int p t x)
  rwa [map_mul, map_teichmuller, map_scaleCoeff] at this

section
variable {R : Type} [CommRing R] (a : R → ℝ) (hb : ∀ x, 0 ≤ a x ∧ a x ≤ 1) (h0 : a 0 = 0)
  (h1 : a 1 = 1) (hm : ∀ x y, a (x * y) = a x * a y) (ha : ∀ x y, a (x + y) ≤ max (a x) (a y))

include h0 ha in
theorem sum_le {ι : Type} (s : Finset ι) (f : ι → R) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ i ∈ s, a (f i) ≤ c) : a (∑ i ∈ s, f i) ≤ c := by
  first
  | exact @_root_.GlobalTheory.UltrametricSum.ultra_sum_le
  | exact _root_.GlobalTheory.UltrametricSum.ultra_sum_le
  | (apply _root_.GlobalTheory.UltrametricSum.ultra_sum_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.UltrametricSum.ultra_sum_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UltrametricSum.ultra_sum_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UltrametricSum.ultra_sum_le ..)

include hb h1 hm in
theorem neg_eq (x : R) : a (-x) = a x := by
  have h : a (-1) * a (-1) = 1 := by rw [← hm]; simpa using h1
  have h' : a (-1) = 1 := by nlinarith [(hb (-1)).1, (hb (-1)).2]
  rw [← neg_one_mul, hm, h', one_mul]

include h1 hm in
theorem pow_eq (x : R) (k : ℕ) : a (x ^ k) = a x ^ k := by
  induction k with
  | zero => simpa using h1
  | succ k ih => rw [pow_succ, hm, ih, pow_succ]

def weightRing (c : ℝ) (hc : 0 ≤ c) : Subring (Polynomial R) where
  carrier := {f | ∀ k, a (f.coeff k) ≤ c ^ k}
  zero_mem' k := by simpa [h0] using pow_nonneg hc k
  one_mem' k := by
    rw [Polynomial.coeff_one]
    split_ifs with h
    · simp [h, h1]
    · simpa [h0] using pow_nonneg hc k
  add_mem' {f g} hf hg k := by
    rw [Polynomial.coeff_add]
    exact (ha _ _).trans (max_le (hf k) (hg k))
  neg_mem' {f} hf k := by
    rw [Polynomial.coeff_neg, neg_eq a hb h1 hm]
    exact hf k
  mul_mem' {f g} hf hg k := by
    rw [Polynomial.coeff_mul]
    refine sum_le a h0 ha _ _ _ (pow_nonneg hc k) fun ij hij => ?_
    have e : ij.1 + ij.2 = k := by simpa using hij
    rw [hm, ← e, pow_add]
    exact mul_le_mul (hf _) (hg _) (hb _).1 (pow_nonneg hc _)

include hb h0 h1 hm ha in
theorem weight_add (p : ℕ) [Fact p.Prime] (c : ℝ) (hc : 0 ≤ c) (x y : WittVector p R)
    (hx : ∀ i, a (x.coeff i) ≤ c ^ p ^ i) (hy : ∀ i, a (y.coeff i) ≤ c ^ p ^ i) (n : ℕ) :
    a ((x + y).coeff n) ≤ c ^ p ^ n := by
  have key : ∀ z : WittVector p R, (∀ i, a (z.coeff i) ≤ c ^ p ^ i) →
      ∃ Z : WittVector p (weightRing a hb h0 h1 hm ha c hc),
        WittVector.map (weightRing a hb h0 h1 hm ha c hc).subtype Z =
          teichmuller p Polynomial.X * WittVector.map Polynomial.C z := by
    intro z hz
    refine ⟨WittVector.mk p fun i => ⟨Polynomial.X ^ p ^ i * Polynomial.C (z.coeff i), ?_⟩, ?_⟩
    · intro k
      rw [mul_comm, Polynomial.coeff_C_mul_X_pow]
      split_ifs with h
      · rw [h]; exact hz i
      · simpa [h0] using pow_nonneg hc k
    · rw [teichmuller_mul_eq]
      ext1 i
      simp [scaleCoeff, WittVector.map_coeff]
  obtain ⟨X, hX⟩ := key x hx
  obtain ⟨Y, hY⟩ := key y hy
  have h : WittVector.map (weightRing a hb h0 h1 hm ha c hc).subtype (X + Y) =
      scaleCoeff p Polynomial.X (WittVector.map Polynomial.C (x + y)) := by
    rw [← teichmuller_mul_eq, map_add, map_add, mul_add, hX, hY]
  have h2 := congrArg (fun z => WittVector.coeff z n) h
  simp only [WittVector.map_coeff, scaleCoeff, WittVector.coeff_mk] at h2
  have h3 := ((X + Y).coeff n).2 (p ^ n)
  change a (((weightRing a hb h0 h1 hm ha c hc).subtype ((X + Y).coeff n)).coeff _) ≤ _ at h3
  rwa [h2, mul_comm, Polynomial.coeff_C_mul_X_pow, if_pos rfl] at h3

include hb h0 h1 hm ha in
theorem weight_add_trunc (p : ℕ) [Fact p.Prime] (c : ℝ) (hc : 0 ≤ c) (x y : WittVector p R)
    (n : ℕ) (hx : ∀ i ≤ n, a (x.coeff i) ≤ c ^ p ^ i) (hy : ∀ i ≤ n, a (y.coeff i) ≤ c ^ p ^ i) :
    a ((x + y).coeff n) ≤ c ^ p ^ n := by
  have key : ∀ z : WittVector p R, (∀ i ≤ n, a (z.coeff i) ≤ c ^ p ^ i) →
      ∃ z' : WittVector p R, truncate (n + 1) z = truncate (n + 1) z' ∧
        ∀ i, a (z'.coeff i) ≤ c ^ p ^ i := by
    intro z hz
    refine ⟨WittVector.mk p fun i => if i ≤ n then z.coeff i else 0, ?_, fun i => ?_⟩
    · ext i
      rw [coeff_truncate, coeff_truncate, WittVector.coeff_mk, if_pos (Nat.lt_succ_iff.1 i.2)]
    · rw [WittVector.coeff_mk]
      split_ifs with h
      · exact hz i h
      · simpa [h0] using pow_nonneg hc _
  obtain ⟨x', hx1, hx2⟩ := key x hx
  obtain ⟨y', hy1, hy2⟩ := key y hy
  have h : truncate (n + 1) (x + y) = truncate (n + 1) (x' + y') := by
    rw [map_add, map_add, hx1, hy1]
  have h2 := congrArg (TruncatedWittVector.coeff (Fin.last n)) h
  rw [coeff_truncate, coeff_truncate, Fin.val_last] at h2
  rw [h2]
  exact weight_add a hb h0 h1 hm ha p c hc x' y' hx2 hy2 n

end

theorem root_pow (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (t ^ ((1 : ℝ) / (p : ℝ) ^ n)) ^ p ^ n = t := by
  rw [one_div, ← Nat.cast_pow]
  exact Real.rpow_inv_natCast_pow ht (pow_ne_zero _ hp.out.ne_zero)

theorem pow_root (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (t ^ p ^ n) ^ ((1 : ℝ) / (p : ℝ) ^ n) = t := by
  rw [one_div, ← Nat.cast_pow]
  exact Real.pow_rpow_inv_natCast ht (pow_ne_zero _ hp.out.ne_zero)

theorem coeff_eq_of_dvd (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [CharP R p]
    [PerfectRing R p] (x y : WittVector p R) (n : ℕ)
    (h : (p : WittVector p R) ^ (n + 1) ∣ x - y) : x.coeff n = y.coeff n := by
  have h1 := (mem_span_p_pow_iff_le_coeff_eq_zero (x - y) (n + 1)).1 (Ideal.mem_span_singleton.2 h)
  have h2 := (mem_ker_truncate (n + 1) (x - y)).2 h1
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h2
  have h3 := congrArg (TruncatedWittVector.coeff (Fin.last n)) h2
  rwa [coeff_truncate, coeff_truncate, Fin.val_last] at h3

theorem gaussNorm_ultrametric_submul : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [CharP R l] [PerfectRing R l] (a : R → ℝ), (∀ x, 0 ≤ a x ∧ a x ≤ 1) → a 0 = 0 → a 1 = 1 → (∀ x y, a (x * y) = a x * a y) → (∀ x y, a (x + y) ≤ max (a x) (a y)) → ∀ r : ℝ, 0 < r → r < 1 → ∀ N : WittVector l R → ℝ, (∀ x, N x = ⨆ n : ℕ, a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) → (∀ x y, N (x + y) ≤ max (N x) (N y)) ∧ (∀ x, N (-x) = N x) ∧ ∀ x y, N (x * y) ≤ N x * N y := by
  intro l hl R _ _ _ a hb h0 h1 hm ha r hr0 hr1 N hN
  have hexp : ∀ n : ℕ, (0 : ℝ) < 1 / (l : ℝ) ^ n := fun n => by
    have : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
    positivity
  have hle1 : ∀ (x : WittVector l R) (n : ℕ),
      a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n ≤ 1 := fun x n =>
    mul_le_one₀ (Real.rpow_le_one (hb _).1 (hb _).2 (hexp n).le) (pow_nonneg hr0.le _)
      (pow_le_one₀ hr0.le hr1.le)
  have hge : ∀ (x : WittVector l R) (n : ℕ),
      a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n ≤ N x := fun x n => by
    rw [hN]
    exact le_ciSup (f := fun n : ℕ => a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n)
      ⟨1, by rintro _ ⟨m, rfl⟩; exact hle1 x m⟩ n
  have hle : ∀ (x : WittVector l R) (c : ℝ),
      (∀ n, a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n ≤ c) → N x ≤ c := fun x c h => by
    rw [hN]; exact ciSup_le h
  have hnn : ∀ x, 0 ≤ N x := fun x =>
    (mul_nonneg (Real.rpow_nonneg (hb _).1 _) (pow_nonneg hr0.le _)).trans (hge x 0)
  have hadd : ∀ x y, N (x + y) ≤ max (N x) (N y) := by
    intro x y
    refine hle _ _ fun n => ?_
    set c := max (N x) (N y) with hc
    have hc0 : 0 ≤ c := (hnn x).trans (le_max_left _ _)
    have hrn : 0 < r ^ n := pow_pos hr0 n
    have key : ∀ z : WittVector l R, N z ≤ c → ∀ i ≤ n, a (z.coeff i) ≤ (c / r ^ n) ^ l ^ i := by
      intro z hz i hi
      rw [← root_pow l i _ (hb (z.coeff i)).1]
      refine pow_le_pow_left₀ (Real.rpow_nonneg (hb _).1 _) ?_ _
      rw [le_div_iff₀ hrn]
      refine le_trans ?_ ((hge z i).trans hz)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0.le hr1.le hi)
        (Real.rpow_nonneg (hb _).1 _)
    have h := weight_add_trunc a hb h0 h1 hm ha l (c / r ^ n) (by positivity) x y n
      (key x (le_max_left _ _)) (key y (le_max_right _ _))
    rw [← le_div_iff₀ hrn, ← pow_root l n (c / r ^ n) (by positivity)]
    exact Real.rpow_le_rpow (hb _).1 h (hexp n).le
  have hzero : N 0 = 0 := by
    refine le_antisymm (hle _ _ fun n => ?_) (hnn _)
    rw [WittVector.zero_coeff, h0, Real.zero_rpow (hexp n).ne', zero_mul]
  have hte : ∀ (u : R) (k : ℕ), N (teichmuller l u * (l : WittVector l R) ^ k) ≤ a u * r ^ k := by
    intro u k
    refine hle _ _ fun n => ?_
    by_cases h : n = k
    · subst h
      rw [teichmuller_mul_pow_coeff, pow_eq a h1 hm, pow_root l n _ (hb _).1]
    · rw [teichmuller_mul_pow_coeff_of_ne _ h, h0, Real.zero_rpow (hexp n).ne', zero_mul]
      exact mul_nonneg (hb _).1 (pow_nonneg hr0.le _)
  have hroot : ∀ (x : WittVector l R) (i : ℕ),
      a (((_root_.frobeniusEquiv R l).symm ^ i) (x.coeff i)) * r ^ i ≤ N x := by
    intro x i
    have e : ∀ (i : ℕ) (u : R), (((_root_.frobeniusEquiv R l).symm ^ i) u) ^ l ^ i = u := by
      intro i
      induction i with
      | zero => intro u; simp
      | succ i ih =>
        intro u
        rw [pow_succ', RingAut.mul_apply, pow_succ', pow_mul, frobeniusEquiv_symm_pow_p, ih]
    have := hge x i
    rwa [← e i (x.coeff i), pow_eq a h1 hm, pow_root l i _ (hb _).1] at this
  have hmul : ∀ x y, N (x * y) ≤ N x * N y := by
    intro x y
    refine hle _ _ fun n => ?_
    have hx := dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff x n
    have hy := dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff y n
    have hxy : ∀ x' y' : WittVector l R, (l : WittVector l R) ^ (n + 1) ∣ x - x' →
        (l : WittVector l R) ^ (n + 1) ∣ y - y' → (x * y).coeff n = (x' * y').coeff n := by
      intro x' y' h h'
      refine coeff_eq_of_dvd l _ _ n ?_
      have : x * y - x' * y' = (x - x') * y + x' * (y - y') := by ring
      rw [this]
      exact dvd_add (h.mul_right _) (h'.mul_left _)
    rw [hxy _ _ hx hy]
    refine (hge _ n).trans ?_
    have hc : 0 ≤ N x * N y := mul_nonneg (hnn x) (hnn y)
    rw [Finset.sum_mul_sum]
    refine sum_le N hzero hadd _ _ _ hc fun i _ => sum_le N hzero hadd _ _ _ hc fun j _ => ?_
    rw [mul_mul_mul_comm, ← map_mul, ← pow_add]
    refine (hte _ _).trans ?_
    rw [hm, pow_add, mul_mul_mul_comm]
    exact mul_le_mul (hroot x i) (hroot y j) (mul_nonneg (hb _).1 (pow_nonneg hr0.le _)) (hnn x)
  have hneg : ∀ x, N (-x) ≤ N x := fun x => by
    rw [← neg_one_mul]
    refine (hmul _ _).trans ?_
    exact mul_le_of_le_one_left (hnn x) (hle _ _ (hle1 _))
  refine ⟨hadd, fun x => le_antisymm (hneg x) ?_, hmul⟩
  simpa using hneg (-x)

end GlobalTheory.WittGauss
