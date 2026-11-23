import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt

set_option autoImplicit false

noncomputable section

open DividedPowers

namespace GlobalTheory.PDA

def IsExpSer {R : Type} [CommRing R] (f : PowerSeries R) : Prop :=
  PowerSeries.coeff 0 f = 1 ∧ ∀ m n, PowerSeries.coeff m f * PowerSeries.coeff n f =
    ((m + n).choose m : R) * PowerSeries.coeff (m + n) f

variable {B : Type} [CommRing B]

def PDPoly.expTerm (Q : PDPoly B) (k : ℕ) (b : B) : PowerSeries Q.P :=
  if k = 0 then 1 else
    PowerSeries.mk fun n ↦ algebraMap B Q.P (b ^ n) * ((n.uniformBell k : Q.P) * Q.e (n * k))

def PDPoly.augExp (Q : PDPoly B) (p : Q.P) : PowerSeries Q.P := (Q.e.repr p).prod Q.expTerm

open Classical in

def PDPoly.augDP (Q : PDPoly B) (n : ℕ) (p : Q.P) : Q.P :=
  if p ∈ Q.aug then PowerSeries.coeff n (Q.augExp p) else 0

open PowerSeries Finset

theorem IsExpSer.mul {R : Type} [CommRing R] {f g : PowerSeries R} (hf : IsExpSer f) (hg : IsExpSer g) :
    IsExpSer (f * g) := by
  refine ⟨by simp [PowerSeries.coeff_mul, hf.1, hg.1], fun m n ↦ ?_⟩
  simp only [PowerSeries.coeff_mul, Finset.sum_mul_sum]
  have key : ∀ x ∈ antidiagonal m, ∑ y ∈ antidiagonal n, coeff x.1 f * coeff x.2 g * (coeff y.1 f * coeff y.2 g) =
      ∑ z ∈ antidiagonal (m + n), ((z.1.choose x.1 * z.2.choose x.2 : ℕ) : R) * (coeff z.1 f * coeff z.2 g) := by
    rintro ⟨i, j⟩ hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    dsimp only at hx
    have e1 : ∀ y ∈ antidiagonal n, coeff i f * coeff j g * (coeff y.1 f * coeff y.2 g) =
        (fun z : ℕ × ℕ ↦ ((z.1.choose i * z.2.choose j : ℕ) : R) * (coeff z.1 f * coeff z.2 g))
          (i + y.1, j + y.2) := by
      intro y _
      simp only
      rw [show coeff i f * coeff j g * (coeff y.1 f * coeff y.2 g) =
        (coeff i f * coeff y.1 f) * (coeff j g * coeff y.2 g) by ring, hf.2, hg.2]
      push_cast; ring
    let F : ℕ × ℕ → R := fun z ↦ ((z.1.choose i * z.2.choose j : ℕ) : R) * (coeff z.1 f * coeff z.2 g)
    let G : ℕ × ℕ → ℕ × ℕ := fun y ↦ (i + y.1, j + y.2)
    have inj : ∀ a ∈ antidiagonal n, ∀ b ∈ antidiagonal n, G a = G b → a = b := by
      intro a _ b _ h; simp only [G, Prod.mk.injEq] at h; ext <;> omega
    refine ((Finset.sum_congr rfl e1).trans (Finset.sum_image (f := F) inj).symm).trans ?_
    refine Finset.sum_subset ?_ ?_
    · intro z hz
      simp only [Finset.mem_image, Finset.HasAntidiagonal.mem_antidiagonal] at hz ⊢
      obtain ⟨y, hy, rfl⟩ := hz
      show i + y.1 + (j + y.2) = m + n
      omega
    · rintro ⟨a, b⟩ hz hn
      simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hz
      simp only [Finset.mem_image, Finset.HasAntidiagonal.mem_antidiagonal, not_exists, not_and, G, Prod.mk.injEq] at hn
      by_cases ha : i ≤ a
      · by_cases hb : j ≤ b
        · exfalso; refine hn (a - i, b - j) ?_ ?_ ?_ <;> dsimp only <;> omega
        · simp only [F]; rw [Nat.choose_eq_zero_of_lt (by omega : b < j)]; simp
      · simp only [F]; rw [Nat.choose_eq_zero_of_lt (by omega : a < i)]; simp
  rw [Finset.sum_congr rfl key, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z hz ↦ ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hz
  rw [← Finset.sum_mul, ← Nat.cast_sum, ← Nat.add_choose_eq, hz]

theorem isExpSer_one {R : Type} [CommRing R] : IsExpSer (1 : PowerSeries R) := by
  refine ⟨by simp, fun m n ↦ ?_⟩
  simp only [PowerSeries.coeff_one]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have : m + n ≠ 0 := by omega
    simp [hm.ne', this]

theorem mk_exp_add {R : Type} [CommRing R] (u : ℕ → R)
    (hu : ∀ m n, u m * u n = ((m + n).choose m : R) * u (m + n)) (a b : R) :
    PowerSeries.mk (fun n ↦ (a + b) ^ n * u n) =
      PowerSeries.mk (fun n ↦ a ^ n * u n) * PowerSeries.mk (fun n ↦ b ^ n * u n) := by
  ext n
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mk, (Commute.all a b).add_pow', Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  simp only [PowerSeries.coeff_mk]
  rw [show a ^ x.1 * u x.1 * (b ^ x.2 * u x.2) = a ^ x.1 * b ^ x.2 * (u x.1 * u x.2) by ring, hu, hx, nsmul_eq_mul]
  ring

theorem uniformBell_mul_uniformBell (m n k : ℕ) (hk : k ≠ 0) :
    m.uniformBell k * n.uniformBell k * (m * k + n * k).choose (m * k) = (m + n).choose m * (m + n).uniformBell k := by
  have q : ∀ a : ℕ, (a.uniformBell k : ℚ) = (a * k).factorial / ((k.factorial : ℚ) ^ a * a.factorial) := by
    intro a
    rw [eq_div_iff (by positivity)]
    exact_mod_cast (by rw [← mul_assoc]; exact Nat.uniformBell_mul_eq a hk)
  have : ((m.uniformBell k * n.uniformBell k * (m * k + n * k).choose (m * k) : ℕ) : ℚ) =
      (((m + n).choose m * (m + n).uniformBell k : ℕ) : ℚ) := by
    push_cast
    rw [q, q, q, Nat.cast_add_choose, Nat.cast_add_choose, add_mul, pow_add]
    field_simp
  exact_mod_cast this

theorem choose_pow_mul_uniformBell (m K n : ℕ) (hm : m ≠ 0) (hK : K ≠ 0) :
    (m + K).choose m ^ n * n.uniformBell (m + K) =
      n.factorial * n.uniformBell m * n.uniformBell K * (n * m + n * K).choose (n * m) := by
  have q : ∀ k : ℕ, k ≠ 0 → (n.uniformBell k : ℚ) = (n * k).factorial / ((k.factorial : ℚ) ^ n * n.factorial) := by
    intro k hk
    rw [eq_div_iff (by positivity)]
    exact_mod_cast (by rw [← mul_assoc]; exact Nat.uniformBell_mul_eq n hk)
  have : ((((m + K).choose m ^ n * n.uniformBell (m + K)) : ℕ) : ℚ) =
      ((n.factorial * n.uniformBell m * n.uniformBell K * (n * m + n * K).choose (n * m) : ℕ) : ℚ) := by
    push_cast
    rw [q _ hm, q _ hK, q _ (by omega), Nat.cast_add_choose, Nat.cast_add_choose, mul_add, div_pow]
    field_simp
    ring
  exact_mod_cast this

theorem PDPoly.expTerm_of_ne (Q : PDPoly B) {k : ℕ} (hk : k ≠ 0) (b : B) :
    Q.expTerm k b = PowerSeries.mk fun n ↦ algebraMap B Q.P b ^ n * ((n.uniformBell k : Q.P) * Q.e (n * k)) := by
  simp [PDPoly.expTerm, hk, map_pow]

theorem PDPoly.coeff_expTerm (Q : PDPoly B) {k : ℕ} (hk : k ≠ 0) (b : B) (n : ℕ) :
    coeff n (Q.expTerm k b) = algebraMap B Q.P b ^ n * ((n.uniformBell k : Q.P) * Q.e (n * k)) := by
  rw [Q.expTerm_of_ne hk, coeff_mk]

theorem PDPoly.expSeq_mul (Q : PDPoly B) {k : ℕ} (hk : k ≠ 0) (m n : ℕ) :
    (m.uniformBell k : Q.P) * Q.e (m * k) * ((n.uniformBell k : Q.P) * Q.e (n * k)) =
      ((m + n).choose m : Q.P) * ((m + n).uniformBell k * Q.e ((m + n) * k)) := by
  have h := uniformBell_mul_uniformBell m n k hk
  calc _ = ((m.uniformBell k * n.uniformBell k : ℕ) : Q.P) * (Q.e (m * k) * Q.e (n * k)) := by push_cast; ring
    _ = (((m.uniformBell k * n.uniformBell k * (m * k + n * k).choose (m * k)) : ℕ) : Q.P) * Q.e (m * k + n * k) := by
        rw [Q.e_mul]; push_cast; ring
    _ = _ := by rw [h, add_mul]; push_cast; ring

theorem PDPoly.expTerm_zero (Q : PDPoly B) (k : ℕ) : Q.expTerm k 0 = 1 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [PDPoly.expTerm]
  · ext n
    rw [Q.coeff_expTerm hk, coeff_one]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [Q.e_zero, Nat.uniformBell_zero_left]
    · simp [hn]

theorem PDPoly.expTerm_add (Q : PDPoly B) (k : ℕ) (a b : B) :
    Q.expTerm k (a + b) = Q.expTerm k a * Q.expTerm k b := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [PDPoly.expTerm]
  · rw [Q.expTerm_of_ne hk, Q.expTerm_of_ne hk, Q.expTerm_of_ne hk, map_add]
    exact mk_exp_add _ (fun m n ↦ Q.expSeq_mul hk m n) _ _

theorem PDPoly.isExpSer_expTerm (Q : PDPoly B) (k : ℕ) (b : B) : IsExpSer (Q.expTerm k b) := by
  rcases eq_or_ne k 0 with rfl | hk
  · simpa [PDPoly.expTerm] using isExpSer_one
  · refine ⟨by simp [Q.coeff_expTerm hk, Q.e_zero, Nat.uniformBell_zero_left], fun m n ↦ ?_⟩
    rw [Q.coeff_expTerm hk, Q.coeff_expTerm hk, Q.coeff_expTerm hk,
      show algebraMap B Q.P b ^ m * ((m.uniformBell k : Q.P) * Q.e (m * k)) *
        (algebraMap B Q.P b ^ n * ((n.uniformBell k : Q.P) * Q.e (n * k))) =
        algebraMap B Q.P b ^ (m + n) * ((m.uniformBell k : Q.P) * Q.e (m * k) * ((n.uniformBell k : Q.P) * Q.e (n * k)))
        by ring, Q.expSeq_mul hk]
    ring

theorem PDPoly.isExpSer_prod (Q : PDPoly B) (c : ℕ →₀ B) : IsExpSer (c.prod Q.expTerm) :=
  Finset.prod_induction _ IsExpSer (fun _ _ ↦ IsExpSer.mul) isExpSer_one fun k _ ↦ Q.isExpSer_expTerm k (c k)

theorem PDPoly.isExpSer_augExp (Q : PDPoly B) (p : Q.P) : IsExpSer (Q.augExp p) := Q.isExpSer_prod _

theorem PDPoly.augExp_add (Q : PDPoly B) (p q : Q.P) : Q.augExp (p + q) = Q.augExp p * Q.augExp q := by
  rw [PDPoly.augExp, map_add, Finsupp.prod_add_index' Q.expTerm_zero Q.expTerm_add]; rfl

theorem PDPoly.augExp_zero (Q : PDPoly B) : Q.augExp 0 = 1 := by
  simp [PDPoly.augExp]

theorem PDPoly.augExp_smul_e (Q : PDPoly B) (b : B) (k : ℕ) : Q.augExp (b • Q.e k) = Q.expTerm k b := by
  rw [PDPoly.augExp, map_smul, Q.e.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
    Finsupp.prod_single_index (Q.expTerm_zero k)]

theorem PDPoly.mem_aug_iff (Q : PDPoly B) (p : Q.P) : p ∈ Q.aug ↔ Q.e.repr p 0 = 0 := by
  have hms : ∀ (q : Q.P) (n : ℕ), Q.e.repr (q * Q.e (n + 1)) 0 = 0 := by
    intro q n
    have : (Q.e.coord 0) ∘ₗ LinearMap.mulRight B (Q.e (n + 1)) = 0 := by
      refine Q.e.ext fun m ↦ ?_
      simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, Q.e_mul, ← nsmul_eq_mul, map_nsmul,
        LinearMap.zero_apply, Module.Basis.coord_apply, Module.Basis.repr_self]
      rw [Finsupp.single_eq_of_ne (by omega), smul_zero]
    exact LinearMap.congr_fun this q
  constructor
  · intro h
    have h2 : ∀ q, Q.e.repr (q * p) 0 = 0 := by
      refine Submodule.span_induction (p := fun a _ ↦ ∀ q, Q.e.repr (q * a) 0 = 0) ?_ ?_ ?_ ?_ h
      · rintro _ ⟨j, rfl⟩ q; exact hms q j
      · simp
      · intro x y _ _ hx hy q; rw [mul_add, map_add, Finsupp.add_apply, hx, hy, add_zero]
      · intro r x _ hx q; rw [smul_eq_mul, ← mul_assoc]; exact hx _
    simpa using h2 1
  · intro h
    rw [← Q.e.linearCombination_repr p, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Ideal.sum_mem _ fun n hn ↦ ?_
    rcases n with _ | n
    · exact absurd h (Finsupp.mem_support_iff.1 hn)
    · rw [Algebra.smul_def]; exact Ideal.mul_mem_left _ _ (Q.e_succ_mem_aug n)

theorem PDPoly.coeff_one_prod (Q : PDPoly B) (c : ℕ →₀ B) :
    coeff 1 (c.prod Q.expTerm) = c.sum fun k b ↦ if k = 0 then 0 else b • Q.e k := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [Finsupp.prod_add_index' Q.expTerm_zero Q.expTerm_add, Finsupp.sum_add_index' (by simp)
      (fun k a b ↦ by split_ifs <;> simp [add_smul]), ← hf, ← hg, coeff_mul,
      Finset.Nat.sum_antidiagonal_succ]
    simp [(Q.isExpSer_prod f).1, (Q.isExpSer_prod g).1, add_comm]
  | single k b =>
    rw [Finsupp.prod_single_index (Q.expTerm_zero k), Finsupp.sum_single_index (by simp)]
    rcases eq_or_ne k 0 with rfl | hk
    · simp [PDPoly.expTerm]
    · rw [Q.coeff_expTerm hk]; simp [hk, Algebra.smul_def, Nat.uniformBell_one_left]

theorem PDPoly.e_pow (Q : PDPoly B) {m : ℕ} (hm : m ≠ 0) (n : ℕ) :
    Q.e m ^ n = ((n.factorial * n.uniformBell m : ℕ) : Q.P) * Q.e (n * m) := by
  induction n with
  | zero => simp [Q.e_zero, Nat.uniformBell_zero_left]
  | succ n ih =>
    have h := uniformBell_mul_uniformBell n 1 m hm
    simp only [Nat.uniformBell_one_left, one_mul, mul_one, Nat.choose_succ_self_right] at h
    rw [pow_succ, ih, mul_assoc, Q.e_mul, ← mul_assoc, ← Nat.cast_mul, Nat.succ_mul]
    congr 2
    rw [Nat.factorial_succ, mul_assoc, h]; ring

theorem PDPoly.augExp_e (Q : PDPoly B) (k : ℕ) : Q.augExp (Q.e k) = Q.expTerm k 1 := by
  simpa using Q.augExp_smul_e 1 k

theorem PDPoly.coeff_prod_mem_aug (Q : PDPoly B) (c : ℕ →₀ B) (n : ℕ) (hn : n ≠ 0) :
    coeff n (c.prod Q.expTerm) ∈ Q.aug := by
  revert n
  refine Finset.prod_induction _ (fun f : PowerSeries Q.P ↦ ∀ n, n ≠ 0 → coeff n f ∈ Q.aug) ?_ ?_ ?_
  · intro f g hf hg n hn
    rw [coeff_mul]
    refine Ideal.sum_mem _ fun x hx ↦ ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rcases eq_or_ne x.1 0 with h0 | h0
    · exact Ideal.mul_mem_left _ _ (hg _ (by omega))
    · exact Ideal.mul_mem_right _ _ (hf _ h0)
  · intro n hn; simp [coeff_one, hn]
  · intro k _ n hn
    rcases eq_or_ne k 0 with rfl | hk
    · simp [PDPoly.expTerm, coeff_one, hn]
    · rw [Q.coeff_expTerm hk]
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (mul_ne_zero hn hk)
      rw [hj]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Q.e_succ_mem_aug j))

theorem PDPoly.coeff_augExp_smul_e_mul_e (Q : PDPoly B) (b : B) (m : ℕ) {K : ℕ} (hK : K ≠ 0) (n : ℕ) :
    coeff n (Q.augExp ((b • Q.e m) * Q.e K)) = (b • Q.e m) ^ n * coeff n (Q.augExp (Q.e K)) := by
  rw [smul_mul_assoc, Q.e_mul, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul B, smul_smul, Q.augExp_smul_e,
    Q.coeff_expTerm (by omega), Q.augExp_e, Q.coeff_expTerm hK, smul_pow, Algebra.smul_def, map_pow, map_one,
    one_pow, one_mul, map_mul, map_natCast]
  rcases eq_or_ne m 0 with rfl | hm
  · simp [Q.e_zero]
  · rw [Q.e_pow hm, show n * (m + K) = n * m + n * K from mul_add _ _ _]
    have h := choose_pow_mul_uniformBell m K n hm hK
    calc (algebraMap B Q.P b * ((m + K).choose m : Q.P)) ^ n * ((n.uniformBell (m + K) : Q.P) * Q.e (n * m + n * K))
        = algebraMap B Q.P b ^ n * (((m + K).choose m ^ n * n.uniformBell (m + K) : ℕ) : Q.P) *
            Q.e (n * m + n * K) := by push_cast; ring
      _ = algebraMap B Q.P b ^ n * ((n.factorial * n.uniformBell m * n.uniformBell K : ℕ) : Q.P) *
            (((n * m + n * K).choose (n * m) : Q.P) * Q.e (n * m + n * K)) := by rw [h]; push_cast; ring
      _ = _ := by rw [← Q.e_mul]; push_cast; ring

theorem PDPoly.coeff_augExp_mul (Q : PDPoly B) (a : Q.P) {x : Q.P} (hx : x ∈ Q.aug) (n : ℕ) :
    coeff n (Q.augExp (a * x)) = a ^ n * coeff n (Q.augExp x) := by

  have hsum : ∀ y : Q.P, ∀ s : Finset ℕ, ∀ f : ℕ → Q.P,
      (∀ i ∈ s, ∀ n, coeff n (Q.augExp (f i * y)) = f i ^ n * coeff n (Q.augExp y)) →
      ∀ n, coeff n (Q.augExp ((∑ i ∈ s, f i) * y)) = (∑ i ∈ s, f i) ^ n * coeff n (Q.augExp y) := by
    intro y s f hf
    refine Finset.sum_induction _ (fun a ↦ ∀ n, coeff n (Q.augExp (a * y)) = a ^ n * coeff n (Q.augExp y))
      ?_ ?_ hf
    · intro a a' ha ha' n
      rw [add_mul, Q.augExp_add, coeff_mul, (Commute.all a a').add_pow', Finset.sum_mul]
      refine Finset.sum_congr rfl fun z hz ↦ ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hz
      rw [ha, ha', nsmul_eq_mul,
        show a ^ z.1 * coeff z.1 (Q.augExp y) * (a' ^ z.2 * coeff z.2 (Q.augExp y)) =
          a ^ z.1 * a' ^ z.2 * (coeff z.1 (Q.augExp y) * coeff z.2 (Q.augExp y)) by ring,
        (Q.isExpSer_augExp y).2, hz]
      ring
    · intro n
      rw [zero_mul, Q.augExp_zero, coeff_one]
      rcases eq_or_ne n 0 with rfl | hn
      · simp [(Q.isExpSer_augExp y).1]
      · simp [hn]

  have hgen : ∀ k a n, coeff n (Q.augExp (a * Q.e (k + 1))) = a ^ n * coeff n (Q.augExp (Q.e (k + 1))) := by
    intro k a
    rw [← Q.e.linearCombination_repr a, Finsupp.linearCombination_apply, Finsupp.sum]
    exact hsum _ _ _ fun m _ n ↦ Q.coeff_augExp_smul_e_mul_e _ m (by omega) n
  revert a n
  refine Submodule.span_induction (p := fun x _ ↦ ∀ a n, coeff n (Q.augExp (a * x)) = a ^ n * coeff n (Q.augExp x))
    ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨k, rfl⟩; exact hgen k
  · intro a n
    rw [mul_zero, Q.augExp_zero, coeff_one]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [hn]
  · intro x y _ _ hx hy a n
    rw [mul_add, Q.augExp_add, Q.augExp_add, coeff_mul, coeff_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z hz ↦ ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hz
    rw [hx, hy, ← hz, pow_add]; ring
  · intro r x _ hx a n
    rw [smul_eq_mul, ← mul_assoc, hx (a * r) n, hx r n, mul_pow, mul_assoc]

theorem PDPoly.augDP_of_mem (Q : PDPoly B) {x : Q.P} (hx : x ∈ Q.aug) (n : ℕ) :
    Q.augDP n x = coeff n (Q.augExp x) := by
  simp [PDPoly.augDP, hx]

theorem exists_isPreDividedPowers_augmentation : ∀ (B : Type) [CommRing B] (Q : PDPoly B), ∃ η : ℕ → Q.P → Q.P, IsPreDP Q.aug η ∧
    ∀ n k : ℕ, η n (Q.e (k + 1)) = (n.uniformBell (k + 1) : Q.P) * Q.e (n * (k + 1)) := by
  intro B _ Q
  refine ⟨Q.augDP, ⟨fun n x hx ↦ by simp [PDPoly.augDP, hx], fun x hx ↦ ?_, fun x hx ↦ ?_, fun n hn x hx ↦ ?_,
    fun n x hx y hy ↦ ?_, fun n a x hx ↦ ?_, fun m n x hx ↦ ?_⟩, fun n k ↦ ?_⟩
  · rw [Q.augDP_of_mem hx]; exact (Q.isExpSer_augExp x).1
  · rw [Q.augDP_of_mem hx, PDPoly.augExp, Q.coeff_one_prod]
    have h0 := (Q.mem_aug_iff x).1 hx
    calc _ = (Q.e.repr x).sum fun k b ↦ b • Q.e k := Finsupp.sum_congr fun k hk ↦ by
            split_ifs with h
            · subst h; exact absurd h0 (Finsupp.mem_support_iff.1 hk)
            · rfl
      _ = x := by rw [← Finsupp.linearCombination_apply, Q.e.linearCombination_repr]
  · rw [Q.augDP_of_mem hx]; exact Q.coeff_prod_mem_aug _ n hn
  · rw [Q.augDP_of_mem (add_mem hx hy), Q.augExp_add, coeff_mul]
    simp only [Q.augDP_of_mem hx, Q.augDP_of_mem hy]
  · rw [Q.augDP_of_mem (Ideal.mul_mem_left _ a hx), Q.augDP_of_mem hx, Q.coeff_augExp_mul a hx]
  · rw [Q.augDP_of_mem hx, Q.augDP_of_mem hx, Q.augDP_of_mem hx]; exact (Q.isExpSer_augExp x).2 m n
  · rw [Q.augDP_of_mem (Q.e_succ_mem_aug k), Q.augExp_e, Q.coeff_expTerm (by omega), map_one, one_pow, one_mul]

end GlobalTheory.PDA
