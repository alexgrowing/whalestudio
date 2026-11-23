import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIdealLifts.NilpotentDividedPowerTrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPreDividedPowersOfGenerators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowerEvalTwoVarsRingHom

set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA PositivityTheory.JLift

namespace GlobalTheory.CompanionTheory.JLiftDP

section Comp

open MvPolynomial Finset

def dpBas2 (p : ℕ × ℕ) : MvPolynomial (Fin 2) ℚ :=
  ((p.1.factorial : ℚ)⁻¹ • X 0 ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • X 1 ^ p.2)

theorem preDP_eval_zero {B : Type} [CommRing B] {J : Ideal B} {γ : ℕ → B → B} (h : IsPreDP J γ)
    {n : ℕ} (hn : n ≠ 0) : γ n 0 = 0 := by
  have := h.mul n 0 0 J.zero_mem
  rwa [mul_zero, zero_pow hn, zero_mul] at this

theorem preDP_comp_add {B : Type} [CommRing B] {J : Ideal B} {γ : ℕ → B → B} (h : IsPreDP J γ)
    {x y : B} (hx : x ∈ J) (hy : y ∈ J)
    (Px : ∀ m n : ℕ, n ≠ 0 → γ m (γ n x) = (m.uniformBell n : B) * γ (m * n) x)
    (Py : ∀ m n : ℕ, n ≠ 0 → γ m (γ n y) = (m.uniformBell n : B) * γ (m * n) y)
    (m n : ℕ) (hn : n ≠ 0) : γ m (γ n (x + y)) = (m.uniformBell n : B) * γ (m * n) (x + y) := by
  classical
  set D := Submodule.span ℤ (Set.range dpBas2) with hD
  obtain ⟨φ, hφb, hφ2, hφz⟩ : ∃ φ : MvPolynomial (Fin 2) ℚ → B,
      (∀ a c : ℕ, φ (dpBas2 (a, c)) = γ a x * γ c y) ∧
      (∀ d ∈ D, ∀ e ∈ D, φ (d + e) = φ d + φ e ∧ d * e ∈ D ∧ φ (d * e) = φ d * φ e) ∧
      (∀ z : ℤ, ∀ d ∈ D, φ (z • d) = z • φ d) :=
    GlobalTheory.dpEval_two B (fun a ↦ γ a x) (fun c ↦ γ c y) (h.zero x hx) (h.zero y hy)
      (fun a b ↦ h.mul_dpow a b x hx) (fun a b ↦ h.mul_dpow a b y hy)
  let Γ : DividedPowers (⊤ : Ideal (MvPolynomial (Fin 2) ℚ)) := RatAlgebra.dividedPowers ⊤
  have top : ∀ q : MvPolynomial (Fin 2) ℚ, q ∈ (⊤ : Ideal _) := fun _ ↦ Submodule.mem_top
  have hΓ : ∀ (k : ℕ) (q : MvPolynomial (Fin 2) ℚ), Γ.dpow k q = (k.factorial : ℚ)⁻¹ • q ^ k := fun k q ↦ by
    rw [RatAlgebra.dpow_eq_inv_fact_smul _ Γ (top q), Ring.inverse_eq_inv']
  have hbasΓ : ∀ p : ℕ × ℕ, dpBas2 p = Γ.dpow p.1 (X 0) * Γ.dpow p.2 (X 1) := fun p ↦ by
    rw [dpBas2, hΓ, hΓ]
  have hX0 : ∀ a, Γ.dpow a (X 0) = dpBas2 (a, 0) := fun a ↦ by
    rw [hbasΓ, Γ.dpow_zero (top _), mul_one]
  have hX1 : ∀ c, Γ.dpow c (X 1) = dpBas2 (0, c) := fun c ↦ by
    rw [hbasΓ, Γ.dpow_zero (top _), one_mul]
  have hbasΓ' : ∀ a c, dpBas2 (a, c) = Γ.dpow a (X 0) * Γ.dpow c (X 1) := fun a c ↦ hbasΓ (a, c)
  have hDb : ∀ p, dpBas2 p ∈ D := fun p ↦ Submodule.subset_span ⟨p, rfl⟩
  have hone : dpBas2 (0, 0) = 1 := by simp [dpBas2]
  have hφ1 : φ 1 = 1 := by rw [← hone, hφb, h.zero x hx, h.zero y hy, one_mul]
  have hD1 : (1 : MvPolynomial (Fin 2) ℚ) ∈ D := hone ▸ hDb _
  have hφ0 : φ 0 = 0 := by
    have := (hφ2 0 D.zero_mem 0 D.zero_mem).1
    rw [add_zero] at this
    exact left_eq_add.mp this
  have hpow : ∀ d ∈ D, ∀ k : ℕ, d ^ k ∈ D ∧ φ (d ^ k) = φ d ^ k := by
    intro d hd k
    induction k with
    | zero => simpa using ⟨hD1, hφ1⟩
    | succ k ih =>
      obtain ⟨_, h2, h3⟩ := hφ2 _ ih.1 d hd
      rw [pow_succ, pow_succ, h3, ih.2]
      exact ⟨h2, rfl⟩
  have hsum : ∀ (t : Finset (ℕ × ℕ)) (f : ℕ × ℕ → MvPolynomial (Fin 2) ℚ), (∀ i ∈ t, f i ∈ D) →
      (∑ i ∈ t, f i) ∈ D ∧ φ (∑ i ∈ t, f i) = ∑ i ∈ t, φ (f i) := by
    intro t f hf
    induction t using Finset.induction with
    | empty => simp [hφ0]
    | insert i t hi ih =>
      have ih' := ih fun j hj ↦ hf j (mem_insert_of_mem hj)
      have hfi := hf i (mem_insert_self i t)
      rw [sum_insert hi, sum_insert hi, (hφ2 _ hfi _ ih'.1).1, ih'.2]
      exact ⟨add_mem hfi ih'.1, rfl⟩
  have hnat : ∀ (N : ℕ), ∀ d ∈ D, (N : MvPolynomial (Fin 2) ℚ) * d ∈ D ∧ φ ((N : MvPolynomial (Fin 2) ℚ) * d) = N * φ d := by
    intro N d hd
    have e1 : (N : MvPolynomial (Fin 2) ℚ) * d = (N : ℤ) • d := by rw [zsmul_eq_mul, Int.cast_natCast]
    refine ⟨by rw [e1]; exact Submodule.smul_mem _ _ hd, ?_⟩
    rw [e1, hφz _ _ hd, zsmul_eq_mul, Int.cast_natCast]
  have hsX : ∀ N : ℕ, Γ.dpow N (X 0 + X 1) ∈ D ∧ φ (Γ.dpow N (X 0 + X 1)) = γ N (x + y) := by
    intro N
    have e1 : Γ.dpow N (X 0 + X 1) = ∑ p ∈ antidiagonal N, dpBas2 p := by
      rw [Γ.dpow_add (top _) (top _)]
      exact sum_congr rfl fun p _ ↦ (hbasΓ p).symm
    rw [e1, (hsum _ _ fun p _ ↦ hDb p).2, h.add N x hx y hy]
    exact ⟨(hsum _ _ fun p _ ↦ hDb p).1, sum_congr rfl fun p _ ↦ hφb p.1 p.2⟩
  set Dp := Submodule.span ℤ (dpBas2 '' {p | p ≠ 0}) with hDp
  have T : ∀ d ∈ Dp, d ∈ D ∧ φ d ∈ J ∧ ∀ k, Γ.dpow k d ∈ D ∧ γ k (φ d) = φ (Γ.dpow k d) := by
    intro d hd
    induction hd using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨⟨a, c⟩, hac, rfl⟩ := hd
      refine ⟨hDb _, ?_, fun k ↦ ?_⟩
      · rw [hφb]
        by_cases ha : a = 0
        · have hc : c ≠ 0 := by rintro rfl; exact hac (by simp [ha])
          exact J.mul_mem_left _ (h.mem c hc y hy)
        · exact J.mul_mem_right _ (h.mem a ha x hx)
      show Γ.dpow k (dpBas2 (a, c)) ∈ D ∧ γ k (φ (dpBas2 (a, c))) = φ (Γ.dpow k (dpBas2 (a, c)))
      rw [hφb a c]
      by_cases ha : a = 0
      · subst ha
        have hc : c ≠ 0 := by rintro rfl; exact hac rfl
        have e : Γ.dpow k (dpBas2 (0, c)) = ((k.uniformBell c : ℕ) : MvPolynomial (Fin 2) ℚ) * dpBas2 (0, k * c) := by
          rw [← hX1 c, Γ.dpow_comp hc (top _), hX1 (k * c)]
        obtain ⟨h1, h2⟩ := hnat (k.uniformBell c) _ (hDb (0, k * c))
        rw [e]
        refine ⟨h1, ?_⟩
        rw [h2, hφb, h.zero x hx, one_mul, one_mul, Py k c hc]
      · have e : Γ.dpow k (dpBas2 (a, c)) =
            ((k.uniformBell a : ℕ) : MvPolynomial (Fin 2) ℚ) * dpBas2 (k * a, 0) * dpBas2 (0, c) ^ k := by
          rw [hbasΓ' a c, Γ.dpow_mul_right (top _), Γ.dpow_comp ha (top _), hX0 (k * a), hX1 c]
        obtain ⟨h1, h2⟩ := hnat (k.uniformBell a) _ (hDb (k * a, 0))
        obtain ⟨h3, h4⟩ := hpow _ (hDb (0, c)) k
        obtain ⟨_, h5, h6⟩ := hφ2 _ h1 _ h3
        rw [e]
        refine ⟨h5, ?_⟩
        rw [h6, h2, h4, hφb, hφb, h.zero x hx, h.zero y hy, mul_comm (γ a x), h.mul k _ _ (h.mem a ha x hx),
          Px k a ha]
        ring
    | zero =>
      refine ⟨D.zero_mem, hφ0 ▸ J.zero_mem, fun k ↦ ?_⟩
      by_cases hk : k = 0
      · subst hk
        rw [Γ.dpow_zero (top _), hφ0, h.zero 0 J.zero_mem, hφ1]
        exact ⟨hD1, rfl⟩
      · rw [Γ.dpow_eval_zero hk, hφ0, preDP_eval_zero h hk]
        exact ⟨D.zero_mem, rfl⟩
    | add d e _ _ hd he =>
      obtain ⟨dD, dJ, dk⟩ := hd
      obtain ⟨eD, eJ, ek⟩ := he
      obtain ⟨hde, -, -⟩ := hφ2 d dD e eD
      refine ⟨add_mem dD eD, hde ▸ add_mem dJ eJ, fun k ↦ ?_⟩
      have hm : ∀ p ∈ antidiagonal k, Γ.dpow p.1 d * Γ.dpow p.2 e ∈ D := fun p _ ↦
        (hφ2 _ (dk p.1).1 _ (ek p.2).1).2.1
      rw [Γ.dpow_add (top _) (top _), hde, h.add k _ dJ _ eJ, (hsum _ _ hm).2]
      refine ⟨(hsum _ _ hm).1, sum_congr rfl fun p _ ↦ ?_⟩
      rw [(dk p.1).2, (ek p.2).2, (hφ2 _ (dk p.1).1 _ (ek p.2).1).2.2]
    | smul z d _ hd =>
      obtain ⟨dD, dJ, dk⟩ := hd
      refine ⟨Submodule.smul_mem _ _ dD, (hφz z d dD) ▸ zsmul_mem dJ z, fun k ↦ ?_⟩
      have e1 : Γ.dpow k (z • d) = (z ^ k) • Γ.dpow k d := by
        rw [zsmul_eq_mul, Γ.dpow_mul (top _), zsmul_eq_mul, Int.cast_pow]
      refine ⟨by rw [e1]; exact Submodule.smul_mem _ _ (dk k).1, ?_⟩
      rw [e1, hφz _ _ dD, hφz _ _ (dk k).1, zsmul_eq_mul, h.mul k _ _ dJ, (dk k).2, zsmul_eq_mul, Int.cast_pow]
  have hmem : Γ.dpow n (X 0 + X 1) ∈ Dp := by
    rw [Γ.dpow_add (top _) (top _)]
    refine Submodule.sum_mem _ fun p hp ↦ ?_
    rw [← hbasΓ]
    refine Submodule.subset_span ⟨p, fun h0 ↦ hn ?_, rfl⟩
    rw [HasAntidiagonal.mem_antidiagonal] at hp
    rw [← hp, h0]; rfl
  obtain ⟨_, _, hk⟩ := T _ hmem
  rw [← (hsX n).2, (hk m).2, Γ.dpow_comp hn (top _), (hnat _ _ (hsX _).1).2, (hsX _).2]

theorem exists_dp_of_comp_on_gens :
    ∀ (B : Type) [CommRing B] (J : Ideal B) (γ : ℕ → B → B) (s : Set B), IsPreDP J γ → J = Ideal.span s →
      (∀ x ∈ s, ∀ m n : ℕ, n ≠ 0 → γ m (γ n x) = (m.uniformBell n : B) * γ (m * n) x) →
      ∃ δ : DividedPowers J, δ.dpow = γ := by
  intro B _ J γ s h hJ hs
  have key : ∀ x ∈ J, ∀ m n : ℕ, n ≠ 0 → γ m (γ n x) = (m.uniformBell n : B) * γ (m * n) x := by
    intro x hx
    subst hJ
    induction hx using Submodule.span_induction with
    | mem x hxs => exact hs x hxs
    | zero =>
      intro m n hn
      rw [preDP_eval_zero h hn]
      by_cases hm : m = 0
      · subst hm
        rw [Nat.uniformBell_zero_left, zero_mul, h.zero 0 (Submodule.zero_mem _), Nat.cast_one, one_mul]
      · rw [preDP_eval_zero h hm, preDP_eval_zero h (mul_ne_zero hm hn), mul_zero]
    | add x y hx hy Px Py => exact fun m n hn ↦ preDP_comp_add h hx hy Px Py m n hn
    | smul a x hx Px =>
      intro m n hn
      rw [smul_eq_mul, h.mul n a x hx, h.mul m _ _ (h.mem n hn x hx), Px m n hn, h.mul (m * n) a x hx, ← pow_mul,
        mul_comm n m]
      ring
  exact ⟨{ dpow := γ
           dpow_null := fun hx ↦ h.null _ _ hx
           dpow_zero := fun hx ↦ h.zero _ hx
           dpow_one := fun hx ↦ h.one _ hx
           dpow_mem := fun hn hx ↦ h.mem _ hn _ hx
           dpow_add := fun hx hy ↦ h.add _ _ hx _ hy
           dpow_mul := fun hx ↦ h.mul _ _ _ hx
           mul_dpow := fun hx ↦ h.mul_dpow _ _ _ hx
           dpow_comp := fun hn hx ↦ key _ hx _ _ hn }, rfl⟩

end Comp

section Flat

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {I : Ideal R} (κ : DividedPowers I)

def expS (z : R) (y : A) : PowerSeries A :=
  PowerSeries.mk fun n ↦ y ^ n * algebraMap R A (κ.dpow n z)

theorem expS_add_right {z : R} (hz : z ∈ I) (y y' : A) :
    expS κ z (y + y') = expS κ z y * expS κ z y' := by
  ext n
  simp only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_mul]
  have h : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n, y ^ p.1 * algebraMap R A (κ.dpow p.1 z) *
      (y' ^ p.2 * algebraMap R A (κ.dpow p.2 z)) =
      y ^ p.1 * y' ^ p.2 * (n.choose p.1 : A) * algebraMap R A (κ.dpow n z) := by
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have h := κ.mul_dpow (m := p.1) (n := p.2) hz
    rw [hp] at h
    calc _ = y ^ p.1 * y' ^ p.2 * algebraMap R A (κ.dpow p.1 z * κ.dpow p.2 z) := by
            rw [map_mul]; ring
      _ = _ := by rw [h, map_mul, map_natCast]; ring
  rw [Finset.sum_congr rfl h, ← Finset.sum_mul, add_pow, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

theorem expS_add_left {z z' : R} (hz : z ∈ I) (hz' : z' ∈ I) (y : A) :
    expS κ (z + z') y = expS κ z y * expS κ z' y := by
  ext n
  simp only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_mul, κ.dpow_add hz hz', map_sum, map_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp, pow_add]; ring

theorem expS_smul {z : R} (hz : z ∈ I) (a : R) (y : A) :
    expS κ z (algebraMap R A a * y) = expS κ (a * z) y := by
  ext n
  simp only [expS, PowerSeries.coeff_mk, κ.dpow_mul hz, map_mul, map_pow]
  ring

theorem expS_zero_left (y : A) : expS κ 0 y = 1 := by
  ext n
  simp only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [κ.dpow_zero I.zero_mem]
  · simp [κ.dpow_eval_zero hn, hn]

theorem expS_zero_right (z : R) (hz : z ∈ I) : expS κ z (0 : A) = 1 := by
  ext n
  simp only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [κ.dpow_zero hz]
  · simp [hn]

theorem expS_sum_right {z : R} (hz : z ∈ I) {K : Type} (s : Finset K) (f : K → A) :
    expS κ z (∑ k ∈ s, f k) = ∏ k ∈ s, expS κ z (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expS_zero_right κ z hz]
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.prod_insert hk, expS_add_right κ hz, ih]

theorem expS_sum_left {K : Type} (s : Finset K) (f : K → R) (hf : ∀ k ∈ s, f k ∈ I) (y : A) :
    expS κ (∑ k ∈ s, f k) y = ∏ k ∈ s, expS κ (f k) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expS_zero_left κ y]
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.prod_insert hk,
      expS_add_left κ (hf k (Finset.mem_insert_self k s))
        (Ideal.sum_mem _ fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)),
      ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)]

theorem prod_expS_eq_one [Module.Flat R A] (c : I →₀ A)
    (hc : (c.sum fun i a ↦ a * algebraMap R A i) = 0) :
    (c.prod fun i a ↦ PowerSeries.mk fun n ↦ a ^ n * algebraMap R A (κ.dpow n i)) = 1 := by
  have h : ∑ i : ↥c.support, ((i : I) : R) • (c (i : I) : A) = (0 : A) := by
    rw [Finset.sum_coe_sort c.support (fun i : I ↦ ((i : R)) • (c i : A)), ← hc, Finsupp.sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Algebra.smul_def, mul_comm]
  obtain ⟨k, a, y, hx, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := A) h
  simp only at hx ha
  change (∏ i ∈ c.support, expS κ (i : R) (c i)) = 1
  rw [← Finset.prod_coe_sort]
  calc ∏ i : c.support, expS κ ((i.1 : I) : R) (c i.1)
      = ∏ i : c.support, ∏ j, expS κ (a i j * ((i.1 : I) : R)) (y j) := by
        refine Finset.prod_congr rfl fun i _ ↦ ?_
        rw [hx i, expS_sum_right κ (i.1 : I).2]
        refine Finset.prod_congr rfl fun j _ ↦ ?_
        rw [Algebra.smul_def, expS_smul κ (i.1 : I).2]
    _ = ∏ j, ∏ i : c.support, expS κ (a i j * ((i.1 : I) : R)) (y j) := Finset.prod_comm
    _ = ∏ j, expS κ (∑ i : c.support, a i j * ((i.1 : I) : R)) (y j) := by
        refine Finset.prod_congr rfl fun j _ ↦ ?_
        rw [expS_sum_left κ _ _ fun i _ ↦ I.mul_mem_left _ (i.1 : I).2]
    _ = 1 := by
        refine Finset.prod_eq_one fun j _ ↦ ?_
        have : ∑ i : c.support, a i j * ((i.1 : I) : R) = 0 := by
          rw [← ha j]; exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
        rw [this, expS_zero_left]

theorem dpFlat : DPFlat := by
  intro R A _ _ _ _ I κ
  let x : I → A := fun i ↦ algebraMap R A i
  have hspan : Ideal.span (Set.range x) = I.map (algebraMap R A) := by
    rw [Ideal.map]; congr 1; ext b; simp [x]
  obtain ⟨γ, hγ, hγx⟩ := GlobalTheory.PDA.exists_isPreDividedPowers_of_generators₂ A I x (fun i n ↦ algebraMap R A (κ.dpow n i))
    (fun i ↦ by simp [κ.dpow_zero i.2]) (fun i ↦ by simp [x, κ.dpow_one i.2])
    (fun i n hn ↦ Ideal.subset_span ⟨⟨κ.dpow n i, κ.dpow_mem hn i.2⟩, rfl⟩)
    (fun i m n ↦ by rw [← map_mul, κ.mul_dpow i.2, map_mul, map_natCast])
    (prod_expS_eq_one κ)
  rw [hspan] at hγ
  obtain ⟨δ, hδ⟩ := exists_dp_of_comp_on_gens A _ γ (Set.range x) hγ hspan.symm (by
    rintro _ ⟨i, rfl⟩ m n hn
    rw [hγx, show algebraMap R A (κ.dpow n i) = x ⟨κ.dpow n i, κ.dpow_mem hn i.2⟩ from rfl, hγx]
    simp only [κ.dpow_comp hn i.2, map_mul, map_natCast]
    rw [← hγx])
  exact ⟨δ, ⟨le_rfl, fun a ha ↦ by rw [hδ]; exact hγx ⟨a, ha⟩ _⟩⟩

end Flat

end GlobalTheory.CompanionTheory.JLiftDP
