import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.SiegelDecay

theorem ratio_le_of_le {n : ℕ} {t : ℝ} (ht : 0 < t) {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i)
    (hs : ∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) (i j : Fin n) (hij : i ≤ j) :
    ρ j / ρ i ≤ max 1 t⁻¹ ^ n := by
  set S := max 1 t⁻¹
  have hS1 : 1 ≤ S := le_max_left _ _
  have hstep : ∀ l : ℕ, ∀ (hl : l + 1 < n), ρ ⟨l + 1, hl⟩ ≤ S * ρ ⟨l, by omega⟩ := by
    intro l hl
    have h := hs ⟨l, by omega⟩ ⟨l + 1, hl⟩ rfl
    have h2 : ρ ⟨l + 1, hl⟩ ≤ t⁻¹ * ρ ⟨l, by omega⟩ := by
      rw [inv_mul_eq_div, le_div_iff₀ ht]; linarith
    exact h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (hρ _).le)
  have hchain : ∀ d : ℕ, ∀ (a : ℕ) (ha : a + d < n),
      ρ ⟨a + d, ha⟩ ≤ S ^ d * ρ ⟨a, by omega⟩ := by
    intro d
    induction d with
    | zero => intro a ha; simp
    | succ d ih =>
      intro a ha
      calc ρ ⟨a + (d + 1), ha⟩ ≤ S * ρ ⟨a + d, by omega⟩ := hstep (a + d) ha
        _ ≤ S * (S ^ d * ρ ⟨a, by omega⟩) :=
            mul_le_mul_of_nonneg_left (ih a (by omega)) (by linarith)
        _ = S ^ (d + 1) * ρ ⟨a, by omega⟩ := by ring
  have hij' : (i : ℕ) ≤ j := hij
  have h1 := hchain (j - i) i (by omega)
  have hj : (⟨(i : ℕ) + (j - i), by omega⟩ : Fin n) = j := Fin.ext (by simp; omega)
  rw [hj] at h1
  rw [div_le_iff₀ (hρ _)]
  calc ρ j ≤ S ^ ((j : ℕ) - i) * ρ i := h1
    _ ≤ S ^ n * ρ i :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hS1 (by omega)) (hρ _).le

theorem ratio_le_all {n : ℕ} {t : ℝ} (ht : 0 < t) {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i)
    (hs : ∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) {A : ℝ} (hA1 : 1 ≤ A)
    (hA : ∀ i j : Fin n, i < j → ρ i / ρ j ≤ A ^ n) (i j : Fin n) :
    ρ i / ρ j ≤ max 1 t⁻¹ ^ n * A ^ n := by
  have hT : 1 ≤ max 1 t⁻¹ ^ n := one_le_pow₀ (le_max_left _ _)
  have hAn : 1 ≤ A ^ n := one_le_pow₀ hA1
  rcases lt_or_ge i j with h | h
  · exact (hA i j h).trans (le_mul_of_one_le_left (by linarith) hT)
  · exact (ratio_le_of_le ht hρ hs j i h).trans (le_mul_of_one_le_right (by linarith) hAn)

theorem le_of_ratio_le {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) (hprod : ∏ i, ρ i = 1)
    {R : ℝ} (hR : 1 ≤ R) (h : ∀ i j, ρ i / ρ j ≤ R) (i : Fin n) : ρ i ≤ R := by
  have hn : n ≠ 0 := by
    rintro rfl
    exact i.elim0
  have h1 : ρ i ^ n = ∏ j, ρ i / ρ j := by
    rw [Finset.prod_div_distrib, hprod, div_one]
    simp
  have h2 : ρ i ^ n ≤ R ^ n := by
    rw [h1]
    calc ∏ j, ρ i / ρ j ≤ ∏ _j : Fin n, R :=
          Finset.prod_le_prod (fun j _ => (div_pos (hρ i) (hρ j)).le) (fun j _ => h i j)
      _ = R ^ n := by simp
  exact (pow_le_pow_iff_left₀ (hρ i).le (by linarith) hn).1 h2

theorem inv_le_of_ratio_le {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) (hprod : ∏ i, ρ i = 1)
    {R : ℝ} (hR : 1 ≤ R) (h : ∀ i j, ρ i / ρ j ≤ R) (i : Fin n) : R⁻¹ ≤ ρ i := by
  have h1 : (ρ i)⁻¹ ≤ R := by
    refine le_of_ratio_le (ρ := fun i => (ρ i)⁻¹) (fun i => inv_pos.2 (hρ i)) ?_ hR ?_ i
    · rw [Finset.prod_inv_distrib, hprod, inv_one]
    · intro i j
      have := h j i
      rwa [inv_div_inv]
  exact inv_le_of_inv_le₀ (hρ i) h1

theorem one_le_rpow_mul_prod {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) {R : ℝ} (hR : 1 ≤ R)
    (hb : ∀ i, ρ i ≤ R) (hb' : ∀ i, R⁻¹ ≤ ρ i) (lam : Fin n → ℝ) :
    1 ≤ R ^ (∑ i, |lam i|) * ∏ i, ρ i ^ lam i := by
  have hR0 : 0 < R := by linarith
  rw [Real.rpow_sum_of_pos hR0, ← Finset.prod_mul_distrib]
  calc (1 : ℝ) = ∏ _i : Fin n, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun i _ => ?_)
  rcases le_total 0 (lam i) with hl | hl
  · rw [abs_of_nonneg hl, ← Real.mul_rpow hR0.le (hρ i).le]
    refine Real.one_le_rpow ?_ hl
    have := mul_le_mul_of_nonneg_left (hb' i) hR0.le
    rwa [mul_inv_cancel₀ hR0.ne'] at this
  · have hρ' : ρ i ^ lam i = ((ρ i)⁻¹) ^ (-lam i) := by
      rw [Real.inv_rpow (hρ i).le, Real.rpow_neg (hρ i).le, inv_inv]
    rw [abs_of_nonpos hl, hρ', ← Real.mul_rpow hR0.le (inv_pos.2 (hρ i)).le]
    refine Real.one_le_rpow ?_ (by linarith)
    rw [← div_eq_mul_inv, one_le_div (hρ i)]
    exact hb i

theorem one_le_weight {n : ℕ} {t : ℝ} (ht : 0 < t) {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i)
    (hs : ∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) (hprod : ∏ i, ρ i = 1)
    {A : ℝ} (hA1 : 1 ≤ A) (hA : ∀ i j : Fin n, i < j → ρ i / ρ j ≤ A ^ n)
    (lam : Fin n → ℝ) (M : ℕ) (hM : (n : ℝ) * ∑ i, |lam i| ≤ M) :
    1 ≤ (max 1 t⁻¹ ^ n) ^ (∑ i, |lam i|) * A ^ M * ∏ i, ρ i ^ lam i := by
  have hT : 1 ≤ max 1 t⁻¹ ^ n := one_le_pow₀ (le_max_left _ _)
  have hAn : 1 ≤ A ^ n := one_le_pow₀ hA1
  have hA0 : 0 < A := by linarith
  have hR : 1 ≤ max 1 t⁻¹ ^ n * A ^ n := one_le_mul_of_one_le_of_one_le hT hAn
  have hrat := ratio_le_all ht hρ hs hA1 hA
  have h := one_le_rpow_mul_prod hρ hR (le_of_ratio_le hρ hprod hR hrat)
    (inv_le_of_ratio_le hρ hprod hR hrat) lam
  have hP : 0 ≤ ∏ i, ρ i ^ lam i :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hρ i).le _
  have hpow : (A ^ n) ^ (∑ i, |lam i|) ≤ A ^ M := by
    rw [← Real.rpow_natCast A n, ← Real.rpow_mul hA0.le, ← Real.rpow_natCast A M]
    exact Real.rpow_le_rpow_of_exponent_le hA1 hM
  rw [Real.mul_rpow (by linarith) (by linarith)] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hP)
  exact mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (by linarith) _)

theorem rapid_decay_of_one_parabolic_bounds : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (φ : AdelicGLn.AdelicGL K n → ℂ), Continuous φ → (∀ ω : Set (AdelicGLn.AdelicGL K n), IsCompact ω → ω ⊆ (adelicBorel (K := K) (n := n) : Set (AdelicGLn.AdelicGL K n)) →
    (∀ b ∈ ω, (IdeleGroup.ideleModule K (Matrix.GeneralLinearGroup.det b) : ℝ) = 1) → ∀ t : ℝ, 0 < t → ∀ (r : ℕ) (hr0 : 0 < r) (hrn : r < n), ∃ N : ℕ, ∀ k : ℕ, ∃ C : ℝ,
      ∀ b ∈ ω, ∀ (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i), (∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) →
        ∏ i, ρ i = 1 → ∀ kk ∈ maxCompact (K := K) (n := n), ∀ R : ℝ, 1 ≤ R → (∀ i j : Fin n, ρ i / ρ j ≤ R) →
          ‖φ (b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) * kk)‖ ≤
            C * (ρ ⟨r, hrn⟩ / ρ ⟨r - 1, lt_of_le_of_lt (Nat.sub_le r 1) hrn⟩) ^ k * R ^ N) → (∀ ω : Set (AdelicGLn.AdelicGL K n), IsCompact ω → ω ⊆ (adelicBorel (K := K) (n := n) : Set (AdelicGLn.AdelicGL K n)) →
    (∀ b ∈ ω, (IdeleGroup.ideleModule K (Matrix.GeneralLinearGroup.det b) : ℝ) = 1) → ∀ t : ℝ, 0 < t → ∀ lam : Fin n → ℝ, ∃ C : ℝ,
      ∀ b ∈ ω, ∀ (r : Fin n → ℝ) (hr : ∀ i, 0 < r i), (∀ i j : Fin n, (j : ℕ) = i + 1 → t * r j ≤ r i) →
        ∏ i, r i = 1 → ∀ k ∈ maxCompact (K := K) (n := n),
          ‖φ (b * diagUnits n (fun i => posIdele (K := K) (r i) (hr i)) * k)‖ ≤ C * ∏ i, r i ^ lam i) := by
  intro K _ _ n φ hφ hyp ω hω hωB hdet t ht lam
  rcases Nat.lt_or_ge n 2 with hn | hn
  · obtain ⟨C, hC⟩ := (hω.mul (isCompact_maxCompact (K := K) (n := n))).exists_bound_of_continuousOn
      hφ.continuousOn
    refine ⟨C, fun b hb r hr hs hprod k hk => ?_⟩
    have hr1 : ∀ i, r i = 1 := by
      intro i
      have h1 : n = 1 := by
        have := i.pos
        omega
      subst h1
      have hi : i = 0 := Subsingleton.elim _ _
      simpa [hi] using hprod
    have hd : diagUnits n (fun i => posIdele (K := K) (r i) (hr i)) = 1 := by
      have h1 : (fun i => posIdele (K := K) (r i) (hr i)) = 1 := by
        funext i
        have h2 : (⟨r i, hr i⟩ : {x : ℝ // 0 < x}) = 1 := Subtype.ext (hr1 i)
        change posIdeleHom K ⟨r i, hr i⟩ = 1
        rw [h2, map_one]
      rw [h1, map_one]
    have hP : ∏ i, r i ^ lam i = 1 :=
      Finset.prod_eq_one fun i _ => by rw [hr1 i, Real.one_rpow]
    rw [hd, hP, mul_one, mul_one]
    exact hC _ (Set.mul_mem_mul hb hk)
  · set T : ℝ := max 1 t⁻¹ ^ n with hTdef
    have hT1 : 1 ≤ T := one_le_pow₀ (le_max_left _ _)
    have hT0 : 0 < T := by linarith
    set L : ℝ := ∑ i, |lam i| with hL
    obtain ⟨M, hM⟩ := exists_nat_ge ((n : ℝ) * L)
    have key : ∀ (r : ℕ) (hr : 0 < r) (hrn : r < n), ∃ D : ℝ, ∀ b ∈ ω, ∀ (ρ : Fin n → ℝ)
        (hρ : ∀ i, 0 < ρ i), (∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) → ∏ i, ρ i = 1 →
        ∀ kk ∈ maxCompact (K := K) (n := n),
        (∀ i j : Fin n, i < j → ρ i / ρ j ≤ max 1 (ρ ⟨r - 1, by omega⟩ / ρ ⟨r, hrn⟩) ^ n) →
        ‖φ (b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) * kk)‖ ≤
          max D 0 * ∏ i, ρ i ^ lam i := by
      intro r hr hrn
      obtain ⟨N, hN⟩ := hyp ω hω hωB hdet t ht r hr hrn
      obtain ⟨C0, hC0⟩ := hN 0
      obtain ⟨C1, hC1⟩ := hN (n * N + M)
      set E : ℝ := max C0 0 + max C1 0 with hE
      have hE0 : 0 ≤ E := add_nonneg (le_max_right _ _) (le_max_right _ _)
      have hC0E : C0 ≤ E := (le_max_left _ _).trans (le_add_of_nonneg_right (le_max_right _ _))
      have hC1E : C1 ≤ E := (le_max_left _ _).trans (le_add_of_nonneg_left (le_max_right _ _))
      have hTL : 0 < T ^ L := Real.rpow_pos_of_pos hT0 _
      have hD0 : 0 ≤ E * T ^ N * T ^ L := by positivity
      refine ⟨E * T ^ N * T ^ L, ?_⟩
      rw [max_eq_left hD0]
      intro b hb ρ hρ hs hprod kk hkk hmax
      have hgain : ρ ⟨r, hrn⟩ / ρ ⟨r - 1, lt_of_le_of_lt (Nat.sub_le r 1) hrn⟩ =
          (ρ ⟨r - 1, by omega⟩ / ρ ⟨r, hrn⟩)⁻¹ := by rw [inv_div]
      obtain ⟨α, hα⟩ : ∃ α, α = ρ ⟨r - 1, by omega⟩ / ρ ⟨r, hrn⟩ := ⟨_, rfl⟩
      rw [← hα] at hmax hgain
      have hα0 : 0 < α := by rw [hα]; exact div_pos (hρ _) (hρ _)
      set P : ℝ := ∏ i, ρ i ^ lam i with hPdef
      have hP : 0 ≤ P := Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hρ i).le _
      rcases le_or_gt α 1 with hα1 | hα1
      · rw [max_eq_left hα1] at hmax
        have hone := one_le_weight ht hρ hs hprod le_rfl hmax lam M hM
        rw [one_pow, mul_one] at hone
        have h := hC0 b hb ρ hρ hs hprod kk hkk T hT1 fun i j => by
          simpa using ratio_le_all ht hρ hs le_rfl hmax i j
        rw [pow_zero, mul_one] at h
        calc _ ≤ C0 * T ^ N := h
          _ ≤ E * T ^ N := mul_le_mul_of_nonneg_right hC0E (by positivity)
          _ ≤ E * T ^ N * (T ^ L * P) := le_mul_of_one_le_right (by positivity) hone
          _ = E * T ^ N * T ^ L * P := by ring
      · rw [max_eq_right hα1.le] at hmax
        have hone := one_le_weight ht hρ hs hprod hα1.le hmax lam M hM
        have hαn : 1 ≤ α ^ n := one_le_pow₀ hα1.le
        have h := hC1 b hb ρ hρ hs hprod kk hkk (T * α ^ n)
          (one_le_mul_of_one_le_of_one_le hT1 hαn) (ratio_le_all ht hρ hs hα1.le hmax)
        rw [hgain] at h
        have hpow : (α⁻¹) ^ (n * N + M) * (T * α ^ n) ^ N = T ^ N * (α ^ M)⁻¹ := by
          have ha : α ^ (n * N) ≠ 0 := (pow_pos hα0 _).ne'
          rw [mul_pow, ← pow_mul α n N, inv_pow, pow_add, mul_inv]
          calc (α ^ (n * N))⁻¹ * (α ^ M)⁻¹ * (T ^ N * α ^ (n * N))
              = ((α ^ (n * N))⁻¹ * α ^ (n * N)) * (T ^ N * (α ^ M)⁻¹) := by ring
            _ = T ^ N * (α ^ M)⁻¹ := by rw [inv_mul_cancel₀ ha, one_mul]
        have hX : 0 ≤ T ^ N * (α ^ M)⁻¹ := by positivity
        calc _ ≤ C1 * (α⁻¹) ^ (n * N + M) * (T * α ^ n) ^ N := h
          _ = C1 * (T ^ N * (α ^ M)⁻¹) := by rw [mul_assoc, hpow]
          _ ≤ E * (T ^ N * (α ^ M)⁻¹) := mul_le_mul_of_nonneg_right hC1E hX
          _ ≤ E * (T ^ N * (α ^ M)⁻¹) * (T ^ L * α ^ M * P) :=
              le_mul_of_one_le_right (mul_nonneg hE0 hX) hone
          _ = E * T ^ N * T ^ L * P := by
              have : α ^ M ≠ 0 := (pow_pos hα0 _).ne'
              field_simp
    choose D hD using key
    refine ⟨∑ r : Fin n, if h : 0 < (r : ℕ) then max (D r h r.2) 0 else 0, ?_⟩
    intro b hb ρ hρ hs hprod k hk
    obtain ⟨r, hr, hrn, hratio⟩ := GroundTheory.Automorphic.CuspidalSpectrum.exists_le_max_pow hn ρ hρ
    have hP : 0 ≤ ∏ i, ρ i ^ lam i :=
      Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hρ i).le _
    refine (hD r hr hrn b hb ρ hρ hs hprod k hk hratio).trans
      (mul_le_mul_of_nonneg_right ?_ hP)
    have h1 := Finset.single_le_sum (f := fun r : Fin n =>
      if h : 0 < (r : ℕ) then max (D r h r.2) 0 else 0)
      (fun r _ => by split_ifs <;> simp) (Finset.mem_univ ⟨r, hrn⟩)
    simpa only [hr, dif_pos] using h1

end GlobalTheory.CompanionTheory.SiegelDecay
