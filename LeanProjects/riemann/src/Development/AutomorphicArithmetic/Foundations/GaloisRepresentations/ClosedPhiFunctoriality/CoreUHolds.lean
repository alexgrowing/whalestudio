import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusSectionAcrisBreuilKisin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

open GlobalTheory.CrisSec Matrix

private theorem matrix_map_smul' {R : Type} [CommRing R] {d : ℕ} (φ : R →+* R) (c : R)
    (X : Matrix (Fin d) (Fin d) R) : (c • X).map φ = φ c • X.map φ := by
  ext i j
  simp [Matrix.map_apply]

private theorem eq_zero_of_pow_mul_eq_zero_of_nonzerodivisor {R : Type} [CommRing R] (L : R) (hL : ∀ x : R, L * x = 0 → x = 0) :
    ∀ (m : ℕ) (x : R), L ^ m * x = 0 → x = 0 := by
  intro m
  induction m with
  | zero => intro x hx; simpa using hx
  | succ k ih =>
    intro x hx
    apply ih
    apply hL
    rw [pow_succ] at hx
    linear_combination hx

private theorem matrix_eq_of_smul_eq_nonzerodivisor {R : Type} [CommRing R] {d : ℕ} (s : R) (hs : ∀ x : R, s * x = 0 → x = 0)
    (X Y : Matrix (Fin d) (Fin d) R) (h : s • X = s • Y) : X = Y := by
  ext i j
  have h1 : s * X i j = s * Y i j := by
    have := congrArg (fun M : Matrix (Fin d) (Fin d) R => M i j) h
    simpa [Matrix.smul_apply] using this
  exact sub_eq_zero.mp (hs _ (by rw [mul_sub, h1, sub_self]))

private theorem lau_mem_iff_vecL_mem {R : Type} [CommRing R] (L x : R) (m : ℕ) :
    x ∈ (Ideal.span {L}) ^ m • (⊤ : Submodule R R) ↔ L ^ m ∣ x := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

private theorem matrix_eq_zero_of_adic_divisible {R : Type} [CommRing R] {d : ℕ} (L : R) (hc : IsAdicComplete (Ideal.span {L}) R)
    (X : Matrix (Fin d) (Fin d) R) (h : ∀ m : ℕ, ∃ Z : Matrix (Fin d) (Fin d) R, X = L ^ m • Z) : X = 0 := by
  ext i j
  show X i j = 0
  apply hc.toIsHausdorff.haus
  intro m
  rw [SModEq.sub_mem, sub_zero, lau_mem_iff_vecL_mem]
  obtain ⟨Z, hZ⟩ := h m
  exact ⟨Z i j, by rw [hZ]; simp [Matrix.smul_apply]⟩

private theorem exists_matrix_limit_adic_series {R : Type} [CommRing R] {d : ℕ} (L : R) (hc : IsAdicComplete (Ideal.span {L}) R)
    (y : ℕ → Matrix (Fin d) (Fin d) R) :
    ∃ T : Matrix (Fin d) (Fin d) R, ∀ m : ℕ, ∃ Z : Matrix (Fin d) (Fin d) R,
      T - ∑ k ∈ Finset.range m, L ^ k • y k = L ^ m • Z := by
  have key : ∀ i j, ∃ t : R, ∀ m : ℕ, L ^ m ∣ t - ∑ k ∈ Finset.range m, L ^ k * y k i j := by
    intro i j
    obtain ⟨t, ht⟩ := hc.toIsPrecomplete.prec (f := fun m => ∑ k ∈ Finset.range m, L ^ k * y k i j)
      (by
        intro m n hmn
        rw [SModEq.sub_mem, lau_mem_iff_vecL_mem, ← Finset.sum_range_add_sum_Ico _ hmn, sub_add_cancel_left,
          dvd_neg]
        apply Finset.dvd_sum
        intro k hk
        exact (pow_dvd_pow L (Finset.mem_Ico.mp hk).1).mul_right _)
    refine ⟨t, fun m => ?_⟩
    have := ht m
    rw [SModEq.sub_mem, lau_mem_iff_vecL_mem] at this
    exact dvd_sub_comm.mp this
  choose t ht using key
  refine ⟨Matrix.of t, fun m => ?_⟩
  have hz : ∀ i j, ∃ z : R, t i j - ∑ k ∈ Finset.range m, L ^ k * y k i j = L ^ m * z :=
    fun i j => ht i j m
  choose z hz using hz
  refine ⟨Matrix.of z, ?_⟩
  ext i j
  simp only [Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  exact hz i j

private theorem matrix_mul_comm_of_mul_eq_smul_one {R : Type} [CommRing R] {d : ℕ} (c : R) (hc : ∀ x : R, c * x = 0 → x = 0)
    (X Y : Matrix (Fin d) (Fin d) R) (h : X * Y = c • 1) : Y * X = c • 1 := by
  have hdet : X.det * Y.det = c ^ d := by
    rw [← Matrix.det_mul, h, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hX : ∀ x : R, X.det * x = 0 → x = 0 := by
    intro x hx
    apply eq_zero_of_pow_mul_eq_zero_of_nonzerodivisor c hc d
    rw [← hdet, mul_comm X.det, mul_assoc, hx, mul_zero]
  apply matrix_eq_of_smul_eq_nonzerodivisor X.det hX
  calc X.det • (Y * X) = (X.adjugate * X) * Y * X := by
        rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.smul_mul, one_mul]
    _ = X.adjugate * (X * Y) * X := by simp only [Matrix.mul_assoc]
    _ = X.det • (c • (1 : Matrix (Fin d) (Fin d) R)) := by
        rw [h, Matrix.mul_smul, mul_one, Matrix.smul_mul, Matrix.adjugate_mul, smul_comm]

private theorem exists_matrix_seq_diff_congruence {R : Type} [CommRing R] {d N q : ℕ} (L u : R) (φ : R →+* R)
    (hφL : φ L = L) (hu : φ u = u ^ q) (a b b' Γ : Matrix (Fin d) (Fin d) R)
    (hbb : b * b' = L ^ (2 * N) • 1) (hab : L • (a - b) = u ^ q • Γ)
    (P : ℕ → Matrix (Fin d) (Fin d) R) (hP0 : P 0 = 1)
    (hPs : ∀ n, P (n + 1) = a * (P n).map φ * b') :
    ∀ n, ∃ M : Matrix (Fin d) (Fin d) R,
      L • (P (n + 1) - L ^ (2 * N) • P n) = u ^ (q ^ (n + 1)) • M := by
  intro n
  induction n with
  | zero =>
    refine ⟨Γ * b', ?_⟩
    rw [hPs, hP0, Matrix.map_one _ (map_zero φ) (map_one φ), mul_one, ← hbb, ← Matrix.sub_mul,
      ← Matrix.smul_mul, hab, Matrix.smul_mul]
    simp
  | succ k ih =>
    obtain ⟨M, hM⟩ := ih
    refine ⟨a * M.map φ * b', ?_⟩
    rw [show P (k + 1 + 1) - L ^ (2 * N) • P (k + 1)
        = a * (P (k + 1)).map φ * b' - L ^ (2 * N) • (a * (P k).map φ * b') by
          rw [← hPs k, ← hPs (k + 1)]]
    have e : L • (a * (P (k + 1)).map φ * b' - L ^ (2 * N) • (a * (P k).map φ * b'))
        = a * (L • (P (k + 1) - L ^ (2 * N) • P k)).map φ * b' := by
      rw [matrix_map_smul', Matrix.map_sub _ (fun x y => map_sub φ x y), matrix_map_smul', map_pow, hφL]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, smul_sub]
    rw [e, hM, matrix_map_smul', map_pow, hu, ← pow_mul, Matrix.mul_smul, Matrix.smul_mul]
    congr 2
    ring

private theorem exists_matrix_pow_sub_mod_u {R : Type} [CommRing R] {d N q : ℕ} (L u : R) (hq : 0 < q)
    (P : ℕ → Matrix (Fin d) (Fin d) R) (hP0 : P 0 = 1)
    (hD : ∀ n, ∃ M : Matrix (Fin d) (Fin d) R,
      L • (P (n + 1) - L ^ (2 * N) • P n) = u ^ (q ^ (n + 1)) • M) :
    ∀ n, ∃ Y : Matrix (Fin d) (Fin d) R, L ^ n • (P n - L ^ (2 * N * n) • 1) = u • Y := by
  intro n
  induction n with
  | zero => exact ⟨0, by simp [hP0]⟩
  | succ k ih =>
    obtain ⟨Y, hY⟩ := ih
    obtain ⟨M, hM⟩ := hD k
    have he : 1 ≤ q ^ (k + 1) := Nat.one_le_pow _ _ hq
    have hu' : u ^ (q ^ (k + 1)) = u * u ^ (q ^ (k + 1) - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    refine ⟨L ^ k • u ^ (q ^ (k + 1) - 1) • M + L ^ (2 * N + 1) • Y, ?_⟩
    have hsplit : P (k + 1) - L ^ (2 * N * (k + 1)) • 1
        = (P (k + 1) - L ^ (2 * N) • P k) + L ^ (2 * N) • (P k - L ^ (2 * N * k) • 1) := by
      rw [smul_sub, smul_smul, ← pow_add, show 2 * N + 2 * N * k = 2 * N * (k + 1) by ring]
      abel
    have h2 : L ^ (k + 1) • L ^ (2 * N) • (P k - L ^ (2 * N * k) • 1)
        = L ^ (2 * N + 1) • (L ^ k • (P k - L ^ (2 * N * k) • 1)) := by
      simp only [smul_smul]
      congr 1
      ring
    rw [hsplit, smul_add, h2, hY, pow_succ, mul_smul, hM, hu']
    simp only [smul_add, smul_smul]
    congr 1 <;> congr 1 <;> ring

private theorem matrix_seq_diff_divisible_of_le {R : Type} [CommRing R] {d N q n₀ : ℕ} (L u : R) (hq : 0 < q)
    (hL : ∀ x : R, L * x = 0 → x = 0)
    (hdiv : ∀ n, n₀ ≤ n → L ^ ((2 * N + 1) * (n + 1) + 1) ∣ u ^ (q ^ (n + 1) - 1))
    (P : ℕ → Matrix (Fin d) (Fin d) R)
    (hD : ∀ n, ∃ M : Matrix (Fin d) (Fin d) R,
      L • (P (n + 1) - L ^ (2 * N) • P n) = u ^ (q ^ (n + 1)) • M) :
    ∀ n, n₀ ≤ n → ∃ C : Matrix (Fin d) (Fin d) R,
      P (n + 1) - L ^ (2 * N) • P n = L ^ ((2 * N + 1) * (n + 1)) • u • C := by
  intro n hn
  obtain ⟨M, hM⟩ := hD n
  obtain ⟨w, hw⟩ := hdiv n hn
  have he : 1 ≤ q ^ (n + 1) := Nat.one_le_pow _ _ hq
  have hu' : u ^ (q ^ (n + 1)) = u * u ^ (q ^ (n + 1) - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  refine ⟨w • M, ?_⟩
  apply matrix_eq_of_smul_eq_nonzerodivisor L hL
  rw [hM, hu', hw]
  simp only [smul_smul]
  congr 1
  ring

private theorem exists_limit_matrix_seq_congruent {R : Type} [CommRing R] {d N n₀ : ℕ} (L u : R)
    (hc : IsAdicComplete (Ideal.span {L}) R)
    (P : ℕ → Matrix (Fin d) (Fin d) R)
    (hBig : ∀ n, n₀ ≤ n → ∃ C : Matrix (Fin d) (Fin d) R,
      P (n + 1) - L ^ (2 * N) • P n = L ^ ((2 * N + 1) * (n + 1)) • u • C)
    (hMod : ∀ n, ∃ Y : Matrix (Fin d) (Fin d) R, L ^ n • (P n - L ^ (2 * N * n) • 1) = u • Y) :
    ∃ (S : Matrix (Fin d) (Fin d) R) (Sq : ℕ → Matrix (Fin d) (Fin d) R),
      (∀ m, P (n₀ + m) = L ^ (2 * N * m) • Sq m) ∧
      (∀ m, ∃ Z : Matrix (Fin d) (Fin d) R, S - Sq m = L ^ m • Z) ∧
      ∃ Y : Matrix (Fin d) (Fin d) R, L ^ n₀ • (S - L ^ (2 * N * n₀) • 1) = u • Y := by
  have hC : ∀ m, ∃ C : Matrix (Fin d) (Fin d) R,
      P (n₀ + m + 1) - L ^ (2 * N) • P (n₀ + m) = L ^ ((2 * N + 1) * (n₀ + m + 1)) • u • C :=
    fun m => hBig (n₀ + m) (by omega)
  choose C hC using hC
  obtain ⟨T, hT⟩ := exists_matrix_limit_adic_series L hc (fun j => L ^ (n₀ + 2 * N * n₀ + 1) • C j)
  refine ⟨P n₀ + u • T,
    fun m => P n₀ + u • ∑ j ∈ Finset.range m, L ^ j • L ^ (n₀ + 2 * N * n₀ + 1) • C j, ?_, ?_, ?_⟩
  · intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hsplit : P (n₀ + (m + 1))
          = (P (n₀ + m + 1) - L ^ (2 * N) • P (n₀ + m)) + L ^ (2 * N) • P (n₀ + m) := by
        rw [sub_add_cancel]
        rfl
      beta_reduce at ih ⊢
      rw [hsplit, hC m, ih, Finset.sum_range_succ, smul_add u, ← add_assoc]
      generalize P n₀ + u • ∑ j ∈ Finset.range m, L ^ j • L ^ (n₀ + 2 * N * n₀ + 1) • C j = X
      simp only [smul_add, smul_smul]
      rw [add_comm]
      congr 1
      · congr 1
        ring
      · congr 1
        ring
  · intro m
    obtain ⟨Z, hZ⟩ := hT m
    refine ⟨u • Z, ?_⟩
    beta_reduce
    rw [add_sub_add_left_eq_sub, ← smul_sub, hZ, smul_comm]
  · obtain ⟨Y, hY⟩ := hMod n₀
    refine ⟨Y + L ^ n₀ • T, ?_⟩
    rw [add_sub_right_comm, smul_add, hY, smul_add, smul_comm]

theorem coreU_holds : CoreU := by
  intro R _ d l q N hl hc φ u hu hq α α' β β' Γ hαα hββ hΓ n₀ hdiv
  have hφL : φ (l : R) = l := map_natCast φ l
  have hβ'β : β' * β = (l : R) ^ (2 * N) • 1 :=
    matrix_mul_comm_of_mul_eq_smul_one _ (fun x hx => eq_zero_of_pow_mul_eq_zero_of_nonzerodivisor _ hl _ x hx) β β' hββ
  obtain ⟨P, hP0, hPs⟩ : ∃ P : ℕ → Matrix (Fin d) (Fin d) R,
      P 0 = 1 ∧ ∀ n, P (n + 1) = α * (P n).map φ * β' :=
    ⟨fun n => Nat.rec 1 (fun _ X => α * X.map φ * β') n, rfl, fun _ => rfl⟩
  obtain ⟨P', hP'0, hP's⟩ : ∃ P : ℕ → Matrix (Fin d) (Fin d) R,
      P 0 = 1 ∧ ∀ n, P (n + 1) = β * (P n).map φ * α' :=
    ⟨fun n => Nat.rec 1 (fun _ X => β * X.map φ * α') n, rfl, fun _ => rfl⟩
  have hΓ' : (l : R) • (β - α) = u ^ q • (-Γ) := by
    rw [smul_neg, ← hΓ, ← smul_neg, neg_sub]
  have hD := exists_matrix_seq_diff_congruence _ u φ hφL hu α β β' Γ hββ hΓ P hP0 hPs
  have hD' := exists_matrix_seq_diff_congruence _ u φ hφL hu β α α' (-Γ) hαα hΓ' P' hP'0 hP's
  obtain ⟨S, Sq, hSq, hSl, hSu⟩ :=
    exists_limit_matrix_seq_congruent _ u hc P (matrix_seq_diff_divisible_of_le _ u hq hl hdiv P hD) (exists_matrix_pow_sub_mod_u _ u hq P hP0 hD)
  obtain ⟨S', Sq', hSq', hSl', hSu'⟩ :=
    exists_limit_matrix_seq_congruent _ u hc P' (matrix_seq_diff_divisible_of_le _ u hq hl hdiv P' hD') (exists_matrix_pow_sub_mod_u _ u hq P' hP'0 hD')
  have hPP : ∀ n, P n * P' n = (l : R) ^ (4 * N * n) • 1 := by
    intro n
    induction n with
    | zero => simp [hP0, hP'0]
    | succ k ih =>
      rw [hPs, hP's]
      calc α * (P k).map φ * β' * (β * (P' k).map φ * α')
          = α * ((P k).map φ * (β' * β) * (P' k).map φ) * α' := by
            simp only [Matrix.mul_assoc]
        _ = (l : R) ^ (2 * N) • (α * (P k * P' k).map φ * α') := by
            rw [hβ'β]
            simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.map_mul,
              Matrix.mul_assoc]
        _ = (l : R) ^ (4 * N * (k + 1)) • 1 := by
            rw [ih, matrix_map_smul', map_pow, hφL, Matrix.map_one _ (map_zero φ) (map_one φ),
              Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hαα, smul_smul, smul_smul,
              ← pow_add, ← pow_add]
            congr 2
            ring
  have hSS0 : ∀ m, Sq m * Sq' m = (l : R) ^ (4 * N * n₀) • 1 := by
    intro m
    apply matrix_eq_of_smul_eq_nonzerodivisor ((l : R) ^ (4 * N * m)) (eq_zero_of_pow_mul_eq_zero_of_nonzerodivisor _ hl _)
    rw [smul_smul, ← pow_add, show 4 * N * m + 4 * N * n₀ = 4 * N * (n₀ + m) by ring, ← hPP,
      hSq, hSq', smul_mul_smul_comm, ← pow_add, show 2 * N * m + 2 * N * m = 4 * N * m by ring]
  have hSS : S * S' = (l : R) ^ (4 * N * n₀) • 1 := by
    have h0 := matrix_eq_zero_of_adic_divisible _ hc (S * S' - (l : R) ^ (4 * N * n₀) • 1) (fun m => by
      obtain ⟨Z, hZ⟩ := hSl m
      obtain ⟨Z', hZ'⟩ := hSl' m
      refine ⟨Sq m * Z' + Z * Sq' m + (l : R) ^ m • (Z * Z'), ?_⟩
      have e1 : S = Sq m + (l : R) ^ m • Z := by rw [← hZ]; abel
      have e2 : S' = Sq' m + (l : R) ^ m • Z' := by rw [← hZ']; abel
      rw [← hSS0 m, e1, e2]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul]
      abel)
    exact sub_eq_zero.mp h0
  have hstep : ∀ m, Sq (m + 1) * β = α * (Sq m).map φ := by
    intro m
    apply matrix_eq_of_smul_eq_nonzerodivisor ((l : R) ^ (2 * N * (m + 1))) (eq_zero_of_pow_mul_eq_zero_of_nonzerodivisor _ hl _)
    rw [← Matrix.smul_mul, ← hSq, show n₀ + (m + 1) = n₀ + m + 1 from rfl, hPs, Matrix.mul_assoc,
      hβ'β, Matrix.mul_smul, Matrix.mul_one, hSq, matrix_map_smul', map_pow, hφL, Matrix.mul_smul,
      smul_smul, ← pow_add]
    congr 2
    ring
  have hint : S * β = α * S.map φ := by
    have h0 := matrix_eq_zero_of_adic_divisible _ hc (S * β - α * S.map φ) (fun m => by
      obtain ⟨Z0, h0⟩ := hSl m
      obtain ⟨Z1, h1⟩ := hSl (m + 1)
      refine ⟨(l : R) • (Z1 * β) - α * Z0.map φ, ?_⟩
      have e0 : S = Sq m + (l : R) ^ m • Z0 := by rw [← h0]; abel
      have e1 : S = Sq (m + 1) + (l : R) ^ (m + 1) • Z1 := by rw [← h1]; abel
      calc S * β - α * S.map φ
          = (Sq (m + 1) + (l : R) ^ (m + 1) • Z1) * β - α * (Sq m + (l : R) ^ m • Z0).map φ := by
            rw [← e0, ← e1]
        _ = (l : R) ^ m • ((l : R) • (Z1 * β) - α * Z0.map φ) := by
            rw [Matrix.map_add _ (fun x y => map_add φ x y), matrix_map_smul', map_pow, hφL,
              Matrix.add_mul, Matrix.mul_add, hstep]
            simp only [Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_smul, ← pow_succ]
            abel)
    exact sub_eq_zero.mp h0
  refine ⟨(l : R) ^ n₀ • S, (l : R) ^ n₀ • S', ?_, ?_, ?_, ?_⟩
  · rw [smul_mul_smul_comm, hSS, smul_smul, ← pow_add, ← pow_add]
    congr 2
    ring
  · obtain ⟨Y, hY⟩ := hSu
    exact ⟨Y, by rw [← hY, smul_sub, pow_add, mul_smul]⟩
  · obtain ⟨Y, hY⟩ := hSu'
    exact ⟨Y, by rw [← hY, smul_sub, pow_add, mul_smul]⟩
  · rw [Matrix.smul_mul, hint, matrix_map_smul', map_pow, hφL, Matrix.mul_smul]

end UpperTheory.Gal.ClosedPhiFromClosedTrace
