import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem bdX_mul_le (M a k T : ℕ) (hT : 2 ≤ T) (hM : M ≤ T) (ha : a ≤ T ^ 3) (hk : k ≤ T) (hk2 : 2 ≤ k) :
    bdX M a k * M ≤ T ^ (10 * k) := by
  have hk1 : k + 1 ≤ T ^ 2 := by nlinarith
  have f1 : (k + 1).factorial ≤ (T ^ 2) ^ (k + 1) :=
    (Nat.factorial_le_pow _).trans (Nat.pow_le_pow_left hk1 _)
  have f2 : k.factorial ≤ T ^ k := (Nat.factorial_le_pow _).trans (Nat.pow_le_pow_left hk _)
  calc bdX M a k * M = M * k * (k + 1).factorial * (2 * a ^ k * M ^ k * k.factorial) * M := rfl
    _ ≤ T * T * (T ^ 2) ^ (k + 1) * (T * (T ^ 3) ^ k * T ^ k * T ^ k) * T := by gcongr
    _ = T ^ (7 * k + 6) := by ring
    _ ≤ T ^ (10 * k) := Nat.pow_le_pow_right (by omega) (by omega)

theorem UpperTheory.V.Odd.bdxLog :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N l e : ℕ, 1 ≤ N → 2 ≤ l → 1 ≤ e → Real.log (bdX (N * l) (2 * (N * l) + 1) (e + 1)) + Real.log ((N : ℝ) * l) ≤ C * (e + 1) * Real.log ((e : ℝ) * l * N) := by
  refine ⟨30, by norm_num, ?_⟩
  intro N l e hN hl he
  have h2 : e * 2 ≤ e * l := Nat.mul_le_mul_left e hl
  have h3 : e * l ≤ e * l * N := Nat.le_mul_of_pos_right _ hN
  have h4 : 1 * l * N ≤ e * l * N := by gcongr
  have h5 : N * l ≤ e * l * N := by nlinarith
  have hX2 : 2 ≤ e * l * N := by nlinarith
  have hT : 2 ≤ 3 * (e * l * N) := by omega
  have hM : N * l ≤ 3 * (e * l * N) := by omega
  have ha : 2 * (N * l) + 1 ≤ (3 * (e * l * N)) ^ 3 :=
    le_trans (by omega) (Nat.le_self_pow (by norm_num) _)
  have hk : e + 1 ≤ 3 * (e * l * N) := by nlinarith
  have key := bdX_mul_le (N * l) (2 * (N * l) + 1) (e + 1) (3 * (e * l * N)) hT hM ha hk (by omega)
  have hNl : 0 < N * l := by positivity
  have hb : 0 < bdX (N * l) (2 * (N * l) + 1) (e + 1) := by
    unfold bdX denY sizeY
    positivity
  have hbpos : (0 : ℝ) < (bdX (N * l) (2 * (N * l) + 1) (e + 1) : ℝ) := by exact_mod_cast hb
  have hMpos : (0 : ℝ) < (N : ℝ) * l := by exact_mod_cast hNl
  rw [← Real.log_mul hbpos.ne' hMpos.ne']
  have hcast : (bdX (N * l) (2 * (N * l) + 1) (e + 1) : ℝ) * ((N : ℝ) * l)
      = ((bdX (N * l) (2 * (N * l) + 1) (e + 1) * (N * l) : ℕ) : ℝ) := by
    push_cast; ring
  rw [hcast]
  have hXr : (2 : ℝ) ≤ (e : ℝ) * l * N := by exact_mod_cast hX2
  have hlog2 : Real.log 2 ≤ Real.log ((e : ℝ) * l * N) := Real.log_le_log (by norm_num) hXr
  have hlog3 : Real.log 3 ≤ 2 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogT : Real.log (((3 * (e * l * N) : ℕ) : ℝ)) ≤ 3 * Real.log ((e : ℝ) * l * N) := by
    push_cast
    rw [Real.log_mul (by norm_num) (by positivity)]
    linarith
  have hpos : (0 : ℝ) < ((bdX (N * l) (2 * (N * l) + 1) (e + 1) * (N * l) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hb hNl
  calc Real.log ((bdX (N * l) (2 * (N * l) + 1) (e + 1) * (N * l) : ℕ) : ℝ)
      ≤ Real.log (((3 * (e * l * N)) ^ (10 * (e + 1)) : ℕ) : ℝ) :=
        Real.log_le_log hpos (by exact_mod_cast key)
    _ = (10 * (e + 1) : ℕ) * Real.log (((3 * (e * l * N) : ℕ) : ℝ)) := by
        rw [Nat.cast_pow, Real.log_pow]
    _ ≤ (10 * (e + 1) : ℕ) * (3 * Real.log ((e : ℝ) * l * N)) :=
        mul_le_mul_of_nonneg_left hlogT (by positivity)
    _ = 30 * ((e : ℝ) + 1) * Real.log ((e : ℝ) * l * N) := by push_cast; ring
