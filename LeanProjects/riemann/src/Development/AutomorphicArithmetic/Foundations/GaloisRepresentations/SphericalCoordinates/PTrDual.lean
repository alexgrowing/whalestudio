import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFrameEx

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem exists_inverse_different (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] :
    ∃ d : K, d ≠ 0 ∧ ∀ a : K,
      (∀ z : K, ‖(z : PadicAlgCl p)‖ ≤ 1 → ‖Algebra.trace ℚ_[p] K (a * z)‖ ≤ 1) ↔
        ‖((a * d : K) : PadicAlgCl p)‖ ≤ 1 := by
  classical
  have hpos : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hmin : ∀ z : K, minpoly ℚ_[p] (z : PadicAlgCl p) = minpoly ℚ_[p] z := fun z =>
    minpoly.algebraMap_eq (algebraMap K (PadicAlgCl p)).injective z
  have hsv : ∀ z : K, ‖(z : PadicAlgCl p)‖ = spectralValue (minpoly ℚ_[p] z) := by
    intro z
    rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, hmin]
  have hnat : ∀ m : ℕ, ‖(m : ℚ_[p])‖ ≤ 1 := fun m => by
    simpa using Padic.norm_int_le_one (p := p) (m : ℤ)
  have hTr : ∀ z : K, ‖(z : PadicAlgCl p)‖ ≤ 1 → ‖Algebra.trace ℚ_[p] K z‖ ≤ 1 := by
    intro z hz
    rw [hsv, spectralValue_le_one_iff (minpoly.monic (Algebra.IsIntegral.isIntegral z))] at hz
    rw [trace_eq_finrank_mul_minpoly_nextCoeff, norm_mul, norm_neg]
    have h2 : ‖(minpoly ℚ_[p] z).nextCoeff‖ ≤ 1 := by
      unfold Polynomial.nextCoeff
      split_ifs
      · simp
      · exact hz _
    calc _ ≤ 1 * 1 := mul_le_mul (hnat _) h2 (norm_nonneg _) zero_le_one
      _ = 1 := _root_.one_mul 1
  have hdisc : ∀ x : K, x ≠ 0 → ∃ j : ℤ,
      ‖(x : PadicAlgCl p)‖ ^ (Module.finrank ℚ_[p] K).factorial = (p : ℝ) ^ j := by
    intro x hx
    have hint : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
    have hdpos : 0 < (minpoly ℚ_[p] x).natDegree := minpoly.natDegree_pos hint
    have hdle : (minpoly ℚ_[p] x).natDegree ≤ Module.finrank ℚ_[p] K := minpoly.natDegree_le x
    obtain ⟨c, hc⟩ := Nat.dvd_factorial hdpos hdle
    have hc0 : (minpoly ℚ_[p] x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hx
    have hx1 : ‖(x : PadicAlgCl p)‖ =
        ‖(minpoly ℚ_[p] x).coeff 0‖ ^ (1 / ((minpoly ℚ_[p] x).natDegree : ℝ)) := by
      rw [← PadicAlgCl.spectralNorm_eq,
        spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow ℚ_[p] (PadicAlgCl p) (x : PadicAlgCl p),
        hmin]
    have hx2 : ‖(x : PadicAlgCl p)‖ ^ (minpoly ℚ_[p] x).natDegree = ‖(minpoly ℚ_[p] x).coeff 0‖ := by
      rw [hx1, one_div, Real.rpow_inv_natCast_pow (norm_nonneg _) hdpos.ne']
    refine ⟨-((minpoly ℚ_[p] x).coeff 0).valuation * c, ?_⟩
    rw [hc, pow_mul, hx2, Padic.norm_eq_zpow_neg_valuation hc0, ← zpow_natCast, ← zpow_mul]
  have hn0 : ((Module.finrank ℚ_[p] K : ℕ) : ℚ_[p]) ≠ 0 :=
    Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  set c : ℚ_[p] := ((p : ℚ_[p]) * (Module.finrank ℚ_[p] K : ℕ))⁻¹ with hcdef
  have hbd : ∀ a : K,
      (∀ z : K, ‖(z : PadicAlgCl p)‖ ≤ 1 → ‖Algebra.trace ℚ_[p] K (a * z)‖ ≤ 1) →
        ‖(a : PadicAlgCl p)‖ < ‖c‖ := by
    intro a ha
    by_contra hlt
    push_neg at hlt
    have ha0 : (a : PadicAlgCl p) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hlt
      exact absurd hlt (not_le.2 (norm_pos_iff.2 (inv_ne_zero (mul_ne_zero hp0 hn0))))
    have ha0' : a ≠ 0 := fun h => ha0 (by simp [h])
    have hz := ha (algebraMap ℚ_[p] K c * a⁻¹) (by
      rw [IntermediateField.coe_mul, IntermediateField.coe_inv, norm_mul, norm_inv]
      have hcn : ‖((algebraMap ℚ_[p] K c : K) : PadicAlgCl p)‖ = ‖c‖ :=
        PadicAlgCl.norm_extends p c
      rw [hcn, ← div_eq_mul_inv, div_le_one (norm_pos_iff.2 ha0)]
      exact hlt)
    have e2 : a * (algebraMap ℚ_[p] K c * a⁻¹) = algebraMap ℚ_[p] K c := by
      rw [_root_.mul_comm, _root_.mul_assoc, inv_mul_cancel₀ ha0', _root_.mul_one]
    rw [e2, Algebra.trace_algebraMap, nsmul_eq_mul] at hz
    have e3 : ((Module.finrank ℚ_[p] K : ℕ) : ℚ_[p]) * c = (p : ℚ_[p])⁻¹ := by
      rw [hcdef]
      field_simp
    rw [e3, norm_inv, Padic.norm_p, inv_inv] at hz
    linarith
  obtain ⟨B, hB⟩ := pow_unbounded_of_one_lt (‖c‖ ^ (Module.finrank ℚ_[p] K).factorial) hpos
  have hex := Int.exists_greatest_of_bdd (P := fun j : ℤ => ∃ a : K,
      (∀ z : K, ‖(z : PadicAlgCl p)‖ ≤ 1 → ‖Algebra.trace ℚ_[p] K (a * z)‖ ≤ 1) ∧ a ≠ 0 ∧
        ‖(a : PadicAlgCl p)‖ ^ (Module.finrank ℚ_[p] K).factorial = (p : ℝ) ^ j)
    ⟨B, fun j ⟨a, ha, _, hj⟩ => by
      have h1 : ‖(a : PadicAlgCl p)‖ ^ (Module.finrank ℚ_[p] K).factorial <
          ‖c‖ ^ (Module.finrank ℚ_[p] K).factorial :=
        pow_lt_pow_left₀ (hbd a ha) (norm_nonneg _) (Nat.factorial_ne_zero _)
      rw [hj] at h1
      have h2 : (p : ℝ) ^ j < (p : ℝ) ^ (B : ℤ) := by
        rw [zpow_natCast]
        exact h1.trans hB
      exact ((zpow_lt_zpow_iff_right₀ hpos).1 h2).le⟩
    ⟨0, 1, fun z hz => by rw [_root_.one_mul]; exact hTr z hz, one_ne_zero, by simp⟩
  obtain ⟨jm, ⟨am, hamD, ham0, hamj⟩, hmax⟩ := hex
  have hamn : (am : PadicAlgCl p) ≠ 0 := fun h => ham0 (by exact_mod_cast h)
  refine ⟨am⁻¹, inv_ne_zero ham0, fun a => ?_⟩
  have key : ‖((a * am⁻¹ : K) : PadicAlgCl p)‖ ≤ 1 ↔
      ‖(a : PadicAlgCl p)‖ ≤ ‖(am : PadicAlgCl p)‖ := by
    rw [IntermediateField.coe_mul, IntermediateField.coe_inv, norm_mul, norm_inv,
      ← div_eq_mul_inv, div_le_one (norm_pos_iff.2 hamn)]
  rw [key]
  constructor
  · intro ha
    by_cases ha0 : a = 0
    · simp [ha0]
    obtain ⟨j, hj⟩ := hdisc a ha0
    have hjle := hmax j ⟨a, ha, ha0, hj⟩
    have hle : ‖(a : PadicAlgCl p)‖ ^ (Module.finrank ℚ_[p] K).factorial ≤
        ‖(am : PadicAlgCl p)‖ ^ (Module.finrank ℚ_[p] K).factorial := by
      rw [hj, hamj]
      exact zpow_le_zpow_right₀ hpos.le hjle
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (Nat.factorial_ne_zero _)).1 hle
  · intro ha z hz
    have e : a * z = am * (am⁻¹ * a * z) := by
      rw [← _root_.mul_assoc, ← _root_.mul_assoc, mul_inv_cancel₀ ham0, _root_.one_mul]
    rw [e]
    apply hamD
    rw [IntermediateField.coe_mul, IntermediateField.coe_mul, IntermediateField.coe_inv,
      norm_mul, norm_mul, norm_inv]
    have h1 : ‖(am : PadicAlgCl p)‖⁻¹ * ‖(a : PadicAlgCl p)‖ ≤ 1 := by
      rw [inv_mul_le_iff₀ (norm_pos_iff.2 hamn), _root_.mul_one]
      exact ha
    exact mul_le_one₀ h1 (norm_nonneg _) hz

theorem UpperTheory.Gal.W2.trDual_of :
    UpperTheory.Gal.W2.TrDual := by
  intro p _ G w
  exact exists_inverse_different p (G.Fw w)
