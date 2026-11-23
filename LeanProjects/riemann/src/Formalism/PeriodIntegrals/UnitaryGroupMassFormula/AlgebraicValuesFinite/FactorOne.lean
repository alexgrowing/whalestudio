import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.ClassSame

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1

namespace PI.AlgValsFin.W

variable {L : Type} [Field L] [NumberField L]

theorem absNorm_pos (v : HeightOneSpectrum (𝓞 L)) : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have h : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  exact_mod_cast Nat.pos_of_ne_zero h

theorem factor_one (N : ℝ) (hN : 0 < N) (o : ℤ) (s : ℝ) : (N ^ o) ^ s * (N ^ (-s)) ^ o = 1 := by
  have h1 : (N ^ o) ^ s = N ^ ((o : ℝ) * s) := by
    rw [← Real.rpow_intCast, ← Real.rpow_mul hN.le]
  have h2 : (N ^ (-s)) ^ o = N ^ (-s * (o : ℝ)) := by
    rw [← Real.rpow_intCast, ← Real.rpow_mul hN.le]
  have h3 : (o : ℝ) * s + -s * (o : ℝ) = 0 := by ring
  rw [h1, h2, ← Real.rpow_add hN, h3, Real.rpow_zero]

theorem keyIdOf : KeyIdOf L := by
  intro hD hL hP χ s m hχ k T hT hU
  obtain ⟨r, hr, hk⟩ := hD k T hT
  refine ⟨r, hr, ?_⟩

  have e : χ.1 (diagUnits L k) = 1 := χ.2.2 k
  rw [hk, map_mul, map_mul, map_prod] at e
  have eloc : ∀ v ∈ T, χ.1 (localIdele L v (atFin v k)) = χ.val v ^ ordF v k := by
    intro v hv
    exact hL χ v k (hU v hv)
  rw [Finset.prod_congr rfl eloc] at e
  have einf : χ.1 (infDiag k) = χ.inf k := rfl
  rw [einf] at e
  have e' := congrArg (fun u : ℂˣ => (u : ℂ)) e
  simp only [Units.val_mul, Units.coe_prod, Units.val_zpow_eq_zpow_val, Units.val_one] at e'

  have hreal : (∏ φ : L →+* ℂ, ‖φ (k : L)‖ ^ s) *
      ∏ v ∈ T, (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s)) ^ ordF v k = 1 := by
    rw [Real.finset_prod_rpow Finset.univ (fun φ : L →+* ℂ => ‖φ (k : L)‖) (fun φ _ => norm_nonneg _) s,
      hP k T hT,
      ← Real.finset_prod_rpow T _ (fun v _ => zpow_nonneg (absNorm_pos v).le _) s,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one (fun v _ => factor_one _ (absNorm_pos v) _ s)
  have hc1 : ∏ φ : L →+* ℂ, ((‖φ (k : L)‖ : ℝ) : ℂ) ^ (s : ℂ)
      = ((∏ φ : L →+* ℂ, ‖φ (k : L)‖ ^ s : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl (fun φ _ => ?_)
    rw [Complex.ofReal_cpow (norm_nonneg _)]
  have hc2 : ∏ v ∈ T, (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s : ℂ))) ^ ordF v k
      = ((∏ v ∈ T, (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s)) ^ ordF v k : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    rw [Complex.ofReal_zpow, Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_neg,
      Complex.ofReal_natCast]
  rw [← hχ k]
  simp only [Formalism.L2.Host.HChar.valTw, mul_zpow, Finset.prod_mul_distrib]
  rw [hc1, hc2]
  set A : ℝ := ∏ φ : L →+* ℂ, ‖φ (k : L)‖ ^ s with hA
  set B : ℝ := ∏ v ∈ T, (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s)) ^ ordF v k with hB
  have hAB : (A : ℂ) * (B : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, hreal, Complex.ofReal_one]
  linear_combination ((A : ℂ) * (B : ℂ)) * e' + hAB

end PI.AlgValsFin.W
