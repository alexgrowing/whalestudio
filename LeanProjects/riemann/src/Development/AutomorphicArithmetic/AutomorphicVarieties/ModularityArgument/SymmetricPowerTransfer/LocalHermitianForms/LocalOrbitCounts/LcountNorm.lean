import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DatIso

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem ofE_mul_local_orbit_counts {K : Type} [Field K] (Δ τ : K) (z w : Etau K τ) :
    ofE Δ (z * w) = ofE Δ z * ofE Δ w := by
  ext <;> simp [ofE.eq_1] <;> ring

private theorem ofE_one' {K : Type} [Field K] (Δ τ : K) : ofE Δ (1 : Etau K τ) = 1 := by
  ext <;> simp [ofE.eq_1]

private theorem sigL_ofE_local_orbit_counts {K : Type} [Field K] (Δ τ : K) (z : Etau K τ) : sigL (ofE Δ z) = ofE Δ z := by
  ext <;> simp [ofE.eq_1, sigL.eq_1]

private theorem mul_ofE_mul_star_sigL_eq_norm_smul {K : Type} [Field K] (Δ τ : K) (m : EL Δ τ) (z : Etau K τ) :
    m * ofE Δ z * star (sigL (ofE Δ z)) = (QuadraticAlgebra.norm z : K) • m := by
  ext <;> simp [ofE.eq_1, sigL.eq_1, QuadraticAlgebra.norm_def] <;> ring

theorem UpperTheory.V.Z.Sym.Loc.lcountNorm : UpperTheory.V.Z.Sym.Loc.LcountNorm := by
  unfold LcountNorm
  intro O K _ _ _ _ _ Δ τ _ c d m _ t ht
  rw [NE.eq_1] at ht
  obtain ⟨u, rfl⟩ := ht
  let y : (EL Δ τ)ˣ :=
    ⟨ofE Δ (u : Etau K τ), ofE Δ (↑u⁻¹ : Etau K τ),
      by rw [← ofE_mul_local_orbit_counts, u.mul_inv, ofE_one'],
      by rw [← ofE_mul_local_orbit_counts, u.inv_mul, ofE_one']⟩
  have hI : DatIso := datIso
  unfold DatIso at hI
  have h := (hI O K Δ τ c d m y).1
  have hy : (y : EL Δ τ) = ofE Δ (u : Etau K τ) := rfl
  have e1 : d * sigL (y : EL Δ τ) * ↑y⁻¹ = d := by
    rw [show sigL (y : EL Δ τ) = (y : EL Δ τ) by rw [hy, sigL_ofE_local_orbit_counts]]
    exact Units.mul_inv_cancel_right d y
  have e2 : m * ↑y * star (sigL (y : EL Δ τ)) = ((Units.map QuadraticAlgebra.norm u : Kˣ) : K) • m := by
    rw [hy, Units.coe_map, mul_ofE_mul_star_sigL_eq_norm_smul]
  rw [e1, e2] at h
  exact h.symm
