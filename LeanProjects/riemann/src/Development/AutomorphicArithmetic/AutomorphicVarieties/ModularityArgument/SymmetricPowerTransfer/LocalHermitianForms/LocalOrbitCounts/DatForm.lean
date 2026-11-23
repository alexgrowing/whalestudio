import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DatLam

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem two_ne {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ : K} (L : IsLoc O Δ) : (2 : K) ≠ 0 := by
  have h := (L.two).map (algebraMap O K)
  rw [map_ofNat] at h
  exact h.ne_zero

theorem UpperTheory.V.Z.Sym.Loc.datForm : UpperTheory.V.Z.Sym.Loc.DatForm := by
  intro O K _ _ _ _ _ Δ τ hL c lam hn z hz m hD
  have h2 : (2 : K) ≠ 0 := two_ne hL
  have h1 := datLam K Δ τ c hD.reg hD.c_ne lam hn z hz
  have hs1 : sigL (1 : EL Δ τ) = 1 := by
    simp [sigL]
    rfl
  have hdd := h1.m_sig
  rw [hs1, one_mul] at hdd
  have hsm := hD.m_sig
  rw [mul_assoc, ← hdd, mul_one] at hsm
  have hst := hD.m_star
  rw [hsm] at hst
  have him : m.im = 0 := by
    have e := congrArg QuadraticAlgebra.im hst
    simp only [QuadraticAlgebra.im_star] at e
    have e2 : (2 : K) • m.im = 0 := by
      rw [two_smul]
      linear_combination -e
    exact (smul_eq_zero.mp e2).resolve_left h2
  have hre : m.re.im = 0 := by
    have e := congrArg (fun x : EL Δ τ => x.re.im) hsm
    simp only [sigL, QuadraticAlgebra.im_star] at e
    have e2 : (2 : K) * m.re.im = 0 := by
      linear_combination -e
    exact (mul_eq_zero.mp e2).resolve_left h2
  have ht : m.re.re ≠ 0 := by
    intro h0
    apply hD.m_unit.ne_zero
    ext <;> simp [h0, hre, him]
  refine ⟨Units.mk0 m.re.re ht, ?_⟩
  ext <;> simp [hre, him]
