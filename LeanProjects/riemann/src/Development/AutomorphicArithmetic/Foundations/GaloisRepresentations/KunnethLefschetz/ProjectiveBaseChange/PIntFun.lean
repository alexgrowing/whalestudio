import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.AdicTopOf
import Development.EtaleCohomology.EtaleTrace.H0LimitCoherence
import Development.EtaleCohomology.EtaleTrace.LRingPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison ReciprocityTheory.ChartRestriction.G.Geo.Tor UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

theorem UpperTheory.Gal.KunnethLefschetz.intFun_holds :
    UpperTheory.Gal.KunnethLefschetz.IntFun := by
  intro hB l _ K M hR i j r g h hspan
  refine eq_top_iff.mpr (le_trans (le_of_eq hspan.symm) ?_)
  apply Submodule.span_le.mpr
  rintro f ⟨s, y, hy⟩
  obtain ⟨b, y0, hb, rfl⟩ := LateralTheory.EtaleTrace.H0LimitCoherence.tensor_form l y
  have hb' : ((b : ℚ_[l])) ≠ 0 := fun e => hb (PadicInt.coe_eq_zero.mp e)
  have hone : (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y0 = (b : ℚ_[l]) • (((b : ℚ_[l]))⁻¹ ⊗ₜ[ℤ_[l]] y0) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_inv_cancel₀ hb']
  have hmem : ((b : ℚ_[l]) • f) ∈
      {f | ∃ s y, ∀ (x : M.T i), ∃ z, M.CupT x y z ∧ M.toV (i + j) z = f (M.toV i x) • g s} := by
    refine ⟨s, y0, fun x => ⟨LateralTheory.EtaleTrace.LRingPf.cupL l M.spc h hB x y0, ?_, ?_⟩⟩
    · intro k
      exact LateralTheory.EtaleTrace.LRingPf.cupL_apply l M.spc h hB x y0 k
    · have hc := hR.isCup (GlobalTheory.Et.geom (PadicAlgCl l) M.q) (i : ℤ) (j : ℤ) ((i + j : ℕ) : ℤ) h x y0
        (LateralTheory.EtaleTrace.LRingPf.cupL l M.spc h hB x y0)
        (fun k => LateralTheory.EtaleTrace.LRingPf.cupL_apply l M.spc h hB x y0 k)
      have hx := hy (1 ⊗ₜ[ℤ_[l]] x)
      change (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] (LateralTheory.EtaleTrace.LRingPf.cupL l M.spc h hB x y0) = _
      rw [← hc, hone, LinearMap.map_smul, hx, smul_smul]
      rfl
  have hsub := Submodule.subset_span (R := ℚ_[l]) hmem
  have hsm := Submodule.smul_mem _ ((b : ℚ_[l]))⁻¹ hsub
  rw [smul_smul, inv_mul_cancel₀ hb', one_smul] at hsm
  exact hsm
