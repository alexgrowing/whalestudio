import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.HermBvecFvec

open Matrix

noncomputable section

namespace PI.StabPairs.Conv

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 PI.StabPairsW

theorem one_mem_UW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : (1 : B.Mat k r) ∈ UWset k r z := by
  refine ⟨?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · show (1 : B.Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
    simp
  all_goals simp

theorem converseStep_of (hG : GramInv) : ConverseStep := by
  intro k r z z' γ hS hP p hp
  obtain ⟨u, u'⟩ := p
  obtain ⟨hu, hu', hZp⟩ := hp
  simp only at hu hu' hZp
  have hGi := hG k r z z' γ hS hP
  have hγ : γ ∈ B.GV k r := hP.1
  have hγu : IsUnit γ.det := isUnit_det_of_mem_GV hγ
  have hZ : IsUnit (Zhat k r z z' γ).det := isUnit_iff_ne_zero.mpr (det_Zhat_ne z z' hS γ hP)
  have hZh : IsUnit (Zhat k r z z' γ)ᴴ.det := by
    rw [Matrix.det_conjTranspose]; exact hZ.star
  have hZp' : u'ᴴ * (Zhat k r z z' γ)ᴴ * u = (Zhat k r z z' γ)ᴴ := by
    have := congrArg Matrix.conjTranspose hZp
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using this
  have hGi' : IsUnit ((Fm k r z z' γ)ᴴ * Hpk k r * Fm k r z z' γ).det := by rwa [← gramM_eq]
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = PI.StabPairsW.rhoOf k r z z' γ u u' := ⟨_, rfl⟩
  rw [← hρ]

  have hρF : ρ * Fm k r z z' γ = Fm k r z z' γ * Wm u u' := by
    rw [hρ, rho_eq]; exact PI.StabPairs.ConvAlg.rhoOf_mul _ _ _ hGi'
  have hcols := hρF
  rw [Fm_eq, Matrix.mul_fromCols, Wm, Matrix.fromCols_mul_fromBlocks] at hcols
  simp only [Matrix.mul_zero, add_zero, zero_add] at hcols
  obtain ⟨hA, hB⟩ := (Matrix.fromCols_ext_iff _ _ _ _).mp hcols
  have hs' : γ⁻¹ * ρ * γ * Ff k r z' = Ff k r z' * u' := by
    calc γ⁻¹ * ρ * γ * Ff k r z' = γ⁻¹ * (ρ * (γ * Ff k r z')) := by simp only [Matrix.mul_assoc]
      _ = γ⁻¹ * (γ * Ff k r z' * u') := by rw [hB]
      _ = Ff k r z' * u' := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hγu, Matrix.one_mul]

  have hWG : (Wm u u')ᴴ * ((Fm k r z z' γ)ᴴ * Hpk k r * Fm k r z z' γ) * Wm u u' =
      (Fm k r z z' γ)ᴴ * Hpk k r * Fm k r z z' γ := by
    rw [← gramM_eq, gramM_blocks z z' hS.2.1.1 hS.2.2.1 γ hγ, Wm, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
    rw [ut_adiag k r z hu, ut_adiag k r z' hu', hZp, hZp']
  have hUH : ρ ∈ B.GV k r := by
    rw [mem_GV_iff, hρ, rho_eq]
    exact PI.StabPairs.ConvAlg.rhoOf_unitary _ _ _ hpk_conjTranspose hGi' hWG
  have hexp : ∀ v, ρ *ᵥ v = v + Ff k r z *ᵥ ((u - 1) *ᵥ ((Km k r z z' γ *ᵥ v) ∘ Sum.inl)) +
      (γ * Ff k r z') *ᵥ ((u' - 1) *ᵥ ((Km k r z z' γ *ᵥ v) ∘ Sum.inr)) := by
    intro v; rw [hρ]; exact rho_mulVec k r z z' γ u u' v

  have hN : ρ ∈ Nset k r := by
    refine ⟨hUH, fun a i hi => N2gen k r z ρ hu hA a i hi, fun i j hj1 hj2 hi => ?_⟩
    refine N3gen k r z ρ i j hi ((u - 1) *ᵥ ((Km k r z z' γ *ᵥ bvec j) ∘ Sum.inl)) (ut_sub_one_last hu _) ?_
    have hc := cancel_of_pair hu hZ hZp _
      (Z_cR k r z z' γ hS hP hGi (bvec j) (fun a ha => herm_bvec_fvec k r z j hj1 hj2 a ha))
    rw [hexp, hc, Matrix.mulVec_zero, add_zero]

  have hN' : γ⁻¹ * ρ * γ ∈ Nset k r := by
    refine ⟨mul_mem_GV (mul_mem_GV (inv_mem_GV hγ) hUH) hγ, fun a i hi => N2gen k r z' _ hu' hs' a i hi,
      fun i j hj1 hj2 hi => ?_⟩
    refine N3gen k r z' _ i j hi ((u' - 1) *ᵥ ((Km k r z z' γ *ᵥ (γ *ᵥ bvec j)) ∘ Sum.inr))
      (ut_sub_one_last hu' _) ?_
    have hc := cancel_of_pair hu' hZh hZp' _
      (Z_cL k r z z' γ hS hP hGi (γ *ᵥ bvec j) (fun b hb => by
        rw [herm_GV hγ]; exact herm_bvec_fvec k r z' j hj1 hj2 b hb))
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hexp, hc, Matrix.mulVec_zero, add_zero,
      Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hγu, Matrix.one_mulVec, Matrix.one_mul]
  refine ⟨⟨⟨⟨1, one_mem_UW k r z, ρ, hN, (Matrix.one_mul ρ).symm⟩,
    γ⁻¹ * ρ * γ, ⟨1, one_mem_UW k r z', _, hN', (Matrix.one_mul _).symm⟩, ?_⟩, ?_⟩, ?_⟩
  · calc ρ = (γ * γ⁻¹) * ρ * (γ * γ⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hγu, Matrix.one_mul, Matrix.mul_one]
      _ = γ * (γ⁻¹ * ρ * γ) * γ⁻¹ := by simp only [Matrix.mul_assoc]
  · intro v hv
    rw [mem_Uperp_iff] at hv
    rw [hρ, rho_eq]
    exact PI.StabPairs.ConvAlg.rhoOf_mulVec_of_ker _ _ _ v hv
  · show (uMap k r z ρ, uMap k r z' (γ⁻¹ * ρ * γ)) = (u, u')
    rw [uMap_eq z hS.2.1 ρ u hA, uMap_eq z' hS.2.2 _ u' hs']

end PI.StabPairs.Conv
