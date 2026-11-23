import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.RepNewformOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RepEig
import Mathlib.NumberTheory.ModularForms.NormTrace

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf UpperTheory.V.Sd
  UpperTheory.V.Br CongruenceSubgroup

private theorem cusp_zero (N : ℕ) [NeZero N] (f : CuspForm (Gamma1 N) ((0 : ℕ) : ℤ)) : f = 0 := by
  obtain ⟨c, hc⟩ := ModularForm.eq_const_of_weight_zero (𝒢 := (Gamma1 N : Subgroup (GL (Fin 2) ℝ)))
    { toFun := f, holo' := f.holo', slash_action_eq' := f.slash_action_eq',
      bdd_at_cusps' := fun hc g hg => (f.zero_at_cusps' hc g hg).isBoundedAtImInfty }
  have hc' : (f : UpperHalfPlane → ℂ) = Function.const UpperHalfPlane c := hc
  have hz : UpperHalfPlane.IsZeroAtImInfty (f : UpperHalfPlane → ℂ) := CuspFormClass.zero_at_infty f
  rw [hc'] at hz
  have h0 : c = 0 := tendsto_nhds_unique tendsto_const_nhds hz
  ext z
  rw [hc', h0]
  rfl

theorem UpperTheory.V.Af.Rn.noLow :
    UpperTheory.V.Sd.Wc.CentChar → UpperTheory.V.Af.Rn.NoLow := by
  intro hC π hπ
  obtain ⟨N, ψ, ν, hN, hν, φ, hφ, h0, hlow, hfix⟩ := levelVec 0 π hπ
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨ω, hω, -⟩ := hC ℚ (π.twist ν)
  have hc := fun z g => hω z φ hφ g
  obtain ⟨χ, hχ⟩ := charOf N hN ω φ h0 hlow.one hfix hc
  have hcusp := (π.twist ν).cusp φ hφ
  obtain ⟨f, -, hL⟩ := deadel 0 N hN χ ω hχ φ hcusp hlow hfix hc
  obtain rfl := cusp_zero N f
  refine h0 (Subtype.ext (funext fun g => ?_))
  obtain ⟨γ, h, u, hu, rfl⟩ := decomp N hN g
  rw [hL γ h u hu]
  simp [nsl]
